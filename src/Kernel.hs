{-# LANGUAGE FlexibleContexts #-}

{-|
Module      : Kernel
Description : Trusted core of the equational reasoning checker
License     : MIT

Everything in this module is part of the trusted computing base. It provides:

* proof contexts ('Ctx'), one-step proofs ('Pf') and checked theorems
  ('Thm'); 'kernelCheck' is the only way to obtain a 'Thm'
* trusted rule services built on GHC's own rewriting machinery:
  definitional unfolding via @substExpr@, postulate rules via
  @lookupRule@, normalization via @simpleOptExpr@
* the postulate registry: every successfully proved declaration
  becomes a rewrite rule for later @Prop@ steps

Site selection (where to rewrite) lives in "CheckProofs" and is
untrusted: a bug there can only make a proof fail, never prove a
false equation.
-}
module Kernel where

import GHC.Core
import GHC.Core.Map.Type (DeBruijn(..), deBruijnize, extendCMEs)
import GHC.Plugins hiding (getModule)

import System.FilePath ((</>))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State.Lazy ( gets, modify )
import Control.Monad.Except ( MonadError(..) )
import Data.Generics.Uniplate.Data (universe)
import Data.List (find)

-- Simplifier
import GHC.Unit.External (initExternalUnitCache, eucEPS, ExternalPackageState(..))
import GHC.Driver.Config.Core.Opt.Simplify (initSimplifyExprOpts)
import GHC.Core.FamInstEnv (extendFamInstEnvList, emptyFamInstEnv)
import GHC.Core.Opt.Simplify (SimplifyExprOpts(..))
import GHC.Core.Opt.Simplify.Env ( getInScope, mkSimplEnv, setInScopeSet, seRuleOpts, SimplEnv (seMode) )
import GHC.Core.Opt.Simplify.Utils ( getUnfoldingInRuleMatch, activeRule )
import GHC.Core.SimpleOpt ( defaultSimpleOpts, simpleOptExpr )

import AstInfo
import PrettyString


---- LOGGING
logPath :: FilePath
logPath = "logs" </> "app.txt"

logMsg :: (MonadIO m) => String -> m ()
logMsg log_msg = liftIO $ appendFile logPath (log_msg ++ "\n")


---- EXPRESSION EQUALITY (trusted)
{-|
-- assume that any variable in convertion is OR
* in (\x ->) this convertion
* global func
* parametr for this function

-- alphaEq called for whole expr works correctly
-- for subexpr need to remember Lam-binds (\x ->)
-}
alphaEq :: (Eq (DeBruijn a)) => a -> a -> Bool
alphaEq lhv rhv = deBruijnize lhv == deBruijnize rhv

-- Called in getFirstDiff
alphaEqWithEnv :: (Eq (DeBruijn a)) => ([Id], [Id]) -> a -> a -> Bool
alphaEqWithEnv (l_vars, r_vars) lhv rhv =
    deBrujinWithEnv lhv l_vars == deBrujinWithEnv rhv r_vars
  where
    deBrujinWithEnv e vars =
      case deBruijnize e of (D cm_env a) -> D (extendCMEs cm_env vars) a


---- PROOF CONTEXTS
-- | An expression with a hole: where a rewrite applies.
-- @plugCtx ctx diff@ rebuilds the original expression.
data Ctx = Hole | CAppF Ctx CoreExpr | CAppA CoreExpr Ctx | CLam Id Ctx

-- | Fill the hole of a context.
plugCtx :: Ctx -> CoreExpr -> CoreExpr
plugCtx Hole            e = e
plugCtx (CAppF ctx arg) e = App (plugCtx ctx e) arg
plugCtx (CAppA f ctx)   e = App f (plugCtx ctx e)
plugCtx (CLam b ctx)    e = Lam b (plugCtx ctx e)


---- PROOFS AND THEOREMS
-- | Justification for one equational step, proposed by a tactic
-- ("CheckProofs") and validated by 'kernelCheck'. Each constructor
-- proves an equation between full expressions: the context applied to
-- both sides of the local rewrite.
data Pf
  = DefAt Ctx Id [CoreExpr]
    -- ^ @plugCtx ctx (f args)@ equals the unfolding of @f@ at @args@
  | RuleAt Ctx CoreExpr PostlDef
    -- ^ @plugCtx ctx site@ equals the registered rule fired at @site@
  | InstAt Ctx CoreExpr
    -- ^ @plugCtx ctx site@ equals the class-method resolution at @site@
  | EtaAt Ctx CoreExpr
    -- ^ @plugCtx ctx site@ equals the eta-contraction of @site@

-- | An equation checked by the kernel. Constructible only via
-- 'kernelCheck'.
data Thm = Thm
  { thmLhs :: CoreExpr
  , thmRhs :: CoreExpr
  }

-- | Check a proposed step with the trusted rule services.
kernelCheck :: Pf -> CheckerM Thm
kernelCheck pf = case pf of
  DefAt ctx f_id args ->
    do
      (fl_id, func_body) <- getBodyByFuncId f_id
      logMsg $ "Substitute def for function: " ++ prettyString fl_id ++ "\n"
      let subst_func = easySubstFunc (Var fl_id) fl_id func_body
      simpl_expr <- simplifyOptFunc (plugCtx ctx (mkCoreApps subst_func args))
      return $ Thm (plugCtx ctx (mkCoreApps (Var f_id) args)) simpl_expr

  RuleAt ctx site pstl ->
    do
      checkRegistered pstl
      lookup_expr <- substRule [pstl] site
      simpl_expr <- simplifyOptFunc (plugCtx ctx lookup_expr)
      return $ Thm (plugCtx ctx site) simpl_expr

  InstAt ctx site ->
    do
      subst_inst <- substituteInst site
      subst_simp <- simplifyOptFunc subst_inst
      subst_expr <- ordinar_subst subst_simp
      simpl_expr <- simplifyOptFunc (plugCtx ctx subst_expr)
      return $ Thm (plugCtx ctx site) simpl_expr

  EtaAt ctx diff_expr ->
    case diff_expr of
      Lam v1 (App f (Var v2)) | v1 == v2 ->  -- TODO: check and fix
        return $ Thm (plugCtx ctx diff_expr) (plugCtx ctx f)
      _ -> throwError $ "Error in analyzeEtaConv:\n" ++ prettyString diff_expr

  where
    -- Resolution of a class-method call to the instance implementation
    substituteInst expr =
      do
        (func_id, args) <- case collectArgs expr of
          (Var f_id, as) -> return (f_id, as)
          _              -> throwError $ "Applied expression not a function call!\nGot: " ++ prettyString expr
        let func_body    = unfoldingTemplate $ idUnfolding func_id

        {- TODO check why doesn't work
          logMsg $ "SUBS_INST" ++
            "\nsubst_func:\n" ++ prettyString subst_func ++
            "\n      func:\n" ++ prettyString func ++
            "\n   func_id:\n" ++ prettyString func_id ++
            "\n func_body:\n" ++ prettyString func_body
        -}
        let subst_selector = mkCoreApps func_body (take 2 args)
        selector_simpl    <- simplifyOptFunc subst_selector
        logMsg $ "Substitute selector for instance_method: " ++ prettyString func_id ++ "\n"
        -- logMsg $ "Selector implementation\n" ++ prettyString selector_simpl ++ "\n"


        instce_id <- case collectArgs (args !! 1) of
          (Var instce_id, _) -> return instce_id
          _                  -> throwError $ "Not implemented: " ++ "instance_is not var."
        (inst_id, inst_body)  <- getBodyByFuncId instce_id
        let subst_inst         = easySubstFunc selector_simpl inst_id inst_body
        selector_inst         <- simplifyOptFunc subst_inst
        logMsg $ "Substitute instance for instance_method: " ++ prettyString instce_id ++ "\n"
        -- logMsg $ "Selector instanced\n" ++ prettyString selector_inst
        return $ mkCoreApps selector_inst (drop 2 args)

    ordinar_subst expr =
      do
        (func@(Var fn_id), args) <- case collectArgs expr of
          f@(Var _, _) -> return f
          _            -> throwError $ "Not implemented: " ++ "function not var."
        (func_id, func_body)        <- getBodyByFuncId fn_id
        let subst_func = easySubstFunc func func_id func_body
        logMsg $ "Substitute instance method for inst: " ++ prettyString func_id ++ "\n"
        return $ mkCoreApps subst_func args

-- | Guard for 'RuleAt': the fired rule must come from the registry.
checkRegistered :: PostlDef -> CheckerM ()
checkRegistered pstl = do
  postl_defs <- gets st_postldefs
  case any (\p -> pstl_id p == pstl_id pstl) postl_defs of
    True  -> return ()
    False -> throwError $
      "Internal error. Firing a rule that is not in the registry: " ++ prettyString (pstl_id pstl)


---- TRUSTED RULE SERVICES
getStrById :: Id -> String
getStrById v = occNameString (getOccName v)

getBodyByFuncId :: Id -> CheckerM (Id, CoreExpr)
getBodyByFuncId func_id =
  do
    let (fl_id, stDefs) = case nameModule_maybe (idName func_id) of
          Just modl | showSDocUnsafe (ppr modl) == "ProofBase" -> (localiseId func_id, st_base_defs)
          _                                                    -> (func_id, st_funcdefs)
    func_defs <- gets stDefs
    case lookup func_id func_defs of
      Just func_body -> return (fl_id, func_body)
      Nothing        -> throwError $ "Function definition not found for:\n" ++ prettyString func_id

-- | substExpr wrapper
easySubstFunc :: CoreExpr -> Id -> CoreExpr -> CoreExpr
easySubstFunc expr fn_id fn_body = substExpr subst expr
  where
  delFunFV = mkInScopeSet $ delVarSet (exprFreeVars expr) fn_id
  subst = extendSubst (mkEmptySubst delFunFV) fn_id fn_body

inlineLetsIgnoreCast :: CoreExpr -> CoreExpr
inlineLetsIgnoreCast expr =
  case expr of
    Let (NonRec b rhs) body ->
      inlineLetsIgnoreCast (easySubstFunc body b rhs)
    App f x ->
      App (inlineLetsIgnoreCast f) (inlineLetsIgnoreCast x)
    Lam b e ->
      Lam b (inlineLetsIgnoreCast e)
    Cast e _ -> inlineLetsIgnoreCast e
    _ -> expr

-- | run 3 times in cyrcle
--
-- * simpleOptExpr
-- * inline created @let@ expressions
-- * check if any beta-reductions
-- * if yes repeat
simplifyOptFunc :: CoreExpr -> CheckerM CoreExpr
simplifyOptFunc expr = go 0 expr
  where
    go :: Int -> CoreExpr -> CheckerM CoreExpr
    go n _ | n >= 3 = throwError $
      "Unexpected expression. Expression needs to much beta-reductions. " ++
      "Default threshold = 3. Expr:\n" ++ prettyString expr ++ "\n"
    go n e = do
      logMsg $ "Try simplifyOptFunc n=" ++ show n ++ "\n"
      let no_lets_expr = inlineLetsIgnoreCast (simpleOptExpr defaultSimpleOpts e)
      case find isBetaRedex (universe no_lets_expr) of
        Just _  -> go (n + 1) no_lets_expr
        Nothing -> return no_lets_expr

    isBetaRedex (App (Lam _ _) _) = True
    isBetaRedex _                 = False


-- | Substitute rules. lookupRule wrapper
substRule :: [PostlDef] -> CoreExpr -> CheckerM CoreExpr
substRule pstls expr =
  do
    hscEnv <- gets st_hscenv
    let opts   = initSimplifyExprOpts (hsc_dflags hscEnv) (hsc_IC hscEnv)

    euc <- liftIO initExternalUnitCache
    eps <- liftIO (eucEPS euc)

    let fam_envs =  ( eps_fam_inst_env eps
                    , extendFamInstEnvList emptyFamInstEnv $ se_fam_inst opts
                    )
        rules = map pstl_rule pstls
        simpl_env = mkSimplEnv (se_mode opts) fam_envs
        ru_rhs_fv = map ruleRhsFreeVars rules
        fv_set    = foldl unionUniqSets (exprFreeVars expr) ru_rhs_fv
        -- NOTE order is important. We want to preserve modified pstl_fid
        fv_idInfo_set = fv_set `addListToUniqSet` map pstl_fid pstls
        my_in_scope   = getInScope simpl_env `extendInScopeSetSet` fv_idInfo_set
        my_env        = setInScopeSet simpl_env my_in_scope

    let
      ru_opts         = seRuleOpts my_env           :: RuleOpts
      in_scope_env = getUnfoldingInRuleMatch my_env :: InScopeEnv
      act_fun      = activeRule (seMode my_env)     :: Activation -> Bool
      rules_id_str = show $ map (prettyString . pstl_id) pstls
      (Var f_target, args_targetgs) = collectArgs expr

    case lookupRule ru_opts in_scope_env act_fun f_target args_targetgs rules of
      Nothing -> do
        logMsg     $ "Rule `" ++ rules_id_str ++ "`not fired." ++ "\n"
        throwError $ "Rule `" ++ rules_id_str ++ "`not fired." ++
          "\nRule:\n" ++ prettyString pstls ++
          "\nExpr:\n" ++ prettyString expr ++ "\n"
      Just (applied_rule, new_expr) -> do
          logMsg $ "Rule fired:" ++ rules_id_str ++ "\n"
          return $ reapplyExtraArgs applied_rule new_expr

  where
    reapplyExtraArgs applied_rule new_expr = mkApps new_expr (leftoverArgs applied_rule)
    leftoverArgs ap_ru = drop (ruleArity ap_ru) $ snd (collectArgs expr)


---- POSTULATE REGISTRY
-- | Helper creating PostlDef
mkRulePstl :: HscEnv -> Id -> [CoreBndr] -> CoreExpr -> CoreExpr -> Maybe PostlDef
mkRulePstl hscEnv pstl_id pstl_binds pstl_lhs pstl_rhs =
  case lhs_func of
        Var fid -> Just $ mkRuleHelper (getName fid) fid
        _       -> Nothing
  where
    (lhs_func, lhs_args) = collectArgs pstl_lhs
    mkRuleHelper lhs_f_name f_id = PostlDef pstl_id f_infoId rule
      where
        rule = mkRule
          (getModule hscEnv)
          False
          True
          (mkFastString ("my-rule-" ++ getStrById pstl_id))
          AlwaysActive
          lhs_f_name
          pstl_binds
          lhs_args
          pstl_rhs
        f_infoId = modifyIdInfo (`setRuleInfo` RuleInfo [rule] emptyDVarSet) f_id
        getModule = mainModIs . hsc_HUE

madePostulate :: Id -> CheckerM ()
madePostulate fn_id =
  do
    (f_id, f_body)     <- getBodyByFuncId fn_id
    let (pstl_binds, _) = collectBinders f_body
    declConvrs <- gets st_declconvrs

    (convrs_fst, convrs_lst) <- case lookup f_id declConvrs of
      Just convrs@(cnvr:_) -> return (cnvr, last convrs)
      _                    -> throwError $
        "Unexpected state. Succesfully analized " ++ getStrById f_id ++ " but it doesn't have conversions."
    hscEnv     <- gets st_hscenv
    case mkRulePstl hscEnv f_id pstl_binds (cn_lhs convrs_fst) (cn_rhs convrs_lst) of
      Nothing -> logMsg $ "Can't make postulate from `" ++ prettyString f_id ++
        "`.\n  Pstl_lhs must be of form (f e1 .. en) where f is not forall'd.\n"
      Just new_postl -> do
        logMsg $ "Made new postulate from: " ++ prettyString f_id ++ "\n"
        modify (\st -> st { st_postldefs = new_postl : st_postldefs st})


---- JUDGMENT
-- | Final comparison
cmpCnvrs :: CoreExpr -> CoreExpr -> CheckerM ()
cmpCnvrs e_cntr e | alphaEq e_cntr e = logMsg "Compare result: True\n"
cmpCnvrs e_cntr e =
  do
    logMsg $
      "EXPR: " ++ prettyString e ++ "\n" ++
      "==?==\n" ++
      "CNTR: " ++ prettyString e_cntr ++ "\n" ++
      "Compare result: False\n"
    throwError $ "Error. Not equal." ++
      "\n\nExpected: " ++ prettyString e_cntr ++
      "\n\n    Got: " ++ prettyString e ++ "\n"
