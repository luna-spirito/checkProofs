{-# LANGUAGE RecordWildCards, FlexibleContexts, LambdaCase #-}

{-|
Module      : CheckProofs
Description : Checking equational reasoning
License     : MIT

Untrusted tactic layer of the checker: decodes tactics from the
desugared program, selects rewrite sites, proposes one-step proofs
("Pf") to the trusted kernel ("Kernel") and checks that kernel
theorems line up with the user's chain.
-}
module CheckProofs where

import GHC
    ( runGhc,
      setSessionDynFlags,
      getSessionDynFlags,
      GhcMonad(..), guessTarget, setTargets, depanal, mgModSummaries, parseModule, typecheckModule, desugarModule, DesugaredModule (dm_core_module), LoadHowMuch (LoadAllTargets), load, setTargets)
import GHC.Paths (libdir)
import GHC.Core
import GHC.Plugins hiding (L, getModule)

import System.FilePath ((</>))
import Control.Monad.State.Lazy ( runStateT, gets, modify )
import Control.Monad.Except ( runExceptT, MonadError(..) )
import Control.Applicative ((<|>))
import qualified Data.ByteString.Char8 as BS8
import Data.Generics.Uniplate.Data (universe)
import Data.Functor ((<&>))
import Data.List (find)
import Data.Bifunctor (bimap)

import AstInfo
import Kernel
import PrettyString
import ProofBase ( RewriteN(..), TacticN(..) )
import SortDecls ( sorteDeclConvrs )


proofbasePath :: FilePath
proofbasePath = "src" </> "ProofBase.hs"

checkProofs :: String -> IO ()
checkProofs filePath = putStr =<< checkProofsReport filePath

-- | Run the checker on the file and return everything 'checkProofs' prints to stdout
checkProofsReport :: String -> IO String
checkProofsReport filePath = do
  runGhc (Just libdir) $ do
    dflags' <- getSessionDynFlags
    let dflags = gopt_set dflags' Opt_EnableRewriteRules
    _ <- setSessionDynFlags dflags
    session <- getSession

    let analyzing_file_str = "ANALUZING FILE: " ++ filePath ++ "\n"
    liftIO $ writeFile logPath analyzing_file_str
    (mg_main, mg_base) <- getModulesGuts filePath

    -- create State
    let astState = getState session (mg_binds mg_main) (mg_binds mg_base)
    report <- liftIO $ analyzeModuleSt astState

    logMsg "\n===== The End: App/Main ====="
    return (analyzing_file_str ++ "\n" ++ report ++ "\n" ++ "\n===== The End: App/Main =====\n")



-- | Get Module guts for provided file and ProofsBase.hs
getModulesGuts :: GhcMonad m => String -> m (ModGuts, ModGuts)
getModulesGuts filePath =
  do
    targets <- mapM (\fp -> guessTarget fp Nothing Nothing) [filePath, proofbasePath]
    setTargets targets
    _ <- load LoadAllTargets

    modGraph <- depanal [] False
    mg_base  <-
      case find (\m -> "ProofBase" == showSDocUnsafe (ppr (moduleName (ms_mod m)))) $ mgModSummaries modGraph of
        Just ms -> getModGuts ms
        Nothing -> error $ "Error. Module `ProofBase` not found. All modules:\n" ++ showSDocUnsafe (ppr (map (moduleName . ms_mod) (mgModSummaries modGraph)))
    mg_main <-
      case filter (\m -> "ProofBase" /= showSDocUnsafe (ppr (moduleName (ms_mod m)))) $ mgModSummaries modGraph of
        [ms] -> getModGuts ms
        _    -> error "Error. Expected to find single NOT `ProofBase` Module"
    return (mg_main, mg_base)
  where
    getModGuts :: GhcMonad m => ModSummary -> m ModGuts
    getModGuts ms = parseModule ms >>= typecheckModule >>= desugarModule <&> dm_core_module


---- COLLECTING AST STATE
-- | Get Checker state
getState :: HscEnv -> CoreProgram -> CoreProgram -> CheckerST
getState hscEnv core_binds base_binds = CheckerST {
  st_declconvrs   = sortedDeclConvrs,
  st_funcdefs     = binds,
  st_postldefs    = [],
  st_hscenv       = hscEnv,
  st_base_defs    = flattenBinds base_binds,
  st_cnvrs_count  = 0,
  st_declconvr_id = Nothing
  -- TODO. maybe add st_counter = CheckerCounter{}
}
  where
  binds    = map (fmap inlineLetsIgnoreCast) $ flattenBinds core_binds
  sortedDeclConvrs = case sorteDeclConvrs $ concatMap collectConvrs binds of
    Left cyrcles -> error $ "Error. Cyrcle dependencies were found.\n" ++ showSDocUnsafe (ppr cyrcles)
    Right sdc    -> sdc

-- | Helper function for collecting conversions from function defenition
collectConvrs :: FuncDef -> [DeclConversions]
collectConvrs (f_id, f_body) = case map getConvrs pairs_skip_lhe_qed of
    []      -> []
    convrs  -> [(f_id, convrs)]
  where
  argAddInfo = [(argExpr, argComm) |
    (App (App (App (Var exprName) _) argExpr) argComm) <- universe f_body,
    "--." <- [getStrById exprName] ]
  pairs  = zip argAddInfo (drop 1 argAddInfo)
  pairs_skip_lhe_qed = filter (\((_, v_cmnt), _) -> not (isTacticCon "QED" v_cmnt)) pairs
  getConvrs ((lhe, c1), (rhe, _)) = Conversion lhe rhe (toTactic c1)
---- END COLLECTING AST STATE


---- UTILS
-- | Helper function to create pretty fails report
createFail :: CheckerST -> String -> (Id, String)
createFail CheckerST{..} reason = (,) d_id $
    "Fail in decl: " ++ str_decl_id ++ " in conversion number: " ++ show st_cnvrs_count ++
    "\nReason:\n" ++ reason ++ "\n"
  where
    (d_id, str_decl_id) = case st_declconvr_id of
      Just d  -> (d, getStrById d)
      Nothing -> error "Have failure but no st_declconvr_id"

-- | Is the expression an application of a tactic data constructor?
-- Polymorphic constructors are applied to a type first in Core (@QED \@\@n@).
isTacticCon :: String -> CoreExpr -> Bool
isTacticCon str expr = case collectArgs expr of
  (Var v, _) -> getStrById v == str
  _          -> False

-- | Value arguments of an application spine, without type instantiations
valArgsOf :: [CoreExpr] -> [CoreExpr]
valArgsOf = filter (\case Type _ -> False; _ -> True)

toTactic :: CoreExpr -> TacticN NameRef
toTactic tactic_expr =
  case collectArgs tactic_expr of
    (Var side, args) -> case (getStrById side, valArgsOf args) of
      ("L", [info])     -> L  (toRewrite info)
      ("R", [info])     -> R  (toRewrite info)
      ("Postulate", []) -> Postulate
      _                 -> err
    _ -> err
  where
    err = error $ "Unexpected expression structure for tactic, expected `L` or `R` applied to a rewrite, or `Postulate`.\nGot: " ++ prettyString tactic_expr

-- | Polymorphic rewrite constructors are applied to a type first
-- in Core (@Def \@\@n \'id@), so match on the application spine
-- with the type instantiations stripped.
toRewrite :: CoreExpr -> RewriteN NameRef
toRewrite rw_expr =
  case collectArgs rw_expr of
    (Var con, args) -> case (getStrById con, valArgsOf args) of
      ("Beta", [])    -> Beta
      ("Eta", [])     -> Eta
      ("Def", [nm])   -> Def  (nameRefFromCore nm)
      ("Prop", [nm])  -> Prop (nameRefFromCore nm)
      ("Inst", [nm])  -> Inst (nameRefFromCore nm)
      ("DefRec", [nm, App _ (Lit (LitNumber _ n))]) | n > 0 -> DefRec (nameRefFromCore nm) n
      _               -> err
    _ -> err
  where
    err = error $ "Unexpected expression structure for rewrite, expected `Beta`, `Eta`, `Def 'name'`, `Prop 'name'`, `Inst 'name'` or `DefRec 'name n > 0`.\nGot: " ++ prettyString rw_expr

-- | Recover a quoted name from its desugared TH quote in Core:
-- @mkNameG_v \"pkg\" \"module\" \"occname\"@
nameRefFromCore :: CoreExpr -> NameRef
nameRefFromCore name_expr =
  case name_expr of
    App (App (App (Var v) (App _ (Lit (LitString pkg))))
                (App _ (Lit (LitString modul))))
                (App _ (Lit (LitString occ)))
      | getStrById v == "mkNameG_v" ->
          NameRef { nrOcc = BS8.unpack occ
                  , nrMod = Just (BS8.unpack modul)
                  , nrPkg = Just (BS8.unpack pkg) }
    _ -> error $ "Unexpected expression structure for quoted name.\nGot: " ++ prettyString name_expr


mapPassStM :: (Monad m) => (a -> s -> m (b, s)) -> [a] -> s -> m [(b, s)]
mapPassStM _ [] _ = return []
mapPassStM f (a:as) s = do
  r@(_, s1) <- f a s
  (r :) <$> mapPassStM f as s1


incCnvrsCounter :: CheckerM ()
incCnvrsCounter =
  do
    modify (\st -> st { st_cnvrs_count = st_cnvrs_count st + 1 })
    cnvrs_count <- gets st_cnvrs_count
    decl_id     <- gets st_declconvr_id
    logMsg $ "\n----------------\n" ++
      "Start analyzing: decl=`" ++ prettyString decl_id ++ "` conversion=" ++ show cnvrs_count ++ "\n"

newDeclCnvrs :: Id -> CheckerM ()
newDeclCnvrs decl_id = modify (\st -> st { st_cnvrs_count = 0, st_declconvr_id = Just decl_id })


------ Analyze
-- | Main analyzing entry function. Returns the report printed by 'checkProofs'
analyzeModuleSt :: CheckerST -> IO String
analyzeModuleSt checkerST =

  do
    result <- mapPassStM runChecker (st_declconvrs checkerST) checkerST
    logMsg $ prettyStringReport True $ toReport result
    return $ prettyStringReport False $ toReport result

  where
    runChecker x = runStateT (runExceptT (analyzeDeclCnvrs x))
    toReport     = foldr resToReport ([], [])
    resToReport (res, st) (succs, fails) = case res of
      Left reason  -> (succs         , createFail st reason : fails)
      Right res_id -> (res_id : succs,                        fails)

    analyzeDeclCnvrs :: DeclConversions -> CheckerM Id
    analyzeDeclCnvrs (decl_id, cnvrs) =
      do
        newDeclCnvrs decl_id
        logMsg $ "\n-----------------------------\n" ++
          "Start analyze declConversion: " ++ prettyString decl_id ++ "\n"
        mapM_ analyzeConvrs cnvrs
        madePostulate decl_id
        return decl_id


---- ANALYZE SINGLE CONVERSION
-- | Main function entry for analyzing single conversion
analyzeConvrs :: Conversion -> CheckerM ()
analyzeConvrs Conversion{..} =
  do
    incCnvrsCounter
    case cn_info of
      Postulate -> return ()
      L info    -> analyze cn_lhs cn_rhs info
      R info    -> analyze cn_rhs cn_lhs info
      info      -> throwError $ "Unexpected converseion_info. Expected useful information. Get:" ++ prettyString info

  where
    analyze expr control_expr expr_info =
      do
        let analyzeExpr = case expr_info of
              Def  comment   -> analyzeDefConv  comment 0
              Prop comment   -> analyzePropConv comment
              Inst comment   -> analyzeInstConv comment
              DefRec cmnt n  -> analyzeDefConv  cmnt n
              Eta            -> analyzeEtaConv
              Beta           -> analyzeBetaConv
        (ce, e) <- analyzeExpr control_expr expr
        cmpCnvrs ce e


---- TACTICS
-- Each tactic selects where the rewrite applies (getFirstDiff /
-- getNAppearance), checks the target against the tactic's name, and
-- proposes a kernel step; the kernel validates the rewrite itself.

---- just believe that this is enought
-- | Function search of first diff between expression.
-- Returns the differing subexpression and the context it sits in.
getFirstDiff :: CoreExpr -> CoreExpr -> CheckerM (CoreExpr, Ctx)
getFirstDiff contrl_expr expr =
  do
    (d_expr, ctx, _) <- go ([], []) contrl_expr expr
    logMsg $ "getFirstDiff result:" ++
      "\ncntr_expr:\n" ++ prettyString contrl_expr ++
      "\nexpr:\n" ++ prettyString d_expr ++ "\n"
    return (d_expr, ctx)

  where
    go cm_envs (Lam cntr_b cntr_body) (Lam b body) = do
      let new_cm_envs = bimap (cntr_b :) (b :) cm_envs
      res <- go new_cm_envs cntr_body body
      return $ updBuilder (CLam b) res
    go cm_envs ce@(App _ (Type _)) e@(App _ (Type _)) = checkEq cm_envs ce e True
    go cm_envs (App cntr_f cntr_arg) (App f arg) =
      (go cm_envs cntr_f f <&>
        \case
          (diff, ctx, True)  -> (App diff arg, ctx, True)
          (diff, ctx, False) -> (diff, CAppF ctx arg, False))
        <|> (go cm_envs cntr_arg arg <&> updBuilder (CAppA f))
    go cm_envs ce e@(App _ _) = checkEq cm_envs ce e True
    go cm_envs ce e = checkEq cm_envs ce e False

    updBuilder updater (diff_expr, ctx, _) = (diff_expr, updater ctx, False)
    checkEq cm_envs ce e is_collect
      | alphaEqWithEnv cm_envs ce e = throwError $ "No difference." ++
        "\n  cntr_expr: " ++ prettyString ce ++
        "\n       expr: " ++ prettyString e ++ "\n"
      | otherwise    = do
        logMsg $ "Get diff:\n  cntr_expr: " ++ prettyString ce ++ "\n       expr: " ++ prettyString e ++ "\n"
        return (e, Hole, is_collect)

getNAppearance :: NameRef -> Integer -> CoreExpr -> CheckerM (CoreExpr, Ctx)
getNAppearance comnt m expr = go m expr >>= (\(x, y, _) -> return (x, y))
  where
    go n (Lam b body) = go n body <&> updBuilder (CLam b)
    go n (App f arg) = do
      (new_e, new_ctx, new_n) <- go n f
      if new_n <= 0
        then return (new_e, CAppF new_ctx arg, new_n)
        else go n arg <&> updBuilder (CAppA f)
    go n f@(Var f_id) | nameMatchesId comnt f_id = return (f, Hole, n - 1)
    go n e = return (e, Hole, n)

    updBuilder updater (diff_expr, ctx, n) = (diff_expr, updater ctx, n)

-- | Analyze beta reduction conversions
analyzeBetaConv :: CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
-- TODO (next phase): verify with the trusted normalizer. Today both
-- sides are returned unchanged and only alphaEq-checked, which works
-- because the desugarer already beta-reduces source redexes.
analyzeBetaConv control_expr expr = return (control_expr, expr)

-- | Analyze Def annotated conversions
analyzeDefConv :: NameRef -> Integer -> CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
analyzeDefConv comment n control_expr expr =
  do
    logMsg "Evaluate def-conversion"
    (diff_expr, ctx) <-
      if n <= 0
        then getFirstDiff control_expr expr
        else getNAppearance comment n expr
    let (func, args) = collectArgs diff_expr
    func_id         <- checkComment func
    thm             <- kernelCheck (DefAt ctx func_id args)
    return (control_expr, thmRhs thm)

  where
    checkComment :: CoreExpr -> CheckerM Id
    checkComment (Var func_id)
      | nameMatchesId comment func_id = return func_id
      | otherwise                     = throwError $
        "Applied function_id does not match comment:" ++
        "\n Expected: " ++ show comment ++
        "\n Got     : " ++ prettyString func_id
    checkComment e = throwError $ "Applied expression not a function call!\nGot: " ++ prettyString e

-- | Analyze Prop annotated conversions
analyzePropConv :: NameRef -> CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
analyzePropConv comment control_expr expr =
  do
    logMsg "Evaluate prop-conversion"
    (diff_expr, ctx) <- getFirstDiff control_expr expr
    postl_defs       <- gets st_postldefs
    let matchedPstls  = filter (nameMatchesId comment . pstl_id) postl_defs
    pstl <- case matchedPstls of
      [pstl] -> return pstl
      (_:_)  -> throwError $ "Unexpected postulate. Found more than one matched with comment `" ++ show comment ++ "`"
      []     -> throwError $ "Unexpected postulate. Not found match with comment `"             ++ show comment ++ "`"

    case collectArgs diff_expr of
      (Var _, _) -> return ()
      _          -> throwError $ "Not implemented: " ++ "postl dif not var."
    thm <- kernelCheck (RuleAt ctx diff_expr pstl)
    return (control_expr, thmRhs thm)


-- | Analyze Inst annotated conversions
analyzeInstConv :: NameRef -> CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
analyzeInstConv comment control_expr expr =
  do
    logMsg "Evaluate inst-conversion"
    (diff_expr, ctx) <- getFirstDiff control_expr expr
    let (func, _) = collectArgs diff_expr
    checkComment func
    thm <- kernelCheck (InstAt ctx diff_expr)
    return (control_expr, thmRhs thm)

  where
    checkComment :: CoreExpr -> CheckerM Id
    checkComment (Var func_id)
      | nameMatchesId comment func_id = return func_id
      | otherwise  = throwError $
        "Applied function_id does not match comment:" ++
        "\n Expected: " ++ show comment ++
        "\n Got     : " ++ prettyString func_id
    checkComment e = throwError $ "Applied expression not a function call!\nGot: " ++ prettyString e

-- | Analyze eta reduction conversions
analyzeEtaConv :: CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
analyzeEtaConv control_expr expr =
  do
    logMsg "Evaluate eta-reduction"
    (diff_expr, ctx) <- getFirstDiff control_expr expr
    thm <- kernelCheck (EtaAt ctx diff_expr)
    return (control_expr, thmRhs thm)
