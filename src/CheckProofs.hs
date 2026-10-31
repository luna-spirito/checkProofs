{-# LANGUAGE RecordWildCards, FlexibleContexts, LambdaCase #-}

{-|
Module      : CheckProofs
Description : Checking equational reasoning
License     : MIT

Untrusted tactic layer of the checker: decodes tactics from the
desugared program, selects rewrite sites, proposes one-step proofs
("Kernel.Pf") to the trusted kernel ("Kernel") and chains the
kernel-verified transitions into whole theorems. The output theorems
are kernel objects: this layer cannot construct one itself.
-}
module CheckProofs
  ( checkProofs
  , checkProofsReport
  , checkProofsTheorems
  ) where

import GHC
    ( runGhc,
      setSessionDynFlags,
      getSessionDynFlags,
      GhcMonad(..), guessTarget, setTargets, depanal, mgModSummaries, parseModule, typecheckModule, desugarModule, DesugaredModule (dm_core_module), LoadHowMuch (LoadAllTargets), load, setTargets)
import GHC.Paths (libdir)
import GHC.Core
import GHC.Plugins hiding (L, getModule)
import Control.Monad.IO.Class (MonadIO)

import System.FilePath ((</>))
import Control.Monad.State.Lazy ( StateT, runStateT, gets, modify )
import Control.Monad.Except ( ExceptT, runExceptT, MonadError(..) )
import Control.Applicative ((<|>))
import qualified Data.ByteString.Char8 as BS8
import Data.Generics.Uniplate.Data (universe)
import Data.Functor ((<&>))
import Data.List (find)
import Data.Bifunctor (bimap)

import Kernel
    ( Theorem, thmLeft, thmRight
    , Pf(..), Ctx(..)
    , alphaEq, alphaEqWithEnv
    , postThm, symThm
    , KernelST(..), KernelM
    , getStrById, inlineLetsIgnoreCast, FuncDef, pstl_id
    )
import qualified Kernel (kernelStep, kernelBeta, transThm, madePostulate, logMsg)
import AstInfo
import PrettyString (prettyString, prettyStringReport)
import ProofBase ( RewriteN(..), TacticN(..) )
import SortDecls ( sorteDeclConvrs )


proofbasePath :: FilePath
proofbasePath = "src" </> "ProofBase.hs"

-- | The checker log; tactics and kernel emit lines via 'logMsg' into
-- the state and 'analyzeModuleSt' flushes them here.
logPath :: FilePath
logPath = "logs" </> "app.txt"

-- | Write directly to the log file, outside the checker monad.
logMsg' :: MonadIO m => String -> m ()
logMsg' message = liftIO $ appendFile logPath (message ++ "\n")

checkProofs :: String -> IO ()
checkProofs filePath = putStr =<< checkProofsReport filePath

-- | Run the checker on the file and return everything 'checkProofs' prints to stdout
checkProofsReport :: String -> IO String
checkProofsReport filePath = fst <$> checkProofsResult filePath

-- | Run the checker and return, for every successfully proved
-- declaration, the kernel-built theorem of its whole chain.
checkProofsTheorems :: String -> IO [(Id, Theorem)]
checkProofsTheorems filePath = snd <$> checkProofsResult filePath

checkProofsResult :: String -> IO (String, [(Id, Theorem)])
checkProofsResult filePath = do
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
    (report, theorems) <- liftIO $ analyzeModuleSt astState

    logMsg' "\n===== The End: App/Main ====="
    return (analyzing_file_str ++ "\n" ++ report ++ "\n" ++ "\n===== The End: App/Main =====\n", theorems)



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
-- | Tactic-layer state: the embedded kernel state plus the decoded
-- conversions and report bookkeeping.
data CheckerST = CheckerST {
  st_kernel       :: KernelST,

  -- | Conversions grouped by declaration.
  st_declconvrs   :: [DeclConversions],

  -- | Number of generated conversions.
  st_cnvrs_count  :: Int,

  -- | Identifier of the declaration currently being processed.
  st_declconvr_id :: Maybe Id,

  -- | Log lines, most recent first; kernel lines are spliced in by
  -- 'zoomKernel' so the order stays chronological.
  st_log          :: [String]
}

-- | Checker monad.
type CheckerM = ExceptT String (StateT CheckerST IO)

-- | Run a kernel computation on the embedded kernel state, splicing
-- its log lines into the checker log in order.
zoomKernel :: KernelM a -> CheckerM a
zoomKernel kma =
  do
    ks <- gets st_kernel
    (res, ks') <- liftIO $ runStateT (runExceptT kma) ks { ks_log = [] }
    modify (\st -> st { st_kernel = ks' { ks_log = [] }
                      , st_log    = ks_log ks' ++ st_log st })
    either throwError return res

-- Kernel API lifted into the checker monad.
logMsg :: String -> CheckerM ()
logMsg = zoomKernel . Kernel.logMsg

kernelStep :: CoreExpr -> Pf -> CoreExpr -> CheckerM Theorem
kernelStep src pf target = zoomKernel $ Kernel.kernelStep src pf target

kernelBeta :: CoreExpr -> CoreExpr -> CheckerM Theorem
kernelBeta ctl e = zoomKernel $ Kernel.kernelBeta ctl e

transThm :: Theorem -> Theorem -> CheckerM Theorem
transThm tl tr = zoomKernel $ Kernel.transThm tl tr

madePostulate :: Id -> Theorem -> CheckerM ()
madePostulate fn_id thm = zoomKernel $ Kernel.madePostulate fn_id thm

-- | Get Checker state
getState :: HscEnv -> CoreProgram -> CoreProgram -> CheckerST
getState hscEnv core_binds base_binds = CheckerST {
  st_kernel = KernelST {
    st_funcdefs  = binds,
    st_base_defs = flattenBinds base_binds,
    st_postldefs = [],
    st_hscenv    = hscEnv,
    ks_log       = []
  },
  st_declconvrs   = sortedDeclConvrs,
  st_cnvrs_count  = 0,
  st_declconvr_id = Nothing,
  st_log          = []
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
-- | Main analyzing entry function. Returns the report printed by
-- 'checkProofs' and the kernel-built theorem of every proved decl.
analyzeModuleSt :: CheckerST -> IO (String, [(Id, Theorem)])
analyzeModuleSt checkerST =

  do
    result <- mapPassStM runChecker (st_declconvrs checkerST) checkerST
    -- flush the log accumulated in the state (oldest first), with the
    -- full report as the closing line
    let final_st = if null result then checkerST else snd (last result)
    liftIO $ appendFile logPath $
      unlines (reverse (st_log final_st)) ++
      prettyStringReport True (toReport result)
    return ( prettyStringReport False $ toReport result
           , [ (rid, thm) | (Right (rid, thms), _) <- result, thm <- thms ] )

  where
    runChecker x = runStateT (runExceptT (analyzeDeclCnvrs x))
    toReport     = foldr resToReport ([], [])
    resToReport (res, st) (succs, fails) = case res of
      Left reason           -> (succs          , createFail st reason : fails)
      Right (res_id, _thms) -> (res_id : succs,                        fails)

    analyzeDeclCnvrs :: DeclConversions -> CheckerM (Id, [Theorem])
    analyzeDeclCnvrs (decl_id, cnvrs) =
      do
        newDeclCnvrs decl_id
        logMsg $ "\n-----------------------------\n" ++
          "Start analyze declConversion: " ++ prettyString decl_id ++ "\n"
        transitions <- mapM analyzeConvrs cnvrs
        thms        <- chainThms transitions
        mapM_ (madePostulate decl_id) thms
        return (decl_id, thms)

    -- A decl defined by pattern matching desugars to several
    -- disconnected chains (one per equation clause); fold each into
    -- its own theorem. transThm rejects mismatches, so only genuinely
    -- connected transitions compose.
    chainThms []     = throwError "Internal error. Decl with no conversions."
    chainThms (t:ts) = go t ts
      where
        go acc []     = return [acc]
        go acc (u:us)
          | alphaEq (thmRight acc) (thmLeft u) = transThm acc u >>= \acc' -> go acc' us
          | otherwise                           = (acc :) <$> go u us


---- ANALYZE SINGLE CONVERSION
-- | Main function entry for analyzing single conversion
analyzeConvrs :: Conversion -> CheckerM Theorem
analyzeConvrs Conversion{..} =
  do
    incCnvrsCounter
    case cn_info of
      Postulate -> return $ postThm cn_lhs cn_rhs
      L info    -> analyze cn_lhs cn_rhs info
      R info    -> symThm <$> analyze cn_rhs cn_lhs info
      info      -> throwError $ "Unexpected converseion_info. Expected useful information. Get:" ++ prettyString info

  where
    -- Proves the transition theorem @expr ≡ control_expr@: the tactic
    -- rewrites @expr@ and the kernel must reach @control_expr@.
    analyze expr control_expr expr_info = do
      let analyzeExpr = case expr_info of
            Def  comment   -> analyzeDefConv  comment 0
            Prop comment   -> analyzePropConv comment
            Inst comment   -> analyzeInstConv comment
            DefRec cmnt n  -> analyzeDefConv  cmnt n
            Eta            -> analyzeEtaConv
            Beta           -> analyzeBetaConv
      analyzeExpr control_expr expr


---- TACTICS
-- Each tactic selects where the rewrite applies (getFirstDiff /
-- getNAppearance), checks the target against the tactic's name, and
-- proposes a kernel step; the kernel validates the rewrite itself and
-- that the proposed site decomposes the rewritten line.

---- just believe that this is enought
-- | Function search of first diff between expression.
-- Returns the differing subexpression and the context it sits in;
-- @plugCtx ctx diff@ is always the inspected line.
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
          -- the diff extends up the application spine; the site is the
          -- whole spine, so the context resets with every extension
          (diff, _, True)    -> (App diff arg, Hole, True)
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
analyzeBetaConv :: CoreExpr -> CoreExpr -> CheckerM Theorem
analyzeBetaConv control_expr expr =
  do
    logMsg "Evaluate beta-conversion"
    -- kernelBeta proves @control_expr ≡ expr@ by normalizing both;
    -- the transition goes the other way, hence symmetry
    symThm <$> kernelBeta control_expr expr

-- | Analyze Def annotated conversions
analyzeDefConv :: NameRef -> Integer -> CoreExpr -> CoreExpr -> CheckerM Theorem
analyzeDefConv comment n control_expr expr =
  do
    logMsg "Evaluate def-conversion"
    (diff_expr, ctx) <-
      if n <= 0
        then getFirstDiff control_expr expr
        else getNAppearance comment n expr
    let (func, args) = collectArgs diff_expr
    func_id         <- checkComment func
    kernelStep expr (DefAt ctx func_id args) control_expr

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
analyzePropConv :: NameRef -> CoreExpr -> CoreExpr -> CheckerM Theorem
analyzePropConv comment control_expr expr =
  do
    logMsg "Evaluate prop-conversion"
    (diff_expr, ctx) <- getFirstDiff control_expr expr
    postl_defs       <- gets (st_postldefs . st_kernel)
    let matchedPstls  = filter (nameMatchesId comment . pstl_id) postl_defs
    pstl <- case matchedPstls of
      [pstl] -> return pstl
      (_:_)  -> throwError $ "Unexpected postulate. Found more than one matched with comment `" ++ show comment ++ "`"
      []     -> throwError $ "Unexpected postulate. Not found match with comment `"             ++ show comment ++ "`"

    case collectArgs diff_expr of
      (Var _, _) -> return ()
      _          -> throwError $ "Not implemented: " ++ "postl dif not var."
    kernelStep expr (RuleAt ctx diff_expr pstl) control_expr


-- | Analyze Inst annotated conversions
analyzeInstConv :: NameRef -> CoreExpr -> CoreExpr -> CheckerM Theorem
analyzeInstConv comment control_expr expr =
  do
    logMsg "Evaluate inst-conversion"
    (diff_expr, ctx) <- getFirstDiff control_expr expr
    let (func, _) = collectArgs diff_expr
    _  <- checkComment func
    kernelStep expr (InstAt ctx diff_expr) control_expr

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
analyzeEtaConv :: CoreExpr -> CoreExpr -> CheckerM Theorem
analyzeEtaConv control_expr expr =
  do
    logMsg "Evaluate eta-reduction"
    (diff_expr, ctx) <- getFirstDiff control_expr expr
    kernelStep expr (EtaAt ctx diff_expr) control_expr
