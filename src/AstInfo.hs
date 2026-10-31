{-|
Module      : AstInfo
Description : Tactic-layer data: decoded conversions and report types.
License     : MIT
-}
module AstInfo
  ( NameRef(..)
  , nameMatchesId
  , Conversion(..)
  , DeclConversions
  , ReportFail
  , Report
  ) where

import GHC.Core ( CoreExpr )
import GHC.Types.Id ( Id )
import GHC.Plugins ( idName, getOccName, occNameString, nameModule_maybe
                   , moduleName, moduleNameString, moduleUnit, unitString )

import ProofBase ( TacticN )

-- | Name of a tactic target, decoded from its desugared TH quote.
-- Occurrence name is always present; module and package only when
-- the quote carried them (plain 'x quotes always do).
data NameRef = NameRef
  { nrOcc :: String,
    nrMod :: Maybe String,
    nrPkg :: Maybe String
  }

instance Show NameRef where
  show (NameRef occ mmod _) = maybe "" (++ ".") mmod ++ occ

-- | Does a decoded 'NameRef' denote this 'Id'?
--
-- Occurrence names must be equal; when both sides carry a module,
-- module and package must agree too.
nameMatchesId :: NameRef -> Id -> Bool
nameMatchesId NameRef{ nrOcc = occ, nrMod = mmod, nrPkg = mpkg } var =
  occ == occNameString (getOccName var)
  && case (mmod, nameModule_maybe (idName var)) of
       (Just ref_mod, Just id_mod) ->
         ref_mod == moduleNameString (moduleName id_mod)
         && maybe True (\pkg -> pkg == unitString (moduleUnit id_mod)) mpkg
       _ -> True

-- | Represents a conversion between two Core expressions.
--
-- The conversion stores:
--
-- * the left-hand side expression
-- * the right-hand side expression
-- * information about operation
data Conversion = Conversion {
  -- | Left-hand side expression.
  cn_lhs  :: CoreExpr,

  -- | Right-hand side expression.
  cn_rhs  :: CoreExpr,

  -- | Conversion tactic.
  cn_info :: TacticN NameRef
}

-- | All conversions associated with a declaration identifier.
--
-- The 'Id' identifies the declaration, while the list contains all
-- conversions known for that declaration.
type DeclConversions = (Id, [Conversion])

-- | A failed report entry.
--
-- Contains:
--
-- * the identifier that failed
-- * an explanatory error message
type ReportFail = (Id, String)

-- | Final checker report.
--
-- The first component contains successful identifiers,
-- while the second contains failures.
type Report = ([Id], [ReportFail])
