{-|
Module      : ProofBase
Description : Annotation operators and base function defenition from Haskell report.

This module contains operators for  annotating equation reasonings and basic functions coppied from Haskell report.
-}
module ProofBase (Tactic, Rewrite, TacticN(..), RewriteN(..), (--.), (===), (.), ($), id, flip, const) where

import Language.Haskell.TH (Name)
import Prelude hiding ((.), ($), id, flip, const)

-- | Tactic annotation for the conversion
data TacticN n = L (RewriteN n) | R (RewriteN n) | QED | Postulate

-- | Rewrite rule applied to the expression.
-- @n@ is the name payload: 'Name' for user-facing DSL
-- (so @Def \'id@ compiles only if @id@ is in scope),
-- a decoded reference for checker internals
data RewriteN n = Def n | Prop n | Inst n | Beta | Eta | DefRec n Integer

type Tactic  = TacticN Name
type Rewrite = RewriteN Name

-- | Operator for adding Tactic annotation to the conversion
(--.) :: a -> Tactic -> a
(--.) x _ = x

-- | Main operator for building conversion chain
infixl 0 ===
(===) :: a -> a -> a
(===) _ y = y




-- MY FUNCTIONS
infixr 9 .
(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

infixr 0 $
($)    :: (a -> b) -> a -> b
($) f x = f x

id                      :: a -> a
id x                    =  x

flip :: (a -> b -> c) -> b -> a -> c
flip f x y              =  f y x

const :: a -> b -> a
const x _  =  x
