{-|
Module      : ProofBase
Description : Annotation operators and base function defenition from Haskell report.

This module contains operators for  annotating equation reasonings and basic functions coppied from Haskell report.
-}
module ProofBase (Tactic(..), Rewrite(..), (--.), (===), (.), ($), id, flip, const) where

import Prelude hiding ((.), ($), id, flip, const)

-- | Tactic annotation for the conversion
data Tactic = L Rewrite | R Rewrite  | QED | Postulate
-- | Rewrite rule applied to the expression
data Rewrite = Def String | Prop String | Inst String | Beta | Eta | DefRec String Integer

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
