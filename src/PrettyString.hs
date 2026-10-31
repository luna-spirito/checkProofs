{-# LANGUAGE RecordWildCards, FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-|
Module      : PrettyString
Description : Creat pretty string for app data types

This module creates string representations for types and data from AstInfo and ProofBase using instance Outputable.
-}
module PrettyString (prettyString, prettyStringReport) where

import GHC.Utils.Outputable
    ( Outputable(..),
      IsLine((<+>), text),
      doubleQuotes,
      integer,
      nest,
      parens,
      showSDocUnsafe,
      IsDoc(($$)) )

import Data.List (intercalate, sort, sortOn)

import AstInfo
import ProofBase ( RewriteN(..), TacticN(..) )



instance Outputable Conversion where
  ppr c =
    text "Conversion"
      $$ nest 2 (
           text "lhs:"  <+> ppr (cn_lhs c)
        $$ text "rhs:"  <+> ppr (cn_rhs c)
        $$ text "info:" <+> ppr (cn_info c)
      )

instance Outputable (RewriteN NameRef) where
  ppr rewrite =
    case rewrite of
      Def name ->
        text "Def " <+> doubleQuotes (text (show name))
      Prop name ->
        text "Prop" <+> doubleQuotes (text (show name))
      Inst name ->
        text "Inst" <+> doubleQuotes (text (show name))
      Beta ->
        text "Beta"
      Eta ->
        text "Eta "
      DefRec name depth ->
        text "DefRec"
          <+> doubleQuotes (text (show name))
          <+> parens (text "depth =" <+> integer depth)


instance Outputable (TacticN NameRef) where
  ppr sideInfo =
    case sideInfo of
      L expr ->
        text "L" <+> ppr expr
      R expr ->
        text "R" <+> ppr expr
      QED ->
        text "QED"
      Postulate ->
        text "Postulate"



prettyString :: (Outputable a) => a -> String
prettyString = showSDocUnsafe . ppr

-- type Report = ([Id], [(Id, String)])
-- Bool - with reasons or without
--
-- The names are sorted here: the original order comes from a topological sort
-- whose traversal order is not stable between runs (it depends on GHC uniques),
-- so only the sorted report is deterministic enough for golden tests.
prettyStringReport :: Bool -> Report -> String
prettyStringReport withReasons (succs, failsWithReasons) =
  "\n============================================" ++
  "\n================== REPORT ==================" ++
  "\nSuccsessfully proved: " ++ prettyRes succs ++ "\n" ++
  "\nFailures proved: "      ++ prettyRes fails ++ "\n" ++
  (if withReasons
    then "Reasons for failures:\n\n" ++ intercalate "\n" reasons ++ "\n"
    else "\n")
  ++ "============================================\n"
  where
    prettyRes [] = "0" ++ "\n  " ++ "<None>"
    prettyRes xs = show (length xs) ++ "\n  " ++ intercalate "\n  " (sort (map prettyString xs))
    (fails, reasons) = unzip (sortOn (prettyString . fst) failsWithReasons)
