{-|
Module      : SortDecls
Description : Topologicaly sort DeclConversions

Topologicaly sort DeclConversions and check for cyrcle dependencies
-}
module SortDecls (sorteDeclConvrs) where

import GHC (Id)
import Data.Graph
import Data.Maybe (mapMaybe)
import Data.List (find)
import Data.List.NonEmpty (toList)

import AstInfo
import PrettyString
import ProofBase ( RewriteN(..), TacticN(..) )

sorteDeclConvrs :: [DeclConversions] -> Either Cyrcles [DeclConversions]
sorteDeclConvrs declConvrs = topoSort $ toNodes declConvrs

--            (value,              key, depend_on)
type EdgeDC = (DeclConversions,    Id,  [Id])
type Cyrcles = [[Id]]

toNodes :: [DeclConversions] -> [EdgeDC]
toNodes decls = map (\dc@(decl_id, cnvrs) -> (dc, decl_id, cnInfoStr cnvrs)) decls
  where
    cnInfoStr :: [Conversion] -> [Id]
    cnInfoStr = mapMaybe (rewriteToId . cnToRewrite)
    rewriteToId cnvr = case cnvr of
      Just (Def  nm) -> findIdByName nm
      Just (Prop nm) -> findIdByName nm
      _              -> Nothing
    cnToRewrite  cnvr = case cn_info cnvr of
      L ei -> Just ei
      R ei -> Just ei
      Postulate -> Nothing
      info -> error $ "Unexpected comment for conversion. Expected L or R. Got:" ++ prettyString info
    findIdByName nm = find (nameMatchesId nm) (map fst decls)



topoSort :: [EdgeDC] -> Either Cyrcles [DeclConversions]
topoSort dc_edges =
  case stronglyConnComp dc_edges of
    cyclic@(_:_)
      | any isCycle cyclic -> Left (collectCycles cyclic)
    sccs -> Right [ v | AcyclicSCC v <- sccs ]
  where

    isCycle :: SCC DeclConversions -> Bool
    isCycle (AcyclicSCC _) = False
    isCycle _              = True

    collectCycles :: [SCC DeclConversions] -> Cyrcles
    collectCycles =
      foldr go []
      where
        go :: SCC DeclConversions -> Cyrcles -> Cyrcles
        go (NECyclicSCC vs) acc = map fst (toList vs) : acc
        go _ acc                = acc
