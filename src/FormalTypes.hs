module FormalTypes (
  module Math.Term,
  module Math.Util,
  module Math.InducTree,
  module Math.Induction.PiType,
  module Math.Induction.SigmaType,
  module Math.Induction.CoprodType, 
  module Math.Induction.NatType, 
  module Math.Induction.TypeMatch,
  module Data.Set,
  module Data.Tree,
  ctx0,
) where

import Math.Term
import Math.Util
import Math.InducTree
import Math.Induction.PiType
import Math.Induction.SigmaType
import Math.Induction.CoprodType
import Math.Induction.NatType
import Math.Induction.TypeMatch
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree 
import qualified Data.Map.Strict as Map

ctx0 :: InducTree (Tree.Tree Term)
ctx0 = intros Init [zero, one, two, nat]
