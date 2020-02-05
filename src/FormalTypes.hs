module FormalTypes (
  module Math.Term,
  module Math.Util,
  module Math.Induction,
  module Math.Induction.PiType,
  module Math.Induction.CoprodType, 
  module Math.Induction.NatType, 
  module Data.Set,
  module Data.Tree,
  typeTheory,
  ctx0,
  ctx1,
) where

import Math.Term
import Math.Util
import Math.Induction
import Math.Induction.PiType
import Math.Induction.CoprodType
import Math.Induction.NatType
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree 
import qualified Data.Map.Strict as Map

typeTheory :: InductionTree
typeTheory = insertAllMT emptyMT $ natExposedInductors ++ piExposedInductors

ctx0 :: Context
ctx0 = newTypes ctxEmp $ natExposedTypes ++ piExposedTypes

ctx1 :: Context
ctx1 = ctx0 <> Ctx Set.empty typeTheory