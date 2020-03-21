{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module FormalTypes (
  module Math.Term,
  module Math.Util,
  module Math.Context,
  module Math.Former,
  module Math.Induction.Induction,
  module Math.Induction.TypeMatch,
  module Data.Set,
  module Data.Tree,
  ctx0,
) where

import Math.Term
import Math.Util
import Math.Context
import Math.Former
import Math.Induction.Induction
import Math.Induction.TypeMatch
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree 
import qualified Data.Map.Strict as Map

ctx0 :: Context (Tree.Tree Term)
ctx0 = intros Init []
