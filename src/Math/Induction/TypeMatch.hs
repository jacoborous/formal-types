module Math.Induction.TypeMatch where

import Math.Term
import Math.Induction
import Math.InducTree
import Math.Util
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree 
import qualified Data.Map.Strict as Map
import Control.Applicative
import Data.Maybe

patternMatch :: Term -> Tree.Tree Term -> Tree.Tree Term
patternMatch = go where
    go t (Tree.Node x xs) 
        | relation t x == EQUIV = Tree.Node x xs  
        | relation t x == SUPERTYPE = Tree.Node x xs
        | otherwise = mergeConcat (fmap (patternMatch t) xs)