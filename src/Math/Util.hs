module Math.Util where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree 
import qualified Data.Map.Strict as Map

minByFunc :: (Ord b, Foldable f) => (a -> b) -> f a -> a
minByFunc f = foldr1 (minGo f) where
    minGo f l1 l2 | f l1 <= f l2 = l1
                  | otherwise = l2