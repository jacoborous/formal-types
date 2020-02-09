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

patternMatch :: Term -> Tree.Tree Term -> [Tree.Tree Term]
--patternMatch (Ap x y) tree = fmap unroll (zipWith (\x -> \y -> Ap x y) (fmap roll (patternMatch x tree)) (fmap roll (patternMatch y tree)))
patternMatch t tree = removeU $ go (etaConvert t) tree where
    go :: Term -> Tree.Tree Term -> Tree.Tree Term
    go (Var x a) (Tree.Node y xs)
        | relation a y == EQUIV = mergeConcat (xs >>= (patternMatch (X x)))
        | otherwise = mergeConcat (xs >>= (patternMatch (Var x a)))
    go (X x) tree = tree
    go (Ap x (Var v a)) (Tree.Node (Ap c d) xs)
        | relation c x == EQUIV = mergeConcat (xs >>= (patternMatch (Var v a)))
        | otherwise = mergeConcat (xs >>= (patternMatch (Ap x (Var v a))))
    go t (Tree.Node x xs) 
        | relation t x == EQUIV = Tree.Node x xs
        | otherwise = mergeConcat (xs >>= (patternMatch t))

match :: InducTree (Tree.Tree Term) -> Term -> [InducTree (Tree.Tree Term)]
match ctx t = Cntxt <$> patternMatch t (eval ctx)

removeU :: Tree.Tree Term -> [Tree.Tree Term]
removeU (Tree.Node U xs) = xs
removeU t = [t]

isType :: InducTree (Tree.Tree Term) -> Term -> Term -> Bool
isType ctx t u = go (match ctx t) (match ctx u) where
  go a b = or $ zipWith (isSubTree') (fmap eval a) (fmap eval b)

{-relate :: InducTree (Tree.Tree Term) -> Term -> Tree.Tree (Term, TypeRel)
relate ctx t = go t SUBTYPE (eval ctx)  where
  go t d (Tree.Node x xs)
    | relation t x == EQUIV = Tree.Node (x, EQUIV) (fmap (go t SUPERTYPE) xs)
    | otherwise = Tree.Node (x, (go2 subtrees d)) subtrees where
      subtrees = (fmap (go t d) xs)
      go2 subtrees d = if or (fmap hasEquiv subtrees) then SUBTYPE else (if d == SUPERTYPE then SUPERTYPE else NOTEQ) where
        hasEquiv (Tree.Node (x, EQUIV) xs) = True
        hasEquiv (Tree.Node (x, r) []) = False
        hasEquiv (Tree.Node (x, r) xs) = or (fmap hasEquiv xs)

compare2 :: InducTree (Tree.Tree Term) -> Term -> Term -> Maybe TypeRel
compare2 ctx a b = go [relate ctx a] where
  go [] = Nothing
  go [Tree.Node (x, r) []] = if x == b then Just r else Nothing
  go [Tree.Node (x, r) xs] = if x == b then Just r else go xs
  go (x:xs) = if go [x] /= Nothing then go [x] else go xs-}


-- compare e.g. (x * y + c) to ("A" * "A" + ?) ; will match only if x and y are equal.
-- procedure: traverse both expressions. if one is a var type, create a new set with its
-- identifier. Add the corresponding term from left expression. (Should behave like a Dict.)
-- If a var type with that identifier exists, add to the set. if the set ever goes beyond size 1,
-- the match should return false.
-- what about "A(X) and A(Y)" where A is a variable too?
{-matchVarTypes :: [Term] -> [Term] -> Bool
matchVarTypes xs ys = checkValid (traverse xs ys Map.empty) where
    traverse [] [] d = d
    traverse _ [] d = d
    traverse [] _ d = d
    traverse (x:xs) (y:ys) d = traverse xs ys (go x y d) where
        go x (X s) d = Map.insertWith Set.union s (Set.singleton x) d
        go (Tree.Node s []) (Tree.Node u []) d = d
        go (Tree.Node s x) (Tree.Node r y) d = traverse x y d
    checkValid map
        | Map.size map == 0 = True
        | otherwise = Map.foldr f True map where
            f ts v = v && (Set.size ts == 1)-}
