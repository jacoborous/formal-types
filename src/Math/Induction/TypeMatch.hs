{-# LANGUAGE GADTs #-}

module Math.Induction.TypeMatch where

import Math.Term
import Math.Context
import Math.Util
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree
import qualified Data.Map.Strict as Map
import Control.Applicative
import Data.Maybe

newtype Pattern = Pattern (Tree.Tree String)

instance Show Pattern where
  show (Pattern p) = Tree.drawTree p

pattern :: Term -> Pattern
pattern t = Pattern $ fmap show (toExpr t)

toExpr :: Term -> Tree.Tree Term
toExpr U = Tree.Node U []
toExpr (Prim p) = Tree.Node (Prim p) []
toExpr (Var x a) = Tree.Node (cnst "Var") [Tree.Node (cnst x) [], toExpr a]
toExpr (Lambda x a b) 
    |  Set.member (Var x a) (freeVars b) = Tree.Node (cnst "λ") [toExpr (Var x a), toExpr b]
    |  otherwise = Tree.Node (cnst "->") [toExpr a, toExpr b]
toExpr (Pair a b) = Tree.Node (cnst "Pair") [toExpr a, toExpr b]
toExpr (Coprod a b) = Tree.Node (cnst "Coprod") [toExpr a, toExpr b]
toExpr (Ap a b) = Tree.Node (cnst "Ap") [toExpr a, toExpr b]
toExpr (Ident a b) = Tree.Node (cnst "Ident") [toExpr a, toExpr b]
toExpr (DefEq a b) = Tree.Node (cnst "DefEq") [toExpr a, toExpr b]
toExpr (Pi (Var x a) b) 
    | Set.member (Var x a) (freeVars b) = Tree.Node (cnst "∏") [toExpr (Var x a), toExpr b]
    | otherwise = Tree.Node (cnst "->") [toExpr a, toExpr b]
toExpr (Pi a b) = Tree.Node (cnst "->") [toExpr a, toExpr b]
toExpr (Sigma (Var x a) b) 
    | Set.member (Var x a) (freeVars b) = Tree.Node (cnst "∑") [toExpr (Var x a), toExpr b]
    | otherwise = Tree.Node (cnst "Pair") [toExpr a, toExpr b]
toExpr (Sigma a b) = Tree.Node (cnst "Pair") [toExpr a, toExpr b]
toExpr (Inl a) = Tree.Node (cnst "Inl") [toExpr a]
toExpr (Inr a) = Tree.Node (cnst "Inr") [toExpr a]
toExpr (Def a bs) = Tree.Node (cnst "Inductive") [toExpr a, Tree.Node (cnst "Coprod") (fmap toExpr bs)]
toExpr (Match terms) = Tree.Node (cnst "Match") (fmap go terms) where
    go (a, b) = toExpr (Lambda wild a b)


shallowMatch :: Context (Tree.Tree Term) -> Term -> [Term]
shallowMatch ctx t = fmap roll (patternMatch t (eval ctx))

typeMatch :: Context (Tree.Tree Term) -> Term -> [Term]
typeMatch ctx t = go (relate ctx t) where
    go (Tree.Node (x, SUPERTYPE) xs) = [x]
    go (Tree.Node (x, r) []) = []
    go (Tree.Node (x, r) xs) = concatMap go xs

typeOf :: Context (Tree.Tree Term) -> Term -> [Term]
typeOf ctx t = go (relate ctx t) where
    go (Tree.Node (x, SUBTYPE) xs) = [x] ++ concatMap go xs
    go (Tree.Node (x, r) []) = []
    go (Tree.Node (x, r) xs) = concatMap go xs

patternMatch :: Term -> Tree.Tree Term -> [Tree.Tree Term]
patternMatch t tree = removeU $ go t tree where
    go :: Term -> Tree.Tree Term -> Tree.Tree Term
    go (Var x a) (Tree.Node y xs)
        | compare2 (Cntxt tree) a y == Just EQUIV = mergeConcat (xs >>= patternMatch (Var x a))
        | otherwise = mergeConcat (xs >>= patternMatch (Var x a))
    go t (Tree.Node x xs)
        | compare2 (Cntxt tree) t x == Just EQUIV = Tree.Node x xs
        | otherwise = mergeConcat (xs >>= patternMatch t)

matchPair :: Context (Tree.Tree Term) -> (Term -> Term -> Term) -> Term -> Term -> [Context (Tree.Tree Term)]
matchPair tree f a b = Cntxt <$> ([uncurry f (x, y) | x <- fmap (roll . eval) (match tree a), y <- fmap (roll . eval) (match tree b)] >>= (\x -> patternMatch x (eval tree)))

match :: Context (Tree.Tree Term) -> Term -> [Context (Tree.Tree Term)]
match tree (Pair x y) = matchPair tree Pair x y
match tree (Ap x y) = matchPair tree Ap x y
match tree (Coprod x y) = matchPair tree Coprod x y
match tree (Pi x y) = matchPair tree Pi x y
match tree (Sigma x y) = matchPair tree Sigma x y
match tree (Ident x y) = matchPair tree Ident x y
match tree (DefEq x y) = matchPair tree DefEq x y
match ctx t = Cntxt <$> patternMatch t (eval ctx)

removeU :: Tree.Tree Term -> [Tree.Tree Term]
removeU (Tree.Node U xs) = xs
removeU t = [t]

isType :: Context (Tree.Tree Term) -> Term -> Term -> Bool
isType ctx t u = go (match ctx t) (match ctx u) where
  go a b = or $ zipWith isSubTree' (fmap eval a) (fmap eval b)


-- compare e.g. (x * y + c) to ("A" * "A" + ?) ; will match only if x and y are equal.
-- procedure: traverse both expressions. if one is a var type, create a new set with its
-- identifier. Add the corresponding term from left expression. (Should behave like a Dict.)
-- If a var type with that identifier exists, add to the set. if the set ever goes beyond size 1,
-- the match should return false.
-- what about "A(X) and A(Y)" where A is a variable too?
matchVarTypes :: Tree.Tree Term -> Tree.Tree Term -> Bool
matchVarTypes (Tree.Node a xs) (Tree.Node b ys) = a == b && checkValid (traverse xs ys Map.empty) where
    traverse [] [] d = d
    traverse _ [] d = d
    traverse [] _ d = d
    traverse (x:xs) (y:ys) d = traverse xs ys (go x y d) where
        go x (Tree.Node (Var s t) zs) d = Map.insertWith Set.union (Var s t) (Set.singleton x) d
        go (Tree.Node s []) (Tree.Node u []) d = d
        go (Tree.Node s x) (Tree.Node r y) d = traverse x y d
    checkValid map
        | Map.size map == 0 = True
        | otherwise = Map.foldr f True map where
            f ts v = v && (Set.size ts == 1)

varToFunc :: Context (Tree.Tree Term) -> Term -> Term -> Bool
varToFunc ctx (Var t s) x = isType ctx x s


