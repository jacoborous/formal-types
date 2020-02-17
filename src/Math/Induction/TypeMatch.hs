{-# LANGUAGE GADTs #-}

module Math.Induction.TypeMatch where

import Math.Term
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
patternMatch t tree = removeU $ go (etaConvert t) tree where
    go :: Term -> Tree.Tree Term -> Tree.Tree Term
    go (Var x a) (Tree.Node y xs)
        | compare2 (Cntxt tree) a y == Just EQUIV = mergeConcat (xs >>= (patternMatch (X x)))
        | otherwise = mergeConcat (xs >>= (patternMatch (Var x a)))
    go (X x) tree = tree
    go t (Tree.Node x xs) 
        | compare2 (Cntxt tree) t x == Just EQUIV = Tree.Node x xs
        | otherwise = mergeConcat (xs >>= (patternMatch t))


matchPair :: InducTree (Tree.Tree Term) -> (Term -> Term -> Term) -> Term -> Term -> [InducTree (Tree.Tree Term)]
matchPair tree f a b = Cntxt <$> ([(uncurry f) (x, y) | x <- fmap (roll . eval) (match tree a), y <- fmap (roll . eval) (match tree b)] >>= (\x -> patternMatch x (eval tree)))

match :: InducTree (Tree.Tree Term) -> Term -> [InducTree (Tree.Tree Term)]
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

isType :: InducTree (Tree.Tree Term) -> Term -> Term -> Bool
isType ctx t u = go (match ctx t) (match ctx u) where
  go a b = or $ zipWith (isSubTree') (fmap eval a) (fmap eval b)

-- compare e.g. (x * y + c) to ("A" * "A" + ?) ; will match only if x and y are equal.
-- procedure: traverse both expressions. if one is a var type, create a new set with its
-- identifier. Add the corresponding term from left expression. (Should behave like a Dict.)
-- If a var type with that identifier exists, add to the set. if the set ever goes beyond size 1,
-- the match should return false.
-- what about "A(X) and A(Y)" where A is a variable too?
matchVarTypes :: Tree.Tree Term -> Tree.Tree Term -> Bool
matchVarTypes (Tree.Node a xs) (Tree.Node b ys) = if a == b then checkValid (traverse xs ys Map.empty) else False where
    traverse [] [] d = d
    traverse _ [] d = d
    traverse [] _ d = d
    traverse (x:xs) (y:ys) d = traverse xs ys (go x y d) where
        go x (Tree.Node (Var s t) zs) d = Map.insertWith Set.union (Var s t) (Set.singleton x) d
        go x (Tree.Node (X s) zs) d = Map.insertWith Set.union (X s) (Set.singleton x) d
        go (Tree.Node s []) (Tree.Node u []) d = d
        go (Tree.Node s x) (Tree.Node r y) d = traverse x y d
    checkValid map
        | Map.size map == 0 = True
        | otherwise = Map.foldr f True map where
            f ts v = v && (Set.size ts == 1)

typeFormerTree :: Term -> Tree.Tree Term
typeFormerTree (X x) = Tree.Node (X x) []
typeFormerTree (Var x s) = Tree.Node (Var x s) []
typeFormerTree (Prim p) = Tree.Node (Prim p) []
typeFormerTree (Lambda s t) = Tree.Node (Lambda s t) [typeFormerTree (X s), typeFormerTree t]
typeFormerTree (Pi a b) = Tree.Node (Pi a b) [typeFormerTree a, typeFormerTree b]
typeFormerTree (Sigma a b) = Tree.Node (Sigma a b) [typeFormerTree a, typeFormerTree b]
typeFormerTree (Pair a b) = Tree.Node (Pair a b) [typeFormerTree a, typeFormerTree b]
typeFormerTree (Coprod a b) = Tree.Node (Coprod a b) [typeFormerTree a, typeFormerTree b]
typeFormerTree (Ap a b) = Tree.Node (Ap a b) [typeFormerTree a, typeFormerTree b]
typeFormerTree (Ident a b) = Tree.Node (Ident a b) [typeFormerTree a, typeFormerTree b]
typeFormerTree (DefEq a b) = Tree.Node (DefEq a b) [typeFormerTree a, typeFormerTree b]
typeFormerTree (Inl a) = Tree.Node (Inl a) [typeFormerTree a]
typeFormerTree (Inr a) = Tree.Node (Inr a) [typeFormerTree a]

varToFunc :: InducTree (Tree.Tree Term) -> Term -> Term -> Bool
varToFunc ctx (Var t s) = \ x -> isType ctx x s 

{- data Constructor a where
    C :: String -> [Constructor Term] -> Constructor Term
    Set :: Term -> Term -> Constructor Term
    Variable :: String -> Term -> Constructor Term
    AppR :: Term -> Constructor (Term -> Term)
    AppL :: Term -> Constructor (Term -> Term)
    Function :: Term -> Term -> Constructor Term
    Family :: String -> Term -> Constructor Term
    ForAll :: String -> Term -> Term -> Constructor Term
    ThereExists :: String -> Term -> Term -> Constructor Term
    Bind :: Term -> Term -> Term -> Constructor Term
    Subst :: Term -> Term -> Term -> Constructor Term
    Define :: Term -> Term -> Constructor (Term -> Term)
    Identity :: Term -> Constructor (Term -> Term)

form :: Constructor a -> a
form (C s xs) = foldl (.$) (cnst s) (fmap form xs)
form (Set a b) = Def b [a]
form (Variable s t) = Var s t
form (Function a b) = Pi a b
form (Family x b) = Lambda x (Ap b (X x))
form (ForAll x a b) = Pi (Var x a) (Ap b (X x))
form (ThereExists x a b) = Pair a (beta $ (form $ ForAll x a b) .$ a) --elim
form (Bind (X x) a b) 
    | Set.member (X x) (freeVars b) = if a == U then Lambda x b else Pi (Var x a) b
    | Set.member (X x) (boundVars b) = error $ "Variable " ++ show (X x) ++ " already bound in " ++ show b 
    | otherwise = b
form (Subst e r m) = substitution m e r
form (Define f d) = \ x -> form (Subst x d f)
form (Identity (Ident a b)) = form $ Define a b
form (AppR t) = \ x -> Ap t x
form (AppL t) = \ x -> Ap x t

instance Show a => Show (Constructor a) where
    show a = show $ form a -}