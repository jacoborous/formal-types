{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

module Math.Context where

import Math.Term
import Math.Util
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree
import qualified Data.Map.Strict as Map
import Control.Applicative
import Data.Maybe

data Context a where
    Init :: Context (Tree.Tree Term)
    TType :: Term -> Context Term
    Cntxt :: Tree.Tree Term -> Context (Tree.Tree Term)
    Roll :: Tree.Tree Term -> Context Term
    Unroll :: Term -> Context (Tree.Tree Term)
    Intro :: Term -> Context (Tree.Tree Term) -> Context (Tree.Tree Term)
    Merge :: Context (Tree.Tree Term) -> Context (Tree.Tree Term) -> Context (Tree.Tree Term)
    Reduce :: Either Term (Tree.Tree Term) -> Context (Tree.Tree Term)
    Proof :: Term -> Context (Tree.Tree Term) -> Context (Tree.Tree Term)

showTree :: (Show a) => Tree.Tree a -> IO ()
showTree tree = putStrLn $ Tree.drawTree (fmap show tree)

instance Show a => Show (Context a) where
    show (TType t) = show t
    show Init = Tree.drawTree (fmap show (eval Init))
    show (Roll x) = show (eval $ Roll x)
    show (Unroll x) = Tree.drawTree (fmap show (eval $ Unroll x)) 
    show (Cntxt tree) = Tree.drawTree (fmap show tree)
    show (Intro t ctx) = Tree.drawTree (fmap show (eval (Intro t ctx))) 
    show (Merge a b) = Tree.drawTree (fmap show (eval (Merge a b)))
    show (Reduce x) = Tree.drawTree (fmap show (eval $ Reduce x))
    show (Proof t ctx) = Tree.drawTree (fmap show (eval (Proof t ctx)))

instance (Eq a, Show a) => Ord (Tree.Tree a) where
    compare a b = compare (show a) (show b)

instance Eq a => Eq (Context a) where
    a == b = eval a == eval b

instance (Eq a, Show a) => Ord (Context a) where
    compare a b = compare (show a) (show b)

instance Semigroup Term where
    t1 <> t2 = roll $ merge (unroll t1) (unroll t2)

instance Monoid Term where
    mempty = U

eval :: Context a -> a
eval Init = Tree.Node U []
eval (TType t) = t
eval (Cntxt tree) = tree
eval (Roll t) = go t where
    go (Tree.Node x []) = x
    go (Tree.Node x xs) = Def x (fmap go xs)
eval (Unroll x) = unfoldRec x
eval (Intro a b) = eval $ intro b a
eval (Merge a b) = mergeTrees (eval a) (eval b)
eval (Reduce (Left a)) = eval $ Unroll a
eval (Reduce (Right b)) = b

roll :: Tree.Tree Term -> Term
roll tree = eval (Roll tree)

unroll :: Term -> Tree.Tree Term
unroll t = eval (Unroll t)

extract1 :: Term -> Tree.Tree Term
extract1 (Def f fs) = Tree.Node f []
extract1 f = Tree.Node f []

unfoldRec :: Term -> Tree.Tree Term
unfoldRec (Def f fs) = Tree.Node f (go (Def f fs) fs) where
  go g gs = if g `elem` (gs ++ concatMap subterms gs) then fmap extract1 gs else fmap unfoldRec gs
unfoldRec t = Tree.Node t []

subterms :: Term -> [Term]
subterms t = uniques (go t) where
  go (Def f fs) = go f
  go (Ap a b) = go a ++ go b
  go (Pi a b) = go a ++ go b
  go (Sigma a b) = go a ++ go b
  go (Pair a b) = go a ++ go b
  go (Ident a b) = go a ++ go b
  go (DefEq a b) = go a ++ go b
  go (Coprod a b) = fmap Inl (go a) ++ fmap Inr (go b)
  go (Lambda a b) = go b
  go (Inl a) = go a
  go (Inr a) = go a
  go (Var s x) = go x
  go (X x) = []
  go x = [x]

merge :: Tree.Tree Term -> Tree.Tree Term -> Tree.Tree Term
merge a b = eval (Merge (Cntxt a) (Cntxt b))

intro :: Context (Tree.Tree Term) -> Term -> Context (Tree.Tree Term)
intro ctx t = if exists ctx t then ctx else Cntxt $ go t (eval ctx) (relate2 ctx t) where
  go :: Term -> Tree.Tree Term -> Tree.Tree (Term, TypeRel) -> Tree.Tree Term
  go x (Tree.Node t ts) (Tree.Node (s, r) xs) 
    | r == SUBTYPE && and (fmap noSubtypeBelow xs) = Tree.Node s (unroll x : fmap pullEm xs)
    | otherwise = Tree.Node s $ fmap (go x (Tree.Node t ts)) xs where
      pullEm :: Tree.Tree (Term, TypeRel) -> Tree.Tree Term
      pullEm (Tree.Node (s, r) xs) = Tree.Node s (fmap pullEm xs)
      noSubtypeBelow :: Tree.Tree (Term, TypeRel) -> Bool
      noSubtypeBelow (Tree.Node (s, r) []) = r /= SUBTYPE
      noSubtypeBelow (Tree.Node (s, r) xs) = (r /= SUBTYPE) && and (fmap noSubtypeBelow xs) 

intros :: Context (Tree.Tree Term) -> [Term] -> Context (Tree.Tree Term)
intros tree [] = tree
intros tree xs = foldl intro tree xs

mergeConcat :: [Tree.Tree Term] -> Tree.Tree Term
mergeConcat [] = eval Init
mergeConcat [x] = x
mergeConcat (x:xs) = mergeTrees x (mergeConcat xs)

clean :: Context (Tree.Tree Term) -> Context (Tree.Tree Term)
clean ctx = Cntxt ((unify . eval) ctx)

unify :: Tree.Tree Term -> Tree.Tree Term
unify (Tree.Node a as) = Tree.Node a (go as) where
  go [] = []
  go xs = fmap unify (subunify (Cntxt $ Tree.Node a as) xs)

subunify :: Context (Tree.Tree Term) -> [Tree.Tree Term] -> [Tree.Tree Term]
subunify ctx xs = subunify' ctx (uniques xs) where
  subunify' ctx [] = []
  subunify' ctx [x] = [x]
  subunify' ctx (x:y:xs) = go x y ++ subunify' ctx xs where
    go (Tree.Node a []) (Tree.Node b [])
       | compare2 ctx a b == Just EQUIV || relation a b == EQUIV = [Tree.Node a []]
       | compare2 ctx a b == Just SUBTYPE || relation a b == SUBTYPE = [Tree.Node b [Tree.Node a []]]
       | compare2 ctx a b == Just SUPERTYPE || relation a b == SUPERTYPE = [Tree.Node a [Tree.Node b []]]
       | otherwise = [Tree.Node a [], Tree.Node b []]
    go (Tree.Node a as) (Tree.Node b [])
       | compare2 ctx a b == Just EQUIV || relation a b == EQUIV = [Tree.Node a (subunify' ctx as)]
       | compare2 ctx a b == Just SUBTYPE || relation a b == SUBTYPE = [Tree.Node b [Tree.Node a (subunify' ctx as)]]
       | compare2 ctx a b == Just SUPERTYPE || relation a b == SUPERTYPE = [Tree.Node a (Tree.Node b [] : subunify' ctx as)]
       | otherwise = [Tree.Node a (subunify' ctx as), Tree.Node b []]
    go (Tree.Node a []) (Tree.Node b bs)
       | compare2 ctx a b == Just EQUIV || relation a b == EQUIV = [Tree.Node b (subunify' ctx bs)]
       | compare2 ctx a b == Just SUBTYPE || relation a b == SUBTYPE = [Tree.Node b (Tree.Node a [] : subunify' ctx bs)]
       | compare2 ctx a b == Just SUPERTYPE || relation a b == SUPERTYPE = [Tree.Node a [Tree.Node b (subunify' ctx bs)]]
       | otherwise = [Tree.Node a [], Tree.Node b (subunify' ctx bs)]
    go (Tree.Node a as) (Tree.Node b bs)
       | compare2 ctx a b == Just EQUIV || relation a b == EQUIV = [Tree.Node a (subunify' ctx (as ++ bs))]
       | compare2 ctx a b == Just SUBTYPE || relation a b == SUBTYPE = [Tree.Node b (concatMap (go (Tree.Node a (subunify' ctx as))) (subunify' ctx bs))]
       | compare2 ctx a b == Just SUPERTYPE || relation a b == SUPERTYPE = [Tree.Node a (concatMap (go (Tree.Node b (subunify' ctx bs))) (subunify' ctx as))]
       | otherwise = [Tree.Node a (subunify' ctx as), Tree.Node b (subunify' ctx bs)]

mergeTrees :: Tree.Tree Term -> Tree.Tree Term -> Tree.Tree Term
mergeTrees (Tree.Node a as) (Tree.Node b bs) = unify $ go $ uniques $ subunify (Cntxt $ Tree.Node a as) $ subunify (Cntxt $ Tree.Node b bs) [Tree.Node a as, Tree.Node b bs] where
    go [t] = t
    go ts = Tree.Node U ts

exists' :: Context (Tree.Tree Term) -> Term -> Bool
exists' ctx t = isSubTree (unroll t) (eval ctx)

exists :: Context (Tree.Tree Term) -> Term -> Bool
exists ctx t = go t (eval ctx) where
    go t (Tree.Node u []) = t == u
    go t (Tree.Node u xs) = if t == u then True else or (fmap (go t) xs)

isTrue :: Context (Tree.Tree Term) -> Term -> Bool
isTrue ctx t = go t (eval ctx) where
    go t (Tree.Node u []) = False
    go t (Tree.Node u xs) = if t == u then True else or (fmap (go t) xs)

isSubTree :: Tree.Tree Term -> Tree.Tree Term -> Bool
isSubTree t1 t2
  | t1 == t2 = True
  | otherwise = go t1 t2 where
    go t1 (Tree.Node x xs) = or (fmap (isSubTree t1) xs)

isSubTree' :: Tree.Tree Term -> Tree.Tree Term -> Bool
isSubTree' t1 t2
  | t1 == t2 = False
  | otherwise = go t1 t2 where
    go t1 (Tree.Node x xs) = or (fmap (isSubTree t1) xs)

relate2 :: Context (Tree.Tree Term) -> Term -> Tree.Tree (Term, TypeRel)
relate2 ctx t = go (fmap (\x -> (x, fromMaybe (relation t x) (compare2 ctx t x))) (eval ctx))  where
  go :: Tree.Tree (Term, TypeRel) -> Tree.Tree (Term, TypeRel)
  go (Tree.Node (x, EQUIV) xs) = Tree.Node (x, EQUIV) (go2 xs) where
    go2 :: [Tree.Tree (Term, TypeRel)] -> [Tree.Tree (Term, TypeRel)]
    go2 [] = []
    go2 [Tree.Node (x, r) xs] = [Tree.Node (x, SUPERTYPE) (go2 xs)]
    go2 (x:xs) = go2 [x] ++ go2 xs
  go (Tree.Node (x, NOTEQ) xs) = if go2 xs then Tree.Node (x, SUBTYPE) (fmap go xs) else Tree.Node (x, NOTEQ) (fmap go xs) where
    go2 :: [Tree.Tree (Term, TypeRel)] -> Bool
    go2 [] = False
    go2 [Tree.Node (x, EQUIV) xs] = True
    go2 [Tree.Node (x, SUBTYPE) xs] = True
    go2 [x] = False
    go2 (x:xs) = go2 [x] || go2 xs
  go (Tree.Node (x, r) xs) = Tree.Node (x, r) (fmap go xs)

relate :: Context (Tree.Tree Term) -> Term -> Tree.Tree (Term, TypeRel)
relate ctx t = go (fmap (\x -> (x, relation t x)) (eval ctx))  where
  go :: Tree.Tree (Term, TypeRel) -> Tree.Tree (Term, TypeRel)
  go (Tree.Node (x, EQUIV) xs) = Tree.Node (x, EQUIV) (go2 xs) where
    go2 :: [Tree.Tree (Term, TypeRel)] -> [Tree.Tree (Term, TypeRel)]
    go2 [] = []
    go2 [Tree.Node (x, r) xs] = [Tree.Node (x, SUPERTYPE) (go2 xs)]
    go2 (x:xs) = go2 [x] ++ go2 xs
  go (Tree.Node (x, NOTEQ) xs) = if go2 xs then Tree.Node (x, SUBTYPE) (fmap go xs) else Tree.Node (x, NOTEQ) (fmap go xs) where
    go2 :: [Tree.Tree (Term, TypeRel)] -> Bool
    go2 [] = False
    go2 [Tree.Node (x, EQUIV) xs] = True
    go2 [Tree.Node (x, SUBTYPE) xs] = True
    go2 [x] = False
    go2 (x:xs) = go2 [x] || go2 xs
  go (Tree.Node (x, r) xs) = Tree.Node (x, r) (fmap go xs)


compare2 :: Context (Tree.Tree Term) -> Term -> Term -> Maybe TypeRel
compare2 ctx (Def f cs) (Def g ds)
  | compare2 ctx f g == Just NOTEQ = go $ fmap (compare2 ctx (Def f cs)) ds
  | otherwise = compare2 ctx f g where
      go y
          | or (fmap (== Just EQUIV) y) = Just SUBTYPE
          | or (fmap (== Just SUBTYPE) y) = Just SUBTYPE
          | otherwise = go $ fmap (compare2 ctx (Def g ds)) cs where
              go y
                  | or (fmap (== Just EQUIV) y) = Just SUPERTYPE
                  | or (fmap (== Just SUBTYPE) y) = Just SUPERTYPE
                  | otherwise = Just NOTEQ
compare2 ctx (Def f cs) x
  | compare2 ctx f x == Just NOTEQ = go $ fmap (compare2 ctx x) cs
  | otherwise = compare2 ctx f x where
      go y
          | or (fmap (== Just EQUIV) y) = Just SUPERTYPE
          | or (fmap (== Just SUBTYPE) y) = Just SUPERTYPE
          | otherwise = Just NOTEQ
compare2 ctx x (Def f cs)
  | compare2 ctx x f == Just NOTEQ = go $ fmap (compare2 ctx x) cs
  | otherwise = compare2 ctx x f where
      go y
          | or (fmap (== Just EQUIV) y) = Just SUBTYPE
          | or (fmap (== Just SUBTYPE) y) = Just SUBTYPE
          | otherwise = Just NOTEQ
compare2 ctx (Lambda s x) (Lambda t y) = go (alphaReduce (Lambda s x)) (alphaReduce (Lambda t y)) where
  go (Lambda a b) (Lambda c d) = compare2 ctx b d
compare2 ctx (Pi a b) (Lambda s x) = compare2 ctx (alphaReduce $ Pi a b) (alphaReduce $ Pi (X s) x)
compare2 ctx (Lambda s x) (Pi a b) = compare2 ctx (alphaReduce $ Pi (X s) x) (alphaReduce $ Pi a b)
compare2 ctx (Pi a b) (Pi c d) = go (alphaReduce (Pi a b)) (alphaReduce (Pi c d)) where
  go (Pi x y) (Pi z w) = compare2 ctx (Ap x y) (Ap z w)
compare2 ctx (Ap a b) (Ap c d) = go (compare2 ctx a c) (compare2 ctx b d) where
  go Nothing _ = Nothing
  go _ Nothing = Nothing
  go (Just EQUIV) (Just SUBTYPE) = Just SUBTYPE
  go (Just EQUIV) (Just EQUIV) = Just EQUIV
  go (Just EQUIV) (Just SUPERTYPE) = Just SUPERTYPE
  go _ _ = Just NOTEQ
compare2 ctx (Pair a b) (Pair c d) = go (compare2 ctx a c) (compare2 ctx b d) where
  go Nothing _ = Nothing
  go _ Nothing = Nothing
  go (Just SUBTYPE) (Just SUBTYPE) = Just SUBTYPE
  go (Just EQUIV) (Just EQUIV) = Just EQUIV
  go (Just SUPERTYPE) (Just SUPERTYPE) = Just SUPERTYPE
  go _ _ = Just NOTEQ
compare2 ctx a (Var s t) = compare2 ctx a t
compare2 ctx (Var s t) a = compare2 ctx t a
compare2 ctx a b
  | exists ctx a = go b (relate ctx a)
  | exists ctx b = flip $ go a (relate ctx b)
  | otherwise = Nothing where
    go t (Tree.Node (x, r) xs) = if t == x then Just r else go2 t xs where
      go2 t [] = Nothing
      go2 t (x:xs) = if isNothing (go t x) then go2 t xs else go t x
    flip (Just SUPERTYPE) = Just SUBTYPE
    flip (Just SUBTYPE) = Just SUPERTYPE
    flip x = x