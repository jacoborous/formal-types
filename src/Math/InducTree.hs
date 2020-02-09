{-# LANGUAGE GADTs #-}

module Math.InducTree where

import Math.Term
import Math.Util
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree 
import qualified Data.Map.Strict as Map
import Control.Applicative
import Data.Maybe

data InducTree a where
    Init :: InducTree (Tree.Tree Term)
    TType :: Term -> InducTree Term
    Cntxt :: Tree.Tree Term -> InducTree (Tree.Tree Term)
    Roll :: Tree.Tree Term -> InducTree Term
    Unroll :: Term -> InducTree (Tree.Tree Term)
    Intro :: Term -> InducTree (Tree.Tree Term) -> InducTree (Tree.Tree Term)
    Merge :: InducTree (Tree.Tree Term) -> InducTree (Tree.Tree Term) -> InducTree (Tree.Tree Term)
    Reduce :: Either Term (Tree.Tree Term) -> InducTree (Tree.Tree Term)

instance Show a => Show (InducTree a) where
    show (TType t) = show t
    show Init = Tree.drawTree (fmap show (eval Init))
    show (Roll x) = show (eval $ Roll x)
    show (Unroll x) = Tree.drawTree (fmap show (eval $ Unroll x)) 
    show (Cntxt tree) = Tree.drawTree (fmap show tree)
    show (Intro t ctx) = Tree.drawTree (fmap show (eval (Intro t ctx))) 
    show (Merge a b) = Tree.drawTree (fmap show (eval (Merge a b)))
    show (Reduce x) = Tree.drawTree (fmap show (eval $ Reduce x))

instance (Eq a, Show a) => Ord (Tree.Tree a) where
    compare a b = compare (show a) (show b)

instance Eq a => Eq (InducTree a) where
    a == b = eval a == eval b

instance (Eq a, Show a) => Ord (InducTree a) where
    compare a b = compare (show a) (show b)

instance Semigroup Term where
    t1 <> t2 = roll $ merge (unroll t1) (unroll t2)

instance Monoid Term where
    mempty = U

eval :: InducTree a -> a
eval Init = Tree.Node U []
eval (TType t) = t
eval (Cntxt tree) = tree
eval (Roll t) = go t where
    go (Tree.Node x []) = x
    go (Tree.Node x xs) = Def x (fmap go xs)
eval (Unroll (Def f fs)) = Tree.Node f (fmap (eval . Unroll) fs)
eval (Unroll x) = Tree.Node x []
eval (Intro a b) = go a (eval b) where
    go (Def f fs) tree = mergeTrees (eval $ Unroll (Def f fs)) tree
    go t tree = mergeTrees (Tree.Node t []) tree
eval (Merge a b) = mergeTrees (eval a) (eval b)
eval (Reduce (Left a)) = eval $ Unroll a
eval (Reduce (Right b)) = b

roll :: Tree.Tree Term -> Term
roll tree = eval (Roll tree)

unroll :: Term -> Tree.Tree Term
unroll t = eval (Unroll t)

merge :: Tree.Tree Term -> Tree.Tree Term -> Tree.Tree Term
merge a b = eval (Merge (Cntxt a) (Cntxt b))

insert :: InducTree (Tree.Tree Term) -> [Term] -> InducTree (Tree.Tree Term)
insert tree [] = tree
insert tree (x:xs) = insert (Intro x tree) xs

mergeConcat :: [Tree.Tree Term] -> Tree.Tree Term
mergeConcat [] = eval Init
mergeConcat [x] = x
mergeConcat (x:xs) = mergeTrees x (mergeConcat xs)

unify :: Tree.Tree Term -> Tree.Tree Term
unify (Tree.Node a as) = Tree.Node a (go as) where
  go [] = []
  go xs = fmap unify (subunify xs)

subunify :: [Tree.Tree Term] -> [Tree.Tree Term]
subunify [] = []
subunify [x] = [x]
subunify (x:y:xs) = uniques $ (go x y) ++ subunify xs where
  go (Tree.Node a []) (Tree.Node b [])
     | relation a b == EQUIV = [Tree.Node a []]
     | relation a b == SUBTYPE = [Tree.Node b [Tree.Node a []]]
     | relation a b == SUPERTYPE = [Tree.Node a [Tree.Node b []]]
     | otherwise = [Tree.Node a [], Tree.Node b []]
  go (Tree.Node a as) (Tree.Node b [])
     | compare2 (Cntxt (Tree.Node a as)) a b == Just EQUIV || relation a b == EQUIV = [Tree.Node a as]
     | compare2 (Cntxt (Tree.Node a as)) a b == Just SUBTYPE || relation a b == SUBTYPE = [Tree.Node b [Tree.Node a as]]
     | compare2 (Cntxt (Tree.Node a as)) a b == Just SUPERTYPE || relation a b == SUPERTYPE = [Tree.Node a (Tree.Node b [] : as)]
     | otherwise = [Tree.Node a as, Tree.Node b []]
  go (Tree.Node a []) (Tree.Node b bs)
     | compare2 (Cntxt (Tree.Node b bs)) a b == Just EQUIV || relation a b == EQUIV = [Tree.Node b bs]
     | compare2 (Cntxt (Tree.Node b bs)) a b == Just SUBTYPE || relation a b == SUBTYPE = [Tree.Node b (Tree.Node a [] : bs)]
     | compare2 (Cntxt (Tree.Node b bs)) a b == Just SUPERTYPE || relation a b == SUPERTYPE = [Tree.Node a [Tree.Node b bs]]
     | otherwise = [Tree.Node a [], Tree.Node b bs]
  go (Tree.Node a as) (Tree.Node b bs)
     | compare2 (Cntxt (Tree.Node b bs)) a b == Just EQUIV || compare2 (Cntxt (Tree.Node a as)) a b == Just EQUIV || relation a b == EQUIV = [Tree.Node a (concatMap (uncurry go) (zip as bs))]
     | compare2 (Cntxt (Tree.Node b bs)) a b == Just SUBTYPE || compare2 (Cntxt (Tree.Node a as)) a b == Just SUBTYPE || relation a b == SUBTYPE = [Tree.Node b (concatMap (go (Tree.Node a as)) bs)]
     | compare2 (Cntxt (Tree.Node b bs)) a b == Just SUPERTYPE || compare2 (Cntxt (Tree.Node a as)) a b == Just SUPERTYPE || relation a b == SUPERTYPE = [Tree.Node a (concatMap (go (Tree.Node b bs)) as)]
     | otherwise = [Tree.Node a as, Tree.Node b bs]

mergeTrees :: Tree.Tree Term -> Tree.Tree Term -> Tree.Tree Term
mergeTrees (Tree.Node a as) (Tree.Node b bs) = unify $ go $ uniques $ subunify [Tree.Node a as, Tree.Node b bs] where
    go [t] = t
    go ts = Tree.Node U ts

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

relate :: InducTree (Tree.Tree Term) -> Term -> Tree.Tree (Term, TypeRel)
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
  go (x:xs) = if go [x] /= Nothing then go [x] else go xs