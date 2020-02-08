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

instance Show a => Show (InducTree a) where
    show (TType t) = show t
    show Init = Tree.drawTree (fmap show (eval Init))
    show (Roll x) = show (eval $ Roll x)
    show (Unroll x) = Tree.drawTree (fmap show (eval $ Unroll x)) 
    show (Cntxt tree) = Tree.drawTree (fmap show tree)
    show (Intro t ctx) = Tree.drawTree (fmap show (eval (Intro t ctx))) 
    show (Merge a b) = Tree.drawTree (fmap show (eval (Merge a b)))

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

roll :: Tree.Tree Term -> Term
roll tree = eval (Roll tree)

unroll :: Term -> Tree.Tree Term
unroll t = eval (Unroll t)

merge :: Tree.Tree Term -> Tree.Tree Term -> Tree.Tree Term
merge a b = eval (Merge (Cntxt a) (Cntxt b))

mergeConcat :: [Tree.Tree Term] -> Tree.Tree Term
mergeConcat [] = eval Init
mergeConcat [x] = x
mergeConcat (x:xs) = mergeTrees x (mergeConcat xs)

mergeTrees :: Tree.Tree Term -> Tree.Tree Term -> Tree.Tree Term
mergeTrees (Tree.Node a as) (Tree.Node b bs) = go2 $ uniques $ go (Tree.Node a as) (Tree.Node b bs) where 
    go2 [t] = t
    go2 ts = Tree.Node U ts 
    go (Tree.Node a []) (Tree.Node b [])
        | relation a b == EQUIV = [Tree.Node a []]
        | relation a b == SUBTYPE = [Tree.Node b [Tree.Node a []]]
        | relation a b == SUPERTYPE = [Tree.Node a [Tree.Node b []]]
        | otherwise = [Tree.Node a [], Tree.Node b []] 
    go (Tree.Node a as) (Tree.Node b []) 
        | relation a b == EQUIV = [Tree.Node a as]
        | relation a b == SUBTYPE = [Tree.Node b [Tree.Node a as]]
        | relation a b == SUPERTYPE = [Tree.Node a (Tree.Node b [] : as)]
        | otherwise = [Tree.Node a as, Tree.Node b []] 
    go (Tree.Node a []) (Tree.Node b bs) 
        | relation a b == EQUIV = [Tree.Node b bs]
        | relation a b == SUBTYPE = [Tree.Node b (Tree.Node a [] : bs)]
        | relation a b == SUPERTYPE = [Tree.Node a [Tree.Node b bs]]
        | otherwise = [Tree.Node a as, Tree.Node b []] 
    go (Tree.Node a as) (Tree.Node b bs)
        | relation a b == EQUIV = [Tree.Node a (concatMap (uncurry go) (zip as bs))]
        | relation a b == SUBTYPE = [Tree.Node b (concatMap (go (Tree.Node a as)) bs)]
        | relation a b == SUPERTYPE = [Tree.Node a (concatMap (go (Tree.Node b bs)) as)]
        | otherwise = [Tree.Node a as, Tree.Node b bs]