{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

module Math.Term where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree 
import qualified Data.Map.Strict as Map
import Control.Applicative
import Data.Semigroup
import Data.List
import Math.Util

data Term = U | X String | Lambda String Term | Var String Term
    | Ap Term Term | Pair Term Term | Coprod Term Term | Inl Term | Inr Term
    | Pi Term Term | Sigma Term Term | Ident Term Term | DefEq Term Term 
    | Prim PrimConst | Def Term [Term]

data PrimConst = DefConst String 
    | Zero | One | Two 
    | Prjl | Prjr 
    | DefType | Func | Refl 
    | Nat deriving (Ord, Eq)

data Inductor = Inductor Term (Term -> Term)

instance Show Inductor where
    show (Inductor m f) = show m ++ " -> " ++ show (f m)

instance Eq Inductor where
    (==) (Inductor m f) (Inductor n g) = (m, f m) == (n, g n)

instance Ord Inductor where
    compare (Inductor m f) (Inductor n g) = compare (m, f m) (n, g n)

indPattern :: Inductor -> Term
indPattern (Inductor m f) = m

indMorph :: Inductor -> Term -> Term
indMorph (Inductor m f) = f

instance Show PrimConst where
    show Zero = "⟘"
    show One = "⟙"
    show Two = "𝟐"
    show Prjl = "prjl"
    show Prjr = "prjr"
    show DefType = ":"
    show Refl = "refl"
    show Nat = "𝐍"
    show (DefConst s) = s

instance Show Term where
    show U = "𝓤"
    show (X s) = s
    show (Var s t) = "(" ++ s ++ " : " ++ show t ++ ")"
    show (Lambda s t) = "λ" ++ s ++ "." ++ show t
    show (Pair a b) = "(" ++ show a ++ " , " ++ show b ++ ")"
    show (Coprod a b) = "(" ++ show a ++ " + " ++ show b ++ ")"
    show (Inl a) = "Inl " ++ show a
    show (Inr a) = "Inr " ++ show a
    show (DefEq a b) = "(" ++ show a ++ " ≡ " ++ show b ++ ")"
    show (Ap (Ap (Prim DefType) a) b) = "(" ++ show a ++ " " ++ show DefType ++ " " ++ show b ++ ")"
    show (Ident a b) = "(" ++ show a ++ " = " ++ show b ++ ")"
    show (Ap t u) = show t ++ " " ++ show u
    show (Pi t u)
      | Set.disjoint (freeVars t) (freeVars u) = show t ++ " -> " ++ show u
      | otherwise = "∏(" ++ show t ++ ")(" ++ show u ++ ")"
    show (Sigma t u) = "∑(" ++ show t ++ ")(" ++ show u ++ ")"
    show (Prim p) = show p
    show (Def s cs) = show s

instance Eq Term where
    (X x) == (X y)
        | x == wild = True
        | y == wild = True
        | otherwise = x == y
    (X x) == (Var s t) = x == s && t == U
    (Var s t) == (X x) = x == s && t == U
    (Var s t) == (Var u v) = s == u && t == v
    (Def x cs) == (Def y ds) = x == y
    (Prim p) == (Prim q) = p == q
    (Inl p) == (Inl q) = p == q
    (Inr p) == (Inr q) = p == q
    U == U = True
    (Lambda s t) == (Lambda r u) = go (alphaReduce (Lambda s t)) (alphaReduce (Lambda r u)) where
        go (Lambda s t) (Lambda r u) = t == u
        go a b = error $ show a ++ " and " ++ show b
    (Ap a b) == (Ap c d) = a == c && b == d
    (Sigma a b) == (Sigma c d) = a == c && b == d
    (Pi a b) == (Pi c d) = a == c && b == d
    (Ident a b) == (Ident c d) = a == c && b == d
    (DefEq a b) == (DefEq c d) = a == c && b == d
    (Coprod a b) == (Coprod c d) = a == c && b == d
    (Pair a b) == (Pair c d) = a == c && b == d
    x == (Def y ds) = x == y
    (Def x cs) == y = x == y
    x == y = False

data TypeRel = EQUIV | SUBTYPE | SUPERTYPE | NOTEQ deriving (Eq, Show)

instance Ord TypeRel where
    compare EQUIV EQUIV = EQ
    compare EQUIV SUBTYPE = GT
    compare EQUIV SUPERTYPE = LT
    compare EQUIV NOTEQ = LT
    compare SUBTYPE SUBTYPE = EQ
    compare SUBTYPE SUPERTYPE = LT
    compare SUBTYPE NOTEQ = LT
    compare SUPERTYPE SUPERTYPE = EQ
    compare SUPERTYPE NOTEQ = LT
    compare NOTEQ NOTEQ = EQ
    compare SUBTYPE EQUIV  = LT
    compare SUPERTYPE EQUIV  = GT
    compare NOTEQ EQUIV = GT
    compare SUPERTYPE SUBTYPE = GT
    compare NOTEQ SUBTYPE = GT
    compare NOTEQ SUPERTYPE = GT

relation :: Term -> Term -> TypeRel
relation a b = if a == b then EQUIV else goRelation (alphaReduce a) (alphaReduce b) where
    goRelation U U = EQUIV
    goRelation x U = SUBTYPE
    goRelation U x = SUPERTYPE
    goRelation (Def f cs) (Def g ds)  
        | goRelation f g == NOTEQ = go $ fmap (relation (Def f cs)) ds 
        | otherwise = goRelation f g where
            go y 
                | or (fmap (== EQUIV) y) = SUBTYPE
                | or (fmap (== SUBTYPE) y) = SUBTYPE
                | otherwise = go $ fmap (relation (Def g ds)) cs where
                    go y 
                        | or (fmap (== EQUIV) y) = SUPERTYPE
                        | or (fmap (== SUBTYPE) y) = SUPERTYPE
                        | otherwise = NOTEQ
    goRelation x (Def f cs) 
        | goRelation x f == NOTEQ = go $ fmap (relation x) cs 
        | otherwise = goRelation x f where
            go y 
                | or (fmap (== EQUIV) y) = SUBTYPE
                | or (fmap (== SUBTYPE) y) = SUBTYPE
                | otherwise = NOTEQ
    goRelation (Def f cs) x 
        | goRelation f x == NOTEQ = go $ fmap (relation x) cs 
        | otherwise = goRelation f x where
            go y 
                | or (fmap (== EQUIV) y) = SUPERTYPE
                | or (fmap (== SUBTYPE) y) = SUPERTYPE
                | otherwise = NOTEQ
    goRelation (X x) (X y)
        | x == wild || y == wild = EQUIV
        | x == y = EQUIV
        | otherwise = NOTEQ
    goRelation (X x) y = SUPERTYPE
    goRelation y (X x) = SUBTYPE
    goRelation (Var s t) (Var u v)
        | relation t v == EQUIV = if s == u then EQUIV else NOTEQ
        | otherwise = NOTEQ
    goRelation x (Var s t) = relation x t
    goRelation (Var s t) x = relation t x
    goRelation (Lambda s t) (Lambda x b) = go2 (alphaReduce (Lambda s t)) (alphaReduce (Lambda x b)) where
        go2 (Lambda i j) (Lambda k l) = goRelation j l
    goRelation (Lambda s t) (Pi (X x) b) = relation (Lambda s t) (Lambda x b)
    goRelation (Pi (X x) b) (Lambda s t) = relation (Lambda x b) (Lambda s t)
    goRelation (Pi a b) (Pi c d) = goRelation (Ap a b) (Ap c d)
    goRelation a (Sigma b c) = go (goRelation a b) (goRelation a c) where
        go x EQUIV = SUBTYPE
        go _ _ = NOTEQ
    goRelation (Coprod a b) (Coprod c d) = goRelation (Pair a b) (Pair c d)
    goRelation (Inl x) (Coprod a b) = go $ goRelation x a where
        go EQUIV = NOTEQ
        go SUBTYPE = SUBTYPE
        go SUPERTYPE = NOTEQ
        go NOTEQ = NOTEQ
    goRelation (Inr x) (Coprod a b) = go $ goRelation x b where
        go EQUIV = NOTEQ
        go SUBTYPE = SUBTYPE
        go SUPERTYPE = NOTEQ
        go NOTEQ = NOTEQ
    goRelation (Pair a b) (Pair c d) = go (goRelation a c) (goRelation b d) where
        go EQUIV EQUIV = EQUIV
        go SUBTYPE SUBTYPE = SUBTYPE
        go SUPERTYPE SUPERTYPE = SUPERTYPE
        go x y = NOTEQ
    goRelation (Ap t u) (Ap v w) = go (goRelation t v) (goRelation u w) where
        go EQUIV EQUIV = EQUIV
        go SUBTYPE EQUIV = SUBTYPE
        go EQUIV SUBTYPE = SUBTYPE
        go SUBTYPE SUBTYPE = SUBTYPE
        go EQUIV SUPERTYPE = SUPERTYPE
        go SUPERTYPE EQUIV = SUPERTYPE
        go SUPERTYPE SUPERTYPE = SUPERTYPE
        go x y = NOTEQ
    goRelation (DefEq a b) (Ident c d) = if (relation a c == EQUIV) && (relation b d == EQUIV) then SUBTYPE else NOTEQ
    goRelation (Ident c d) (DefEq a b) = if (relation a c == EQUIV) && (relation b d == EQUIV) then SUPERTYPE else NOTEQ
    goRelation (Prim p) (Prim q)
        | p == q = EQUIV
        | otherwise = NOTEQ
    goRelation (Prim p) y = NOTEQ
    goRelation y (Prim p) = NOTEQ
    goRelation x y = NOTEQ

depth :: Term -> Int
depth U = 0
depth (X s) = 1
depth (Var s t) = 1 + depth t
depth (Def f cs) = depth f
depth (Lambda s t) = 1 + depth t 
depth (Ap t u) = 2 + depth t + depth u
depth (Pair t u) = 2 + depth t + depth u
depth (Coprod t u) = 2 + depth t + depth u
depth (Sigma t u) = 2 + depth t + depth u
depth (Pi t u) = 2 + depth t + depth u
depth (Prim p) = 2
depth (Inl t) = 1 + depth t
depth (Inr t) = 1 + depth t
depth (Ident t u) = 2 + depth t + depth u
depth (DefEq t u) = 2 + depth t + depth u

instance Ord Term where
    compare x y 
        | relation x y == EQUIV = EQ
        | relation x y == SUBTYPE = LT
        | otherwise = GT

indX :: Int -> Term
indX n = X $ "𝑥" ++ subscript n

subscript :: Int -> String
subscript i 
    | i >= 0 && i < 10 = ["₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉"] !! i
    | otherwise = concatMap subscript (splitInt i) where
        splitInt n 
            | n `div` 10 == 0 = [n]
            | otherwise = splitInt (n `div` 10) ++ [n `mod` 10]

etaConvert :: Term -> Term
etaConvert t = go t (Set.toList $ freeVars t) 0 where
    go t [] n = t
    go t [X x] n = pureSub (X x) t (indX n)
    go t (X x : xs) n = go (pureSub (X x) t (indX n)) xs (n+1)

alphaReduce :: Term -> Term
alphaReduce t = go t (Set.toList $ boundVars t) 0 where
    go t [] n = t
    go t [X x] n = pureSub (X x) t (indX n)
    go t (X x : xs) n = go (pureSub (X x) t (indX n)) xs (n+1)
    go t [Var x a] n = pureSub (Var x a) t (indX n) where
    go t ((Var x a) : xs) n = go (pureSub (Var x a) t (indX n)) xs (n+1)

beta :: Term -> Term
beta (Ap (Pi (Var x a) m) n)
    | Set.disjoint (freeVars n) (boundVars m) = substitution (X x) m n
    | otherwise = Ap (Pi (Var x a) m) n
beta (Ap (Pi (X x) m) n) = beta (Ap (Lambda x m) n)
beta (Ap (Lambda x m) n) 
    | Set.disjoint (freeVars n) (boundVars m) = substitution (X x) m n
    | otherwise = Ap (Lambda x m) n
beta x = error (show x)

pureSub :: Term -> Term -> Term -> Term
pureSub v m n = if v == m then n else go v m where
    go v (Pi a b) = Pi (pureSub v a n) (pureSub v b n)
    go v (Sigma a b) = Sigma (pureSub v a n) (pureSub v b n)
    go v (Ap a b) = Ap (pureSub v a n) (pureSub v b n)
    go v (Pair a b) = Pair (pureSub v a n) (pureSub v b n)
    go v (Coprod a b) = Coprod (pureSub v a n) (pureSub v b n)
    go v (Ident a b) = Ident (pureSub v a n) (pureSub v b n)
    go v (DefEq a b) = DefEq (pureSub v a n) (pureSub v b n)
    go v (Def f cs) = Def (pureSub v f n) (fmap (\ x -> pureSub v x n) cs)
    go v (Inl a) = Inl (pureSub v a n)
    go v (Inr a) = Inr (pureSub v a n)
    go v (Var s a) = Var s (pureSub v a n)
    go (X x) (Lambda s t)
        | x == s = bind n (go (X x) t)
        | otherwise = Lambda s (go (X x) t)
    go v m = m

substitution :: Term -> Term -> Term -> Term
substitution v m n = if relation v m == EQUIV then n else go v m where
    go v (Pi a b)
        | relation v a == EQUIV = Pi a b
        | otherwise = Pi a (substitution v b n)
    go v (Sigma a b)
        | relation v a == EQUIV = Sigma a b
        | otherwise = Sigma a (substitution v b n)
    go v (Ap a b) = Ap (substitution v a n) (substitution v b n)
    go v (Pair a b) = Pair (substitution v a n) (substitution v b n)
    go v (Coprod a b) = Coprod (substitution v a n) (substitution v b n)
    go v (Inl a) = Inl (substitution v a n)
    go v (Inr a) = Inr (substitution v a n)
    go v (Ident a b) = Ident (substitution v a n) (substitution v b n)
    go v (DefEq a b) = DefEq (substitution v a n) (substitution v b n)
    go v (Def f cs) = Def (substitution v f n) (fmap (\ x -> substitution v x n) cs)
    go (X x) (Lambda s t) 
        | x == s = Lambda s t
        | otherwise = Lambda s (go (X x) t)
    go v m = m

freeVars :: Term -> Set.Set Term
freeVars (X s) = Set.singleton (X s)
freeVars (Var x a) = Set.singleton (Var x a)
freeVars (Def f cd) = freeVars f
freeVars (Lambda s t) = Set.delete (X s) (freeVars t)
freeVars (Pi (Var x a) u) = Set.delete (Var x a) (freeVars u)
freeVars (Sigma (Var x a) u) = Set.delete (Var x a) (freeVars u)
freeVars (Ap t u) = Set.union (freeVars t) (freeVars u)
freeVars (Pair t u) = Set.union (freeVars t) (freeVars u)
freeVars (Coprod t u) = Set.union (freeVars t) (freeVars u)
freeVars (Inl t) = freeVars t
freeVars (Inr t) = freeVars t
freeVars (Ident t u) = Set.union (freeVars t) (freeVars u)
freeVars (DefEq t u) = Set.union (freeVars t) (freeVars u)
freeVars _ = Set.empty

boundVars :: Term -> Set.Set Term
boundVars (X s) = Set.empty
boundVars (Var x a) = Set.empty
boundVars (Def f cd) = boundVars f
boundVars (Lambda s t) = Set.union (Set.singleton (X s)) (boundVars t)
boundVars (Pi (Var s t) u) = Set.union (Set.singleton (Var s t)) (boundVars u)
boundVars (Sigma (Var s t) u) = Set.union (Set.singleton (Var s t)) (boundVars u)
boundVars (Ap t u) = Set.union (boundVars t) (boundVars u)
boundVars (Pair t u) = Set.union (boundVars t) (boundVars u)
boundVars (Coprod t u) = Set.union (boundVars t) (boundVars u)
boundVars (Inl t) = boundVars t
boundVars (Inr t) = boundVars t
boundVars (Ident t u) = Set.union (boundVars t) (boundVars u)
boundVars (DefEq t u) = Set.union (boundVars t) (boundVars u)
boundVars _ = Set.empty

bindFree :: Term -> Term
bindFree expr = go (Set.toList $ freeVars expr) expr where
  go [] f = f
  go (x:xs) f = go xs (bind x f)

arity :: Term -> [Term]
arity (X s) = []
arity (Var x a) = []
arity (Def f cd) = arity f
arity (Lambda s t) = (X s) : (arity t)
arity (Pi (Var s t) u) = (Var s t) : (arity u)
arity (Sigma (Var s t) u) = (Var s t) : (arity u)
arity (Ap t u) = (arity t) ++ (arity u)
arity (Pair t u) = (arity t) ++ (arity u)
arity (Coprod t u) = (arity t) ++ (arity u)
arity (Inl t) = arity t
arity (Inr t) = arity t
arity (Ident t u) = (arity t) ++ (arity u)
arity (DefEq t u) = (arity t) ++ (arity u)
arity _ = []

bind :: Term -> Term -> Term
bind (X x) expr 
    | Set.member (X x) (freeVars expr) = Lambda x expr
    | Set.member (X x) (boundVars expr) = expr
    | otherwise = Lambda x expr
bind (Var x a) expr
    | Set.member (X x) (freeVars expr) = Pi (Var x a) expr
    | Set.member (X x) (boundVars expr) = expr
    | otherwise = Pi (Var x a) expr

(|->) :: Term -> Term -> Term
t |-> expr = bind t expr

infixl 9 .$
infixr 0 .=, .:, ~=

(.$) :: Term -> Term -> Term
t .$ u = Ap t u

(.=) :: Term -> Term -> Term
x .= y = DefEq x y

(~=) :: Term -> Term -> Term
x ~= y = Ident x y

(.:) :: Term -> Term -> Term
(X x) .: t = Var x t
a .: b = Def b [a]

prjl :: Term -> Term
prjl = Ap (Prim Prjl)

prjr :: Term -> Term
prjr = Ap (Prim Prjr)

unary :: PrimConst -> Term -> Term
unary p = Ap (Prim p)

binary :: PrimConst -> Term -> Term -> Term
binary p x y = Prim p .$ x .$ y

nary :: PrimConst -> [Term] -> Term
nary p [] = Prim p
nary p xs = Prim p .$ go xs where
    go [x] = x
    go (x:xs) = x .$ go xs 

processList :: [a -> a] -> a -> a
processList fs a = foldl (\ a f -> f a) a fs  
 
toIdInd :: Term -> Inductor
toIdInd (Pi a b) 
    | a == b = Inductor a id
    | otherwise = Inductor (Pi a b) id 
toIdInd t = Inductor t id --id

uniquejoin :: Ord a => [a] -> [a]
uniquejoin x = Set.toList $ Set.fromList x

setconcat :: Ord a => [a] -> [a] -> [a]
setconcat x y = Set.toList $ Set.union (Set.fromList x) (Set.fromList y)

getDefSubs :: Term -> [Term]
getDefSubs (Def f cs) = cs

cnst :: String -> Term
cnst s = Prim $ DefConst s

wild = "𝑥"
wildcard = X wild

inType :: Term -> Term -> Term
inType x a = Def a [x]

inU :: Term -> Term
inU x = inType x U

xInType :: String -> String -> Term
xInType s t = inType (X s) (cnst t)

typesIn :: [Term] -> Term -> Term
typesIn xs a = Def a xs

xsInType :: [String] -> String -> Term
xsInType xs a = Def (cnst a) (go xs) where
  go = map X

assocLaw0 :: Inductor
assocLaw0 = Inductor (Pair (Pair U U) U) (\ (Pair (Pair a b) c) -> Pair a (Pair b c))

assocLaw1 :: Inductor
assocLaw1 = Inductor (Pair U (Pair U U)) (\ (Pair a (Pair b c)) -> Pair (Pair a b) c)

reflectLaw :: Inductor
reflectLaw = Inductor (DefEq U U) (\(DefEq a b) -> DefEq b a)

anyInhabOf :: Term -> Term
anyInhabOf = Ap (Ap (Prim DefType) wildcard)

equivType :: Term
equivType = Ident U U

identityFunctorLaw1 :: Inductor
identityFunctorLaw1 = Inductor (Ap U (Ident U U)) (\ (Ap a (Ident b c)) -> Ident (a .$ b) (a .$ c) )

identityFunctorLaw2 :: Inductor
identityFunctorLaw2 = Inductor (Ap (Ident U U) U) (\ (Ap (Ident a b) c) -> Ident (a .$ c) (b .$ c) )

alpha :: Term -> Term -> Term
alpha v t = bind v $ beta $ t .$ v

typeTree :: Term -> Tree.Tree Term
typeTree (Def t cs) = Tree.Node t (fmap typeTree cs)
typeTree t = Tree.Node t []

treeType :: Tree.Tree Term -> Term
treeType (Tree.Node t []) = t
treeType (Tree.Node t cs) = Def t (fmap treeType cs)

expr :: Int -> Term -> Term
expr 0 t = bind (indX 0) (t .$ indX 0)
expr n t = bind (indX n) (expr (n - 1) t .$ indX n)