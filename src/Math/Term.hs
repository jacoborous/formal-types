{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

module Math.Term where

import Data.Set (Set)
import Data.Semigroup
import Data.List
import Data.Tree (Tree)
import qualified Data.Tree as Tree 
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Control.Applicative

data Term = U | X String | Lambda String Term 
    | Ap Term Term | Pair Term Term | Coprod Term Term 
    | Pi Term Term | Sigma Term Term | Ident Term Term
    | Prim PrimConst | Def Term [Term]

data PrimConst = DefConst String 
    | Zero | One | Two 
    | Inl | Inr | Prjl | Prjr 
    | DefType | DefEq | Func | Refl 
    | Nat deriving (Ord, Eq)

data Inductor = Inductor Term (Term -> Term)

instance Show Inductor where
    show (Inductor m f) = show m ++ " ≃ " ++ show (f m)

instance Eq Inductor where
    (==) (Inductor m f) (Inductor n g) = (m, f m) == (n, g n)

instance Ord Inductor where
    compare (Inductor m f) (Inductor n g) = compare (m, f m) (n, g n)

indPattern :: Inductor -> Term
indPattern (Inductor m f) = m

indMorph :: Inductor -> Term -> Term
indMorph (Inductor m f) = f

indToFunc :: Inductor -> Term
indToFunc (Inductor m f) = Ap (Ap (Prim Func) m) (f m)

funcToInd :: Term -> Inductor
funcToInd (Ap (Ap (Prim Func) m) g) = Inductor m (const g)

instance Show PrimConst where
    show Zero = "⟘"
    show One = "⟙"
    show Two = "𝟐"
    show Inl = "inl"
    show Inr = "inr"
    show Prjl = "prjl"
    show Prjr = "prjr"
    show DefType = ":"
    show DefEq = "≡"
    show Func = "->"
    show Refl = "refl"
    show Nat = "𝐍"
    show (DefConst s) = s

instance Show Term where
    show U = "𝓤"
    show (X s) = s
    show (Lambda s t) = "λ" ++ s ++ "." ++ show t
    show (Pair a b) = "(" ++ show a ++ " , " ++ show b ++ ")"
    show (Coprod a b) = "(" ++ show a ++ " + " ++ show b ++ ")"
    show (Ap (Ap (Prim DefEq) a) b) = "(" ++ show a ++ " " ++ show DefEq ++ " " ++ show b ++ ")"
    show (Ap (Ap (Prim DefType) a) b) = "(" ++ show a ++ " " ++ show DefType ++ " " ++ show b ++ ")"
    show (Ident a b) = "(" ++ show a ++ " = " ++ show b ++ ")"
    show (Ap (Ap (Prim Func) a) b) = "(" ++ show a ++ " " ++ show Func ++ " " ++ show b ++ ")"
    show (Ap t u) = "(" ++ show t ++ " " ++ show u ++ ")"
    show (Pi t u) = "∏(" ++ show t ++ ")(" ++ show u ++ ")"
    show (Sigma t u) = "∑(" ++ show t ++ ")(" ++ show u ++ ")"
    show (Prim p) = show p 
    show (Def s cs) = showDef (Def s cs) 1 where
        showDef (Def f cs) 0 = showDef f 0
        showDef (Ap (Ap (Prim DefEq) t) u) 0 = "(" ++ (showDef t 0 ) ++ " " ++ show DefEq ++ " " ++ (showDef u 0 ) ++ ")"
        showDef (Ap (Ap (Prim DefType) t) u) 0 = "(" ++ (showDef t 0 ) ++ " " ++ show DefType ++ " " ++ (showDef u 0 ) ++ ")"
        showDef (Ap (Ap (Prim Func) t) u) 0 = "(" ++ (showDef t 0 ) ++ " " ++ show Func ++ " " ++ (showDef u 0 ) ++ ")"
        showDef (Sigma t u) 0 = "∑(" ++ (showDef t 0 ) ++ ")(" ++ (showDef u 0 ) ++ ")"
        showDef (Pi t u) 0 = "∏(" ++ (showDef t 0 ) ++ ")(" ++ (showDef u 0 ) ++ ")"
        showDef (Ident t u) 0 = "(" ++ (showDef t 0 ) ++ " = " ++ (showDef u 0 ) ++ ")"
        showDef (Coprod t u) 0 = "(" ++ (showDef t 0 ) ++ " + " ++ (showDef u 0 ) ++ ")"
        showDef (Pair t u) 0 = "(" ++ (showDef t 0 ) ++ " , " ++ (showDef u 0 ) ++ ")"
        showDef (Ap t u) 0 = "(" ++ (showDef t 0 ) ++ " " ++ (showDef u 0 ) ++ ")"
        showDef (Lambda s u) 0 = "λ" ++ s ++ "." ++ (showDef u 0 )
        showDef (X s) 0 = s
        showDef (Prim p) 0 = show p
        showDef U 0 = show U
        showDef (Def f []) 1 = showDef f 0 
        showDef (Def f cs) 1 = "([" ++ concat (intersperse "," (fmap (\ x -> showDef x 0) cs)) ++ "] : " ++ showDef f 0 ++ ")"

instance Eq Term where
    (X x) == (X y)
        | x == wild = True
        | y == wild = True
        | otherwise = x == y 
    (Def x cs) == (Def y ds) = x == y
    (Prim p) == (Prim q) = p == q
    U == U = True
    (Lambda s t) == (Lambda r u) = go (alphaReduce (Lambda s t)) (alphaReduce (Lambda r u)) where
        go (Lambda s t) (Lambda r u) = t == u   
    (Ap a b) == (Ap c d) = a == c && b == d
    (Sigma a b) == (Sigma c d) = a == c && b == d
    (Pi a b) == (Pi c d) = a == c && b == d
    (Ident a b) == (Ident c d) = a == c && b == d
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
        | x == y = EQUIV
        | otherwise = NOTEQ
    goRelation (X x) y = NOTEQ
    goRelation y (X x) = NOTEQ  
    goRelation (Prim p) (Prim q) 
        | p == q = EQUIV
        | otherwise = NOTEQ
    goRelation (Prim p) y = NOTEQ
    goRelation y (Prim p) = NOTEQ
    goRelation (Ident a b) (Ident c d) = goRelation (Pair a b) (Pair c d)
    goRelation (Ident a b) x = NOTEQ
    goRelation x (Ident a b) = NOTEQ
    goRelation (Lambda s t) (Lambda x b) = if s == x then goRelation t b else NOTEQ
    goRelation (Lambda s t) (Pi (X x) b) = if s == x then goRelation t b else NOTEQ
    goRelation (Pi (X x) b) (Lambda s t) = if s == x then goRelation b t else NOTEQ
    goRelation (Lambda s t) y = NOTEQ
    goRelation y (Lambda s t) = NOTEQ 
    goRelation (Pi a b) (Pi c d) = go (goRelation a c) (goRelation b d) where
        go EQUIV x = x
        go _ _ = NOTEQ
    goRelation (Pair a b) (Sigma c d) = goRelation (Pair a b) (Pair c d)
    goRelation (Sigma a b) (Pair c d) = goRelation (Pair a b) (Pair c d)
    goRelation (Sigma a b) (Sigma c d) = go (goRelation a c) (goRelation b d) where
        go EQUIV x = x
        go _ _ = NOTEQ
    goRelation (Coprod a b) (Coprod c d) = goRelation (Pair a b) (Pair c d)
    goRelation (Ap (Prim Inl) x) (Coprod a b) = go $ goRelation x a where
        go EQUIV = NOTEQ
        go SUBTYPE = SUBTYPE
        go SUPERTYPE = NOTEQ
        go NOTEQ = NOTEQ
    goRelation (Ap (Prim Inr) x) (Coprod a b) = go $ goRelation x b where
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
        go EQUIV x = x
        go x y = NOTEQ
    goRelation x y = NOTEQ

depth :: Term -> Int
depth U = 0
depth (X s) = 1 
depth (Def f cs) = depth f
depth (Lambda s t) = 1 + depth t 
depth (Ap t u) = 2 + depth t + depth u
depth (Pair t u) = 2 + depth t + depth u
depth (Coprod t u) = 2 + depth t + depth u
depth (Sigma t u) = 2 + depth t + depth u
depth (Pi t u) = 2 + depth t + depth u
depth (Prim p) = 2

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

alphaReduce :: Term -> Term
alphaReduce t = go t (Set.toList $ boundVars t) 0 where
    go t [] n = t
    go t [x] n = pureSub x t (indX n)
    go t (x:xs) n = go (pureSub x t (indX n)) xs (n+1) 

beta :: Term -> Term
beta (Ap (Lambda x m) n) 
    | Set.disjoint (freeVars n) (boundVars m) = substitution (X x) m n
    | otherwise = Ap (Lambda x m) n

pureSub :: Term -> Term -> Term -> Term
pureSub v m n = if v == m then n else go v m where
    go v (Pi a b) = Pi (pureSub v a n) (pureSub v b n)
    go v (Sigma a b) = Sigma (pureSub v a n) (pureSub v b n)
    go v (Ap a b) = Ap (pureSub v a n) (pureSub v b n)
    go v (Pair a b) = Pair (pureSub v a n) (pureSub v b n)
    go v (Coprod a b) = Coprod (pureSub v a n) (pureSub v b n)
    go v (Ident a b) = Ident (pureSub v a n) (pureSub v b n)
    go v (Def f cs) = Def (pureSub v f n) (fmap (\ x -> pureSub v x n) cs)
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
    go v (Ident a b) = Ident (substitution v a n) (substitution v b n)
    go v (Def f cs) = Def (substitution v f n) (fmap (\ x -> substitution v x n) cs)
    go (X x) (Lambda s t) 
        | x == s = Lambda s t
        | otherwise = Lambda s (go (X x) t) 
    go v m = m

freeVars :: Term -> Set.Set Term
freeVars (X s) = Set.singleton (X s)
freeVars (Def f cs) = freeVars f
freeVars (Lambda s t) = Set.delete (X s) (freeVars t)
freeVars (Pi t u) = freeVars u Set.\\ freeVars t
freeVars (Sigma t u) = freeVars u Set.\\ freeVars t
freeVars (Ap t u) = Set.union (freeVars t) (freeVars u)
freeVars (Pair t u) = Set.union (freeVars t) (freeVars u)
freeVars (Coprod t u) = Set.union (freeVars t) (freeVars u)
freeVars (Ident t u) = Set.union (freeVars t) (freeVars u)
freeVars _ = Set.empty

boundVars :: Term -> Set.Set Term
boundVars (X s) = Set.empty
boundVars (Def f cs) = boundVars f
boundVars (Lambda s t) = Set.union (Set.singleton (X s)) (boundVars t)
boundVars (Pi t u) = Set.union (freeVars t) (boundVars u)
boundVars (Sigma t u) = Set.union (freeVars t) (boundVars u)
boundVars (Ap t u) = Set.union (boundVars t) (boundVars u)
boundVars (Pair t u) = Set.union (boundVars t) (boundVars u)
boundVars (Coprod t u) = Set.union (boundVars t) (boundVars u)
boundVars (Ident t u) = Set.union (boundVars t) (boundVars u)
boundVars _ = Set.empty

bind :: Term -> Term -> Term
bind (X x) expr 
    | Set.member (X x) (freeVars expr) = Lambda x expr
    | Set.member (X x) (boundVars expr) = expr
    | otherwise = Lambda x expr
bind t expr
    | Set.disjoint (boundVars t) (freeVars expr) = Pi t expr
    | otherwise = expr

(|->) :: Term -> Term -> Term
t |-> expr = bind t expr

infixl 9 .$
infixr 0 .=, .:, -->

(.$) :: Term -> Term -> Term
t .$ u = Ap t u

(-->) :: Term -> Term -> Term
x --> y = binary Func x y

(.=) :: Term -> Term -> Term
x .= y = binary DefEq x y

(.:) :: Term -> Term -> Term
a .: b = Ap (Ap (Prim DefType) a) b

refl :: Term -> Term
refl = unary Refl

inl :: Term -> Term
inl = unary Inl

inr :: Term -> Term
inr = unary Inr

prjl :: Term -> Term
prjl = Ap (Prim Prjl)

prjr :: Term -> Term
prjr = Ap (Prim Prjr)

prjMatchL :: Term
prjMatchL = Ap (Prim Prjl) (Pair U U)

prjMatchR :: Term
prjMatchR = Ap (Prim Prjr) (Pair U U)

prjMatchLComp :: Term -> Term
prjMatchLComp (Ap (Prim Prjl) (Pair a b)) = a

prjMatchRComp :: Term -> Term
prjMatchRComp (Ap (Prim Prjr) (Pair a b)) = b

prjLInd :: Inductor
prjLInd = Inductor prjMatchL prjMatchLComp

prjRInd :: Inductor
prjRInd = Inductor prjMatchR prjMatchRComp

reflElim :: Inductor
reflElim = Inductor (Ap (Prim Refl) U) (\ (Ap (Prim Refl) x) -> Ident (x) x)

unary :: PrimConst -> Term -> Term
unary p = Ap (Prim p)

binary :: PrimConst -> Term -> Term -> Term
binary p x y = (Prim p) .$ x .$ y

nary :: PrimConst -> [Term] -> Term
nary p [] = (Prim p)
nary p xs = (Prim p) .$ (go xs) where
    go [x] = x
    go (x:xs) = x .$ (go xs) 

instance Semigroup Term where
    x <> y = Pair x y

instance Monoid Term where
    mempty = U

data InductionTree = Null | Node [Term -> Term] Term InductionTree InductionTree

indToTree :: InductionTree -> Tree.Tree Term
indToTree tree = (go tree) !! 0 where
    go Null = []
    go (Node [] t l r) = uniquesTree $ [Tree.Node t (go l)] ++ go r
    go (Node f t l r) = uniquesTree $ [Tree.Node (go2 t) (go l)] ++ go r where
        go2 t = go3 (fmap (\ x -> (x t)) f) where
            go3 [m] = if t == m then t else Ident t m
            go3 (m:ms) = if ((go3 ms) == (Ident t m)) then (Ident t m) else Pair (go3 ms) (Ident t m)

uniquesTree :: [Tree.Tree Term] -> [Tree.Tree Term]
uniquesTree [] = []
uniquesTree (x:xs) = if elem x xs then xs else x : uniquesTree xs

instance Show InductionTree where
    show tree = Tree.drawTree  $ fmap show $ indToTree tree
    {- show tree = showFunc tree 0 where
        showFunc Null d = ""
        showFunc (Node fs m l r) d = replicate d ' ' ++ go m fs ++ "\n" ++ showFunc l (d + 3) ++ showFunc r d where
            go m fs = show $ Set.fromList $ fmap (Inductor m) fs -}

inductors :: InductionTree -> [Inductor]
inductors = go [] where
    go ls Null = ls
    go ls (Node m t l r) = go ls l ++ go ls r ++ fmap (Inductor t) m

showMatches :: Term -> Context -> Set.Set Term
showMatches t (Ctx ts intree) = go Set.empty t intree where
    go ls tt Null = ls
    go ls tt (Node fs m l r) | tt <= m = Set.union (Set.fromList $ fmap (\ x -> Ident (tt) (x tt)) fs) (Set.union (go ls tt l) (go ls tt r))
                             | otherwise = Set.union (go ls tt l) (go ls tt r)

applyMatches :: Term -> Context -> Set.Set Term
applyMatches t (Ctx ts intree) = go Set.empty t intree where
    go ls tt Null = ls
    go ls tt (Node fs m l r) | tt <= m = Set.union (Set.fromList $ fmap (\ x -> x tt) fs) (Set.union (go ls tt l) (go ls tt r))
                             | otherwise = Set.union (go ls tt l) (go ls tt r)

getRelations :: Term -> Context -> Set.Set (Term, TypeRel)
getRelations t (Ctx ts intree) = go Set.empty t intree where
    go ls tt Null = ls
    go ls tt (Node fs m l r) = Set.union (Set.singleton (m, relation tt m)) (Set.union (go ls tt l) (go ls tt r))

getRelated :: TypeRel -> Term -> Context -> Set.Set Term
getRelated rel t (Ctx ts intree) = go Set.empty t intree where
    go ls tt Null = ls
    go ls tt (Node fs m l r) | rel == relation tt m = Set.union (Set.singleton m) (Set.union (go ls tt l) (go ls tt r))
                             | otherwise = Set.union (go ls tt l) (go ls tt r)

subtypes :: Context -> Term -> Set.Set Term
subtypes ctx t = getRelated SUPERTYPE t ctx

supertypes :: Context -> Term -> Set.Set Term
supertypes ctx t = getRelated SUBTYPE t ctx

equivs :: Context -> Term -> Set.Set Term
equivs ctx t = getRelated EQUIV t ctx

emptyMT :: InductionTree
emptyMT = Node [id] U Null Null

processList :: [a -> a] -> a -> a
processList fs a = foldl (\ a f -> f a) a fs  
 
toIdInd :: Term -> Inductor
toIdInd t = Inductor t id

uniquejoin :: Ord a => [a] -> [a]
uniquejoin x = Set.toList $ Set.fromList x

setconcat :: Ord a => [a] -> [a] -> [a]
setconcat x y = Set.toList $ Set.union (Set.fromList x) (Set.fromList y)

getDefSubs :: Term -> [Term]
getDefSubs (Def f cs) = cs

insertMT :: InductionTree -> Inductor -> InductionTree
insertMT tree ind = go tree (indPattern ind) (indMorph ind) where
    go Null (Def tt cs) m = Node [m] (Def tt cs) (insertAllMT Null (fmap toIdInd cs)) Null
    go Null tt m = Node [m] tt Null Null
    go (Node ms (Def t ds) l r) (Def tt cs) m 
        | relation tt t == EQUIV = Node (m : ms) (Def t (setconcat cs ds)) (insertAllMT l (fmap toIdInd cs)) r
        | relation tt t == SUBTYPE = Node ms (Def t ds) (go l (Def tt cs) m) r
        | relation tt t == SUPERTYPE = go2 (Node ms (Def t ds) l r) cs 
        | otherwise = Node ms (Def t ds) l (go r (Def tt cs) m) where
            go2 node typs = Node [m] (Def tt cs) (insertAllMT node (fmap toIdInd cs)) Null
    go (Node ms t l r) (Def tt cs) m 
        | relation (Def tt cs) t == EQUIV = Node (m : ms) (Def tt cs) (insertAllMT l (fmap toIdInd cs)) r
        | relation (Def tt cs) t == SUBTYPE = Node ms t (go l (Def tt cs) m) r
        | relation (Def tt cs) t == SUPERTYPE = go2 (Node ms t l r) cs 
        | otherwise = Node ms t l (go r (Def tt cs) m) where
            go2 node typs = Node [m] (Def tt cs) (insertAllMT node (fmap toIdInd cs)) Null
    go (Node ms t l r) tt m 
        | relation tt t == EQUIV = Node (m : ms) t l r
        | relation tt t == SUBTYPE = Node ms t (go l tt m) r
        | relation tt t == SUPERTYPE = Node [m] tt (Node ms t l r) Null
        | otherwise = Node ms t l (go r tt m)

insertAllMT :: InductionTree -> [Inductor] -> InductionTree
insertAllMT tree [] = tree
insertAllMT tree (p:ps) = insertAllMT nexttree ps where 
    nexttree = insertMT tree p  

data Context = Ctx (Set.Set Term) InductionTree

isMemberOf :: Term -> InductionTree -> Bool
isMemberOf t Null = False
isMemberOf t (Node ms tt l r) 
    | t == tt = True
    | otherwise = isMemberOf t l || isMemberOf t r

instance Show Context where
    show (Ctx types intree) = "context: \n" ++ show intree ++ "given types: \n" ++ show (insertAllMT emptyMT $ fmap toIdInd (Set.toList types)) 

instance Semigroup InductionTree where
    ind1 <> ind2 = go emptyMT (Set.toList (Set.fromList ((inductors ind1) ++ (inductors ind2)))) where
        go ind [] = ind
        go ind [x] 
            | isMemberOf (indPattern x) ind = ind
            | otherwise = insertMT ind x
        go ind (x:xs) = go (go ind [x]) xs where

instance Semigroup Context where
    ctx1 <> ctx2 = go ctx1 ctx2 where
        go (Ctx ms it1) (Ctx ns it2) = Ctx (Set.union ms ns) (it1 <> it2)

instance Monoid Context where
    mempty = ctxEmp

pathInduction :: Context -> Term -> Set.Set Term
pathInduction ctx (Ap t1 t2) = Set.union (showMatches (Ap t1 t2) ctx) (Set.fromList [Ap x y | x <- Set.toList $ pathInduction ctx t1, y <- Set.toList $ pathInduction ctx t2])
pathInduction ctx term = Set.insert term (showMatches term ctx)

derive :: Context -> Context
derive ctx = applyMorphs $ applyDefs ctx --applyDefs $ applyMorphs ctx

applyMorphs :: Context -> Context
applyMorphs (Ctx types intree) = go (Set.toList types) where
    go [t] = Ctx (pathInduction (Ctx types intree) t) intree
    go (t:ts) = go [t] <> go ts

applyDefs :: Context -> Context
applyDefs (Ctx types intree) = go (Set.toList types) where
    go [t] = newType t (Ctx types intree)
    go (t:ts) = newType t (go ts)
    
newIdents :: Context -> Set.Set Term
newIdents (Ctx typset intree) = go (Set.toList typset) where
    go = foldr (Set.union . pathInduction (Ctx typset intree)) Set.empty

intro :: Context -> Term -> Context
intro (Ctx s it) t = newType t (Ctx (Set.insert t s) it)

intros :: Context -> [Term] -> Context
intros ctx [t] = intro ctx t
intros ctx (t:ts) = intros (intro ctx t) ts

inductionTree :: [Inductor] -> InductionTree
inductionTree [] = emptyMT
inductionTree ms = insertAllMT emptyMT ms

introRules :: [Inductor] -> Context -> Context
introRules [] ctx = ctx
introRules ms (Ctx set tree) = Ctx set (insertAllMT tree ms) 

newType :: Term -> Context -> Context
newType (Def s cs) (Ctx set tree) = Ctx set (insertMT tree (toIdInd (Def s cs)))
newType (Ap (Ap (Prim DefType) a) b) ctx = newType newT ctx where
    newT = Def b [a]
newType (Ap (Ap (Prim DefEq) x) y) ctx = newType (Def (Ident x y) [(Ap (Ap (Prim DefEq) x) y)]) ctx <> newType x ctx <> newType y ctx
newType x (Ctx set tree) = Ctx set (insertMT tree (toIdInd x))

addTypes :: Context -> [Term] -> Context
addTypes = intros

newTypes :: Context -> [Term] -> Context
newTypes ctx [t] = newType t ctx
newTypes ctx (t:ts) = newTypes (newType t ctx) ts

equivdef :: Term -> Term -> Inductor
equivdef input t = Inductor input (const t)

induct :: Inductor -> Term -> Maybe Term
induct (Inductor m f) t 
    | relation t m == SUBTYPE = Just (f t)
    | relation t m == EQUIV = Just (f t)
    | otherwise = Nothing

search :: Context -> Set.Set Term -> Set.Set (Set.Set Term)
search ctx patterns = go (Set.toList patterns) where
    go [] = Set.empty
    go (x:xs) = Set.insert (getRelated EQUIV x ctx) (go xs) 

piForm :: Set.Set Term
piForm = Set.fromList [inType (X "A") U, Lambda "x" U] -- two terms, a type, and a lambda. The type refers to the type of the variable bound to the lambda expression.

defConst :: String -> Term
defConst s = Prim $ DefConst s

inhabOne = defConst "⋆"

wild = "𝑥"
wildcard = X wild

funcComp :: Term -> Term
funcComp (Ap (Ap (Ap (Prim Func) a) b) c) 
    | a == c = b
    | otherwise = Ap (Ap (Ap (Prim Func) a) b) c

funcElim :: Inductor
funcElim = Inductor (Ap (Ap (Ap (Prim Func) U) U) U) funcComp

typeReduce :: Term -> Term
typeReduce (Ap (Ap (Prim DefType) a) b) 
    | relation a b == SUBTYPE = one
    | otherwise = Def b [a]
typeReduce els = error $ "unrecognized: " ++ show els

inType :: Term -> Term -> Term
inType x a = Def a [x]

inU :: Term -> Term
inU x = inType x U

xInType :: String -> Term -> Term
xInType s = inType (X s)

xInU :: String -> Term
xInU s = xInType s U

typeInductor :: Inductor
typeInductor = Inductor (Ap (Ap (Prim DefType) U) U) typeReduce

assocLaw0 :: Inductor
assocLaw0 = Inductor (Ap (Ap U U) U) (\ (Ap (Ap a b) c) -> Ap a (Ap b c))

assocLaw1 :: Inductor
assocLaw1 = Inductor (Ap U (Ap U U)) (\ (Ap a (Ap b c)) -> Ap (Ap a b) c)

reflectLaw :: Inductor
reflectLaw = Inductor (Ident U U) (\(Ident a b) -> Ident b a)

anyInhabOf :: Term -> Term
anyInhabOf = Ap (Ap (Prim DefType) wildcard)

anyCoprod :: Term
anyCoprod = Coprod U U

coprodType :: Term
coprodType = Def anyCoprod [Ap (Prim Inl) (inType (indX 0) (X "A")), Ap (Prim Inr) (inType (indX 1) (X "B"))]

funcType :: Term
funcType = Ap (Ap (Prim Func) U) U

lambdaType :: Term
lambdaType = Lambda wild U

lambdaInductor :: Inductor 
lambdaInductor = Inductor (Ap lambdaType U) beta

piType :: Term
piType = Def (Pi U U) [lambdaType, funcType]

piInductorUniq :: Inductor
piInductorUniq = Inductor (Ap (Pi (xInU wild) U) (xInU wild)) (\ (Ap (Pi a f ) b) -> if a == b then f else (Ap (Pi a f ) b))

piInductor1 :: Inductor
piInductor1 = Inductor lambdaType (\ (Lambda a b) -> Pi (X a) b)

piInductor2 :: Inductor
piInductor2 = Inductor (Ap (Pi wildcard U) wildcard) (\ (Ap (Pi (X a) b) c) -> Ap (Lambda a b) c)

piPairComp :: Term -> Term
piPairComp (Pi (Pair x y) (Lambda wild c)) = Pi x (Pi y g) where 
    g = substitution wildcard c (Pair x y) 

piInductor3 :: Inductor
piInductor3 = Inductor (Pi (Pair U U) (Lambda wild U)) piPairComp  

piCoprodComp :: Term -> Term
piCoprodComp (Pi (Coprod x y) (Pair g0 g1)) = Coprod (Ap g0 x) (Ap g1 y) -- third term must be lambda term.
piCoprodComp (Pi (Ap (Prim Inl) x) (Pair g0 g1)) = Ap g0 x
piCoprodComp (Pi (Ap (Prim Inr) y) (Pair g0 g1)) = Ap g1 y

piInductor4 :: Inductor
piInductor4 = Inductor (Pi anyCoprod (Pair U U)) piCoprodComp

pairType :: Term
pairType = Pair U U

sigmaType :: Term
sigmaType = Def (Sigma U U) [Pair U U]

sigmaInductor1 :: Inductor
sigmaInductor1 = Inductor (Pair U (Lambda wild U)) (\ (Pair a (Lambda x b)) -> Sigma (a) (substitution (X x) b a))

sigmaInductor2 :: Inductor
sigmaInductor2 = Inductor (Pair U (Pi U U)) (\ (Pair a (Pi x b)) -> Sigma (a) (substitution x b a))

zero :: Term
zero = Def (Prim Zero) []

zeroInductor :: Inductor
zeroInductor = Inductor (Pi U zero) (\ (Pi c z) -> c)

one :: Term
one = Def (Prim One) [inhabOne, Lambda wild wildcard]

oneInductor :: Inductor
oneInductor = Inductor (Pi one U) (\ (Pi t c) -> c)

two :: Term
two = Def (Prim Two) [Coprod (defConst "𝟎") (defConst "𝟏")]

nat :: Term
nat = Def (Prim Nat) [defConst "0", Ap successor nat]

successor :: Term
successor = defConst "succ"

false2 :: Term
false2 = inl (defConst "𝟎")

true2 :: Term
true2 = inr (defConst "𝟏")

natnum :: Int -> Term
natnum 0 = defConst "0"
natnum n = Ap successor (natnum (n-1))

numnat :: Term -> Int 
numnat (Ap (Prim (DefConst "succ")) n) = numnat n + 1
numnat (Prim (DefConst "0")) = 0

idenTerm :: Term -> Term
idenTerm t = Ident (xInType "x" t) (xInType "y" t)  

identityFunctorLaw1 :: Inductor
identityFunctorLaw1 = Inductor (Ap U (idenTerm U)) (\ (Ap a (Ident b c)) -> Ident (a .$ b) (a .$ c) )

identityFunctorLaw2 :: Inductor
identityFunctorLaw2 = Inductor (Ap (idenTerm U) U) (\ (Ap (Ident a b) c) -> Ident (a .$ c) (b .$ c) )

alphaConversion :: Inductor
alphaConversion = Inductor piType alphaReduce

typeTheory :: InductionTree
typeTheory = insertAllMT emptyMT [zeroInductor, oneInductor, typeInductor,
    reflectLaw, identityFunctorLaw1, identityFunctorLaw2,
    assocLaw0, assocLaw1, alphaConversion,
    prjLInd, prjRInd, 
    reflElim, 
    funcElim, lambdaInductor, 
    piInductor1, piInductor2, piInductor3, piInductor4, piInductorUniq,
    sigmaInductor1, sigmaInductor2]

ctxEmp :: Context
ctxEmp = Ctx Set.empty emptyMT

ctx0 :: Context
ctx0 = newTypes ctxEmp [zero, one, two, nat, piType, sigmaType, pairType, coprodType, (idenTerm U)]

ctx1 :: Context
ctx1 = ctx0 <> Ctx Set.empty typeTheory
