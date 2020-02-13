module Math.Induction where

import Math.Term
import Math.Util
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree 
import qualified Data.Map.Strict as Map
import Control.Applicative

data InductionTree = Null | Node [Term -> Term] Term InductionTree InductionTree

instance Show InductionTree where
    show tree = Tree.drawTree (show <$> indToTree tree)

inductors :: InductionTree -> [Inductor]
inductors = go [] where
    go ls Null = ls
    go ls (Node m t l r) = go ls l ++ go ls r ++ fmap (Inductor t) m

showMatches :: Term -> Context -> Set.Set Term
showMatches t (Ctx ts intree) = go Set.empty t intree where
    go ls tt Null = ls
    go ls tt (Node fs m l r) | tt <= m = Set.union (Set.fromList $ fmap (\ x -> if tt == x tt then tt else Pi tt (x tt)) fs) (Set.union (go ls tt l) (go ls tt r))
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

equivdef :: Term -> Term -> Inductor
equivdef input t = Inductor input (const t)

induct :: Inductor -> Term -> Maybe Term
induct (Inductor m f) t 
    | relation t m == SUBTYPE = Just (f t)
    | relation t m == EQUIV = Just (f t)
    | otherwise = Nothing

pathInduction :: Context -> Term -> Set.Set Term
pathInduction ctx (Pi t1 t2) = Set.union (applyMatches (Pi t1 t2) ctx) (Set.fromList [Pi x y | x <- Set.toList $ pathInduction ctx t1, y <- Set.toList $ pathInduction ctx t2])
pathInduction ctx (Sigma t1 t2) = Set.union (applyMatches (Sigma t1 t2) ctx) (Set.fromList [Sigma x y | x <- Set.toList $ pathInduction ctx t1, y <- Set.toList $ pathInduction ctx t2])
pathInduction ctx (Ident t1 t2) = Set.union (applyMatches (Ident t1 t2) ctx) (Set.fromList [Ident x y | x <- Set.toList $ pathInduction ctx t1, y <- Set.toList $ pathInduction ctx t2])
pathInduction ctx (DefEq t1 t2) = Set.union (applyMatches (DefEq t1 t2) ctx) (Set.fromList [DefEq x y | x <- Set.toList $ pathInduction ctx t1, y <- Set.toList $ pathInduction ctx t2])
pathInduction ctx (Coprod t1 t2) = Set.union (applyMatches (Coprod t1 t2) ctx) (Set.fromList [Coprod x y | x <- Set.toList $ pathInduction ctx t1, y <- Set.toList $ pathInduction ctx t2])
pathInduction ctx (Pair t1 t2) = Set.union (applyMatches (Pair t1 t2) ctx) (Set.fromList [Pair x y | x <- Set.toList $ pathInduction ctx t1, y <- Set.toList $ pathInduction ctx t2])
pathInduction ctx (Ap t1 t2) = Set.union (applyMatches (Ap t1 t2) ctx) (Set.fromList [Ap x y | x <- Set.toList $ pathInduction ctx t1, y <- Set.toList $ pathInduction ctx t2])
pathInduction ctx (Inl t1) = Set.union (applyMatches (Inl t1) ctx) (Set.fromList [Inl x | x <- Set.toList $ pathInduction ctx t1])
pathInduction ctx (Inr t1) = Set.union (applyMatches (Inr t1) ctx) (Set.fromList [Inr x | x <- Set.toList $ pathInduction ctx t1])
pathInduction ctx term = Set.insert term (applyMatches term ctx)

pathIteration :: Context -> Int -> Context
pathIteration ctx 0 = ctx
pathIteration (Ctx set ind) 1 = Ctx (iteratePaths (Ctx set ind) set) ind
pathIteration (Ctx set ind) n = pathIteration (Ctx (iteratePaths (Ctx set ind) set) ind) (n-1)

iteratePaths :: Context -> Set.Set Term -> Set.Set Term
iteratePaths ctx set = Set.fromList $ concatMap (Set.toList . pathInduction ctx) set

reduceIter :: Context -> Int -> Context
reduceIter ctx 0 = ctx
reduceIter (Ctx set ind) 1 = Ctx (reduce (Ctx set ind) set) ind
reduceIter (Ctx set ind) n = pathIteration (Ctx (reduce (Ctx set ind) set) ind) (n-1)

lowestRank :: Set.Set Term -> Term
lowestRank = minByFunc depth

reduce :: Context -> Set.Set Term -> Set.Set Term 
reduce ctx set = Set.singleton $ lowestRank $ Set.fromList $ concatMap (Set.toList . pathInduction ctx) set

derive :: Context -> Context
derive ctx = applyMorphs $ applyDefs ctx 

applyMorphs :: Context -> Context
applyMorphs (Ctx types intree) = go (Set.toList types) where
    go [] = Ctx types intree
    go [t] = Ctx (pathInduction (Ctx types intree) t) intree
    go (t:ts) = go [t] <> go ts

applyDefs :: Context -> Context
applyDefs (Ctx types intree) = go (Set.toList types) where
    go [] = Ctx types intree
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

defIn :: Context -> Term -> Term -> Context
defIn ctx a b = intro (intro ctx (Def b [a])) a

newType :: Term -> Context -> Context
newType (Def s cs) (Ctx set ind) = Ctx set $ insertAllMT (insertMT ind (toIdInd (Def s cs))) (fmap toIdInd cs)
newType (Ap (Ap (Prim DefType) a) b) ctx = newType newT ctx where
    newT = Def b [a]
newType (DefEq x y) (Ctx set tree)  = newType (Def (Ident y y) [DefEq x y]) (Ctx set (insertAllMT tree [Inductor x (const y), Inductor y (const x)]))
newType x (Ctx set tree) = Ctx set (insertMT tree (toIdInd x))

addTypes :: Context -> [Term] -> Context
addTypes = intros

newTypes :: Context -> [Term] -> Context
newTypes ctx [t] = newType t ctx
newTypes ctx (t:ts) = newTypes (newType t ctx) ts

search :: Context -> Set.Set Term -> Set.Set (Set.Set Term)
search ctx patterns = go (Set.toList patterns) where
    go [] = Set.empty
    go (x:xs) = Set.insert (getRelated EQUIV x ctx) (go xs) 

subtypes :: Context -> Term -> Set.Set Term
subtypes ctx t = getRelated SUPERTYPE t ctx

supertypes :: Context -> Term -> Set.Set Term
supertypes ctx t = getRelated SUBTYPE t ctx

equivs :: Context -> Term -> Set.Set Term
equivs ctx t = getRelated EQUIV t ctx

emptyMT :: InductionTree
emptyMT = Node [id] U Null Null

piForm :: Set.Set Term
piForm = Set.fromList [inType (X "A") U, Lambda "x" U] -- two terms, a type, and a lambda. The type refers to the type of the variable bound to the lambda expression.

vble :: Context -> String -> Term -> Context
vble ctx s t = intro ctx (Def t [X s])

typeFamily :: Context -> String -> Term -> Term -> Context
typeFamily ctx s a b = intro (intro ctx (Def a [X s])) (Def (Ap b a) [Ap b (X s)])

piIntro :: Context -> String -> Term -> Term -> Context
piIntro ctx s a b = intro (typeFamily ctx s a b) (Def (Pi a b) [Lambda s (Ap b (X s))])

insertMT :: InductionTree -> Inductor -> InductionTree
insertMT tree ind
    | isMemberOf (indPattern ind) tree = tree
    | otherwise = go tree (indPattern ind) (indMorph ind) where
        go Null (Def tt cs) m = Node [m] tt (insertAllMT Null (fmap toIdInd cs)) Null
        go Null tt m = Node [m] tt Null Null
        go (Node ms t l r) (Def tt cs) m
            | relation (Def tt cs) t == EQUIV = Node (m : ms) t (insertAllMT l (fmap toIdInd cs)) r
            | relation (Def tt cs) t == SUBTYPE = Node ms t (go l (Def tt cs) m) r
            | relation (Def tt cs) t == SUPERTYPE = insertAllMT (Node [m] tt (Node ms t l r) Null) (fmap toIdInd cs)
            | otherwise = Node ms t l (go r (Def tt cs) m)
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

getTree :: Context -> InductionTree
getTree (Ctx set tree) = tree

isMemberOf :: Term -> InductionTree -> Bool
isMemberOf t Null = False
isMemberOf (Def t cs) (Node ms tt l r) 
    | t == tt && and (fmap (`isMemberOf` l) cs) = True
    | otherwise = isMemberOf (Def t cs) l || isMemberOf (Def t cs) r 
isMemberOf t (Node ms tt l r) 
    | t == tt = True
    | otherwise = isMemberOf t l || isMemberOf t r

instance Show Context where
    show (Ctx types intree) = "context: \n" ++ show intree ++ "given types: \n" ++ show (insertAllMT emptyMT $ fmap toIdInd (Set.toList types)) 

instance Semigroup InductionTree where
    ind1 <> ind2 = (insertAllMT emptyMT [toIdInd (treeType (indToTree ind1)), toIdInd (treeType (indToTree ind2))])

instance Monoid InductionTree where
  mempty = emptyMT

instance Semigroup Context where
    ctx1 <> ctx2 = go ctx1 ctx2 where
        go (Ctx ms it1) (Ctx ns it2) = Ctx (Set.union ms ns) (it1 <> it2)

instance Monoid Context where
    mempty = ctxEmp

indToTree :: InductionTree -> Tree.Tree Term
indToTree tree = (go tree) !! 0 where
    go Null = []
    go (Node [] t l r) = uniquesTree $ [Tree.Node t (go l)] ++ go r
    go (Node f t l r) = uniquesTree $ [Tree.Node (go2 t) (go l)] ++ go r where
        go2 t = go3 (fmap (\ x -> (x t)) f) where
            go3 [m] = if t == m then t else Pi t m
            go3 (m:ms) = if ((go3 ms) == (Pi t m)) then (Pi t m) else Pair (go3 ms) (Pi t m)

uniquesTree :: [Tree.Tree Term] -> [Tree.Tree Term]
uniquesTree [] = []
uniquesTree (x:xs) = if elem x xs then xs else x : uniquesTree xs

indToTypes :: InductionTree -> [Term]
indToTypes (Null) = []
indToTypes (Node fs m l r) = Def m (indToTypes l) : indToTypes r

indType :: InductionTree -> Term
indType ind = go (indToTypes ind) where
  go [x] = x
  go xs = Def U xs

ctxType :: Context -> Term
ctxType (Ctx set ind) = indType ind

termTree :: Context -> Tree.Tree Term
termTree ctx = typeTree $ ctxType ctx

mergeTerms :: Term -> Term -> Term
mergeTerms t1 t2 = ctxType $ Ctx Set.empty (insertAllMT emptyMT [toIdInd t1, toIdInd t2])

ctxEmp :: Context
ctxEmp = Ctx Set.empty emptyMT