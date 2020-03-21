{-# LANGUAGE GADTs #-}

module Math.Induction.Induction where

import Math.Context
import Math.Term
import Math.Former
import Math.Util
import Math.Induction.TypeMatch
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree

newtype Inductor = Inductor [(Pattern, Term -> Term)]

prove :: Former Term -> Context (Tree.Tree Term) -> Context (Tree.Tree Term)
prove (C s xs) ctx = if and (fmap (exists ctx) xs) then intro ctx (form $ C s xs) else error "Cannot form, some types do not exist."
prove (Family x a b) ctx = if isTrue ctx a then intros ctx ((Def (Pi a U) [b]) : (fmap (b .$) (shallowMatch ctx (Var x a)))) else intro ctx (Pi (form (Family x a b)) (Prim Zero))
prove (Set a xs) ctx = intro ctx (form (Set a xs))
prove (NewType x) ctx = intro ctx (cnst x)
prove (ForAll x a b) ctx = if isTrue ctx a then intros ctx ((Def (Pi a U) [b]) : (fmap (Ap (form (ForAll x a b))) (shallowMatch ctx (Var x a)))) else intro ctx (Pi (form (ForAll x a b)) (Prim Zero))
prove (Equals a b) ctx
    | exists ctx a && exists ctx b = if (typeOf ctx a == typeOf ctx b) then intro ctx (Def (Ident a b) [form (Equals a b)]) else error $ "terms already exist and are not the same type: " ++ show (typeOf ctx a) ++ ", " ++ show (typeOf ctx b)
    | exists ctx a = intros ctx [Def (last $ typeOf ctx a) [b], (Def (Ident a b) [form (Equals a b)])]
    | exists ctx b = intros ctx [Def (last $ typeOf ctx b) [a], (Def (Ident a b) [form (Equals a b)])]
    | otherwise = intros ctx [a, b, (Def (Ident a b) [form (Equals a b)])]

computeBeta :: Context (Tree.Tree Term) -> Context (Tree.Tree Term)
computeBeta ctx = intros ctx (go (typeMatch ctx a)) where
    a = Ap (Pi U U) U
    go [] = []
    go (x:xs) = if x /= beta x then (Ident x (beta x)) : go xs else go xs
