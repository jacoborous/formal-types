{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}

module Math.Former where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree (Tree)
import qualified Data.Tree as Tree
import qualified Data.Map.Strict as Map
import Control.Applicative
import Data.Semigroup
import Data.List
import Math.Util
import Math.Term
import Math.Context

data Former a where
    NewType :: String -> Former Term
    C :: String -> [Term] -> Former Term
    Set :: Term -> [Term] -> Former Term
    Variable :: String -> Term -> Former Term
    Apply :: Context (Tree.Tree Term) -> Term -> [Term] -> Former Term
    Function :: Term -> Term -> Former Term
    Family :: String -> Term -> Term -> Former Term
    ForAll :: String -> Term -> Term -> Former Term
    ThereExists :: String -> Term -> Term -> Former Term
    Bind :: Term -> Term -> Former Term
    Subst :: Term -> Term -> Term -> Former Term
    BetaReduce :: Term -> Former Term
    AlphaReduce :: Term -> Former Term
    Equals :: Term -> Term -> Former Term


form :: Former a -> a
form (NewType s) = cnst s
form (C s xs) = foldl (.$) (cnst s) xs
form (Set a b) = Def a b
form (Variable s t) = Var s t
form (Function a b) = if Set.disjoint (freeVars a) (freeVars b) then Pi a b else error $ "Cannot construct the function type: type " ++ show b ++ " depends on elements from type " ++ show a
form (Family x U b) = Ap b (X x)
form (Family x a b) = Ap b (Var x a)
form (ForAll x U b) = Lambda x (Ap b (X x))
form (ForAll x a b) = Pi (Var x a) (Ap b (Var x a))
form (ThereExists x a b) = Sigma a (beta $ (form $ ForAll x a b) .$ a) --elim
form (Bind x a) = bind x a
form (Subst e r m) = substitution m e r
form (Apply ctx f args) = go (arity f) args where
  go [] [] = f
  go (m:ms) (x:xs) = if compare2 ctx x m == Just SUBTYPE then form (Apply ctx (beta $ f .$ x) xs) else error $ "Illegal argument exception: " ++ show m ++ ", given: " ++ show x
  go [] xs = error "Too many arguments given."
  go ms [] = error "Too few arguments given."
form (BetaReduce t) = betaReduce t
form (AlphaReduce t) = alphaReduce t
form (Equals x y) = DefEq x y

instance Show a => Show (Former a) where
    show a = show $ form a
    