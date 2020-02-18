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

prove :: Former Term -> Context (Tree.Tree Term) -> Context (Tree.Tree Term)
prove (C s xs) ctx = if and (fmap (exists ctx) (fmap form xs)) then intro ctx (form $ C s xs) else error "Cannot form, some types do not exist."
prove (Family x a b) ctx = if isTrue ctx a && exists ctx (Def (Pi a U) [b]) then intros ctx (fmap (b .$) (shallowMatch ctx (Var x a))) else intro ctx (Pi (form (Family x a b)) (Prim Zero))
prove (Set a xs) ctx = intro ctx (form (Set a xs))
prove (NewType x) ctx = intro ctx (cnst x)
prove (ForAll x a b) ctx = if isTrue ctx a && exists ctx (Def (Pi a U) [b]) then intros ctx (fmap (Ap (form (ForAll x a b))) (shallowMatch ctx (Var x a))) else intro ctx (Pi (form (ForAll x a b)) (Prim Zero))