module Math.Induction.IdentityType where

import Math.Term
import Math.Util

path1 :: Term -> Term -> Term
path1 a b = bind (Var "x" a) (Ident (X "x") b)

path2 :: Term -> Term
path2 a = bind (Var "x" a) (bind (Var "y" a) (Ident (X "x") (X "y")))

ident :: Term
ident = bind (X "A") (path2 (X "A"))

pathVar2 :: Term
pathVar2 = bind (X "p") (bind (X "x") (bind (X "y") (Var "p" (Ident (X "x") (X "y")))))

refl :: Term
refl = define (Prim Refl) (bind (X "A") (bind (Var "x" (X "A")) (Ident (X "x") (X "x"))))

define :: Term -> Term -> Term
define a b = Def (Ident a b) [a .= b]

identInd :: Term
identInd = bind (Var "c" (Lambda "z" U)) ((cnst "Ind_=") .$ pathVar2 .$ (X "c"))