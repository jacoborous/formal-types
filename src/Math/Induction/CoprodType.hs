module Math.Induction.CoprodType where

import Math.Term
import Math.Induction
import Math.Util

anyCoprod :: Term
anyCoprod = Coprod U U

coprodType :: Term
coprodType = Def anyCoprod [Inl U, Inr U]

coprodRec :: Term
coprodRec = cnst "coprod_rec"

coprodRecursor :: Term -> Term -> Term -> Term
coprodRecursor z g0 g1 = bind z (coprodRec .$ Pair (Pair g0 g1) z)

piCoprodInductor :: Inductor
piCoprodInductor = Inductor (Pi (Coprod U U) (Lambda wild (Coprod U U))) (\ (Pi (Coprod x y) (Lambda z (Coprod g0 g1))) -> coprodRecursor (X z) (bind x $ beta (Lambda z g0 .$ x)) (bind y $ beta (Lambda z g1 .$ y)))

piCoprodDef :: Term -> Term
piCoprodDef (Ap (Prim (DefConst "coprod_rec")) (Pair (Pair g0 g1) (Coprod a b))) = Coprod (g0 .$ a) (g1 .$ b)
piCoprodDef (Ap (Prim (DefConst "coprod_rec")) (Pair (Pair g0 g1) (Inl a))) = g0 .$ a
piCoprodDef (Ap (Prim (DefConst "coprod_rec")) (Pair (Pair g0 g1) (Inr b))) = g1 .$ b

coprodRecInductor :: Inductor
coprodRecInductor = Inductor (coprodRec .$ Pair (Pair U U) (Coprod U U)) piCoprodDef