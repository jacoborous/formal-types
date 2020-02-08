module Math.Induction.NatType where

import Math.Term
import Math.Induction
import Math.Util

natExposedTypes :: [Term]
natExposedTypes = [zero, one, two, false2, true2, ind2Type, pi2Type, nat, successor, indNatType]

natExposedInductors :: [Inductor]
natExposedInductors = [zeroInductor, oneInductor, ind2Inductor, pi2Inductor, natInductor, piNatInductor]

zero :: Term
zero = Def (Prim Zero) []

zeroInductor :: Inductor
zeroInductor = Inductor (Pi U zero) (\ (Pi c z) -> c)

inhabOne :: Term
inhabOne = cnst "⋆"

one :: Term
one = Def (Prim One) [inhabOne]

oneInductor :: Inductor
oneInductor = Inductor (Pi one U) (\ (Pi t c) -> c)

false2 :: Term
false2 = cnst "𝐅"

true2 :: Term
true2 = cnst "𝐓"

two :: Term
two = Def (Prim Two) [true2, false2]

ind2 :: Term -> Term -> Term -> Term
ind2 c0 c1 n = bind n (Ap (cnst "2_ind") (tuple [c0, c1, n]))

ind2Type :: Term
ind2Type = cnst "2_ind" .$ tuple [U, U, two]

ind2Comp :: Term -> Term
ind2Comp (Ap (Prim (DefConst "2_ind")) (Pair c0 (Pair c1 (Prim (DefConst "𝐓"))))) = c0
ind2Comp (Ap (Prim (DefConst "2_ind")) (Pair c0 (Pair c1 (Prim (DefConst "𝐅"))))) = c1
ind2Comp (Ap (Prim (DefConst "2_ind")) (Pair c0 (Pair c1 (Def (Prim Two) cs)))) = Coprod c0 c1
ind2Comp els = error $ show els

ind2Inductor :: Inductor
ind2Inductor = Inductor ind2Type ind2Comp

pi2Type :: Term 
pi2Type = Pi two (Lambda wild (Pair U U))

pi2Comp :: Term -> Term
pi2Comp (Pi (Def (Prim Two) cs) (Lambda z (Pair c0 c1))) = indNat c0 c1 (X z)

pi2Inductor :: Inductor
pi2Inductor = Inductor pi2Type pi2Comp

nat :: Term
nat = Def (Prim Nat) [cnst "0", Ap (cnst "succ") (Prim Nat)]

successor :: Term
successor = Lambda wild (Ap (cnst "succ") wildcard)

natnum :: Int -> Term
natnum 0 = cnst "0"
natnum n = Ap successor (natnum (n-1))

numnat :: Term -> Int 
numnat (Ap (Prim (DefConst "succ")) n) = numnat n + 1
numnat (Prim (DefConst "0")) = 0

tuple :: [Term] -> Term
tuple [] = one
tuple [t] = t
tuple (t:ts) = Pair t (tuple ts)

indNat :: Term -> Term -> Term -> Term
indNat c0 cs n = bind n (Ap (cnst "nat_ind") (tuple [c0, cs, n]))

indNatType :: Term
indNatType = indNat U U nat

natIndComp :: Term -> Term
natIndComp (Ap (Prim (DefConst "nat_ind")) (Pair c0 (Pair cs (Prim (DefConst "0"))))) = c0
natIndComp (Ap (Prim (DefConst "nat_ind")) (Pair c0 (Pair cs (Ap (Prim (DefConst "succ")) n)))) = Ap cs (Pair n (beta $ (indNat c0 cs (X "𝒏")) .$ n)) --(alpha (X "𝒏") (indNat c0 cs n))
natIndComp (Ap (Prim (DefConst "nat_ind")) (Pair c0 (Pair cs n))) = Coprod c0 (Ap cs (Ap cs (Pair n (alpha (X "𝒏") (indNat c0 cs n))))) 
natIndComp els = error $ show els

natInductor :: Inductor
natInductor = Inductor ((cnst "nat_ind") .$ Pair U (Pair U nat)) natIndComp

piNatInductor :: Inductor
piNatInductor = Inductor (Pi nat (Lambda wild (Coprod U U))) 
    (\ (Pi nat (Lambda z (Coprod g0 g1))) -> bind (X "𝑛") (indNat (bind (indX 0) $ beta ((Lambda z g0) .$ (indX 0))) (bind (indX 1) $ beta ((Lambda z g1) .$ (indX 1))) (X "𝑛")))