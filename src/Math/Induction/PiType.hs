module Math.Induction.PiType where

import Math.Term
import Math.Induction
import Math.Util

piExposedTypes :: [Term]
piExposedTypes = [lambdaType, lambdaType2, piType, pairType]

piExposedInductors :: [Inductor]
piExposedInductors = [lambdaInductor, curryInductor, alphaConversion, piPairInductor, prjLInd, prjRInd]

lambdaType :: Term
lambdaType = Lambda wild U

lambdaType2 :: Term
lambdaType2 = Lambda wild lambdaType

piType :: Term
piType =  Pi U U

pairType :: Term
pairType = Pair U U

lambdaInductor :: Inductor 
lambdaInductor = Inductor (Ap lambdaType U) beta

curryFunc :: Term -> Term
curryFunc (Ap (Lambda x (Lambda y f)) (Pair a b)) = ((Lambda x (Lambda y f)) .$ a) .$ b
curryFunc els = error $ show els

curryInductor :: Inductor
curryInductor = Inductor (Ap lambdaType2 pairType) curryFunc

alphaConversion :: Inductor
alphaConversion = Inductor piType alphaReduce

piPairInductor :: Inductor
piPairInductor = Inductor (Pi (Pair U U) (Lambda wild U)) (\ (Pi (Pair x y) c) -> bind x (bind y (beta $ c .$ (Pair x y))))  

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
