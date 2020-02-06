module Math.Induction.SigmaType where

import Math.Term
import Math.Induction
import Math.Induction.PiType
import Math.Util

sigmaExposedTypes :: [Term]
sigmaExposedTypes = [sigmaType, sigmaIntro1Type, sigmaIntro2Type, sigmaElimTerm, sigmaInductorType]

sigmaExposedInductors :: [Inductor]
sigmaExposedInductors = [sigmaIntro1Ind, sigmaIntro2Ind, sigmaInductor]

sigmaType :: Term
sigmaType = Def (Sigma U U) [sigmaIntro1Type, sigmaIntro2Type]

sigmaIntro1Type :: Term
sigmaIntro1Type = Pair wildcard lambdaType

sigmaIntro1 :: Term -> Term
sigmaIntro1 (Pair (X a) (Lambda x b)) = Sigma (X a) (beta $ (Lambda x b) .$ (X a))

sigmaIntro1Ind :: Inductor
sigmaIntro1Ind = Inductor sigmaIntro1Type sigmaIntro1

sigmaIntro2Type :: Term
sigmaIntro2Type = Pair U piType

sigmaIntro2 :: Term -> Term
sigmaIntro2 (Pair a (Pi x b))
  | relation a x == SUBTYPE = Sigma a (b .$ a)
  | otherwise = (Pair a (Pi x b))

sigmaIntro2Ind :: Inductor
sigmaIntro2Ind = Inductor sigmaIntro2Type sigmaIntro2

sigmaElimTerm :: Term
sigmaElimTerm = Pi sigmaType U

sigmaComp :: Term -> Term
sigmaComp (Ap (Pi (Sigma a b) c) (Pair x y)) = (c .$ x) .$ y
sigmaComp (Ap (Pi (Sigma a b) c) (Sigma x y)) = (c .$ x) .$ y
sigmaComp (Ap (Pi (Def (Sigma a b) ls) c) d) = sigmaComp (Ap (Pi (Sigma a b) c) d)
sigmaComp (Ap (Pi a c) (Def (Sigma x y) ls)) = sigmaComp (Ap (Pi a c) (Sigma x y))

sigmaInductorType :: Term
sigmaInductorType = (Ap (Pi sigmaType U) sigmaType)

sigmaInductor :: Inductor
sigmaInductor = Inductor sigmaInductorType sigmaComp

