import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Primitive.H6.Double.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  (B : Mod2ReducedMilnorBasis H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- The double tensor-boundary cycle defines a class on the existing
internal E₂ page in (2,128). Nonvanishing on E₂ and identification with
the fixed standard or computed square are not part of this definition. -/
def sphereH6DoubleInternalE2
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B)
    (a : Mod2Cooperations H 64) (ha : cooperationMilnorPolynomial H R B 64 a = h6Polynomial)
    (x : Mod2Homology H 0 SphereSpectrum) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (2, 128) :=
  adamsTowerE2OfFirstCycle H.unit SphereSpectrum 2 128
    ((adamsPageOneHomologyEquiv H.unit SphereSpectrum 2 128).symm
      (sphereH6DoubleTensorRepresentative H R K a x))
    (sphereAdamsDifferential_one_h6_double_zero H R K B hK hD hU hM a ha x)

end
end KIP126.Classical.Adams
