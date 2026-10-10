import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Data
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.H6.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
  KIP126.Steenrod.Milnor

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The sphere coefficient normalized to the empty word with coefficient one.
It is constructed using the sphere unitor and the specified π₀ coordinate. -/
def sphereMilnorUnitCoefficient : Mod2Homology H 0 SphereSpectrum :=
  (sphereHomologyEmptyWordEquiv H R 0).symm (Finsupp.single emptyMilnorWord 1)

end
end KIP126.Classical.Adams
