import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Data
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Single.Data

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Steenrod.Milnor KIP126.Core.Algebra

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

/-- Reduced cooperation coordinates exhaust the existing normalized
one-slot cochains. This uses only the specified reduced Milnor basis. -/
def reducedCooperationCochainEquiv (n : ℕ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    LinearMap.ker (cooperationCounitF2 H R n) ≃ₗ[F2] cochains 1 n :=
  (B.basis n).repr.trans
    ((Finsupp.domLCongr (R := F2) (singleMilnorWordEquiv n)).trans (cochainsWordEquiv 1 n).symm)

end
end KIP126.StableHomotopy.Cohomology
