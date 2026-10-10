import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Cobar.Reduced.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Core.Algebra

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R) (K : Mod2CooperationKunneth H R)

/-- The actual corrected coproduct, with its codomain restricted using
the proved double reduction. No extra differential data is supplied. -/
def cooperationReducedCobarDiagonal
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B) (n : ℤ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    LinearMap.ker (cooperationCounitF2 H R n) →ₗ[F2] reducedCooperationSquare H R n := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  exact ((cooperationCobarDiagonal H R K n).comp
    (LinearMap.ker (cooperationCounitF2 H R n)).subtype).codRestrictOfInjective
      (reducedCooperationSquareInclusion H R n)
      (reducedCooperationSquareInclusion_injective H R n)
      (fun a => (cooperationCobarDiagonal_existsUnique_reduced H R B K hU hM n a).exists)

end
end KIP126.StableHomotopy.Cohomology
