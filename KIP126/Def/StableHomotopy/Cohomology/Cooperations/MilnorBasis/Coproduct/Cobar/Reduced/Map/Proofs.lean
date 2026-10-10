import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Cobar.Reduced.Map.Data

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Steenrod.Milnor KIP126.Core.Algebra

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R) (K : Mod2CooperationKunneth H R)
  (hU : Mod2KunnethUnitCompatible H R K)
  (hM : Mod2MilnorCoproductCompatible H R K B)

/-- Inclusion recovers the original actual corrected coproduct exactly. -/
theorem cooperationReducedCobarDiagonal_inclusion (n : ℤ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R n),
      reducedCooperationSquareInclusion H R n
        (cooperationReducedCobarDiagonal H R B K hU hM n a) =
          cooperationCobarDiagonal H R K n a.val := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  exact LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ a

/-- The derived reduced map realizes the original polynomial cobar
differential; normalization has been proved, not added as a premise. -/
theorem cooperationReducedCobarDiagonal_polynomial (n : ℤ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R n),
      cooperationTensorMilnorPolynomial H R B n
        (reducedCooperationSquareInclusion H R n
          (cooperationReducedCobarDiagonal H R B K hU hM n a)) =
        differentialPolynomial 1 (cooperationMilnorPolynomial H R B n a.val) := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  rw [cooperationReducedCobarDiagonal_inclusion]
  exact cooperationCobarDiagonal_polynomial H R B K hU hM n a.val

end
end KIP126.StableHomotopy.Cohomology
