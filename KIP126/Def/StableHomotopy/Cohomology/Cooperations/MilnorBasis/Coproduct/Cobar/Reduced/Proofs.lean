import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Cobar.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Reduced.Square.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Steenrod.Milnor KIP126.Core.Algebra

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R) (K : Mod2CooperationKunneth H R)
  (hU : Mod2KunnethUnitCompatible H R K)
  (hM : Mod2MilnorCoproductCompatible H R K B)

include hU hM

/-- Both slots of the actual corrected coproduct of a reduced cooperation
are polynomially normalized. The property follows from the proved cobar
formula and normalization theorem; it is not an additional input. -/
theorem cooperationCobarDiagonal_reduced_normalized (n : ℤ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ (a : LinearMap.ker (cooperationCounitF2 H R n)) (j : Fin 2),
      augmentSlot j (cooperationTensorMilnorPolynomial H R B n
        (cooperationCobarDiagonal H R K n a.val)) = 0 := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a j
  rw [cooperationCobarDiagonal_polynomial H R B K hU hM]
  exact differentialPolynomial_normalized _
    (cooperationMilnorPolynomial_reduced_normalized H R B n a) j

/-- The actual corrected coproduct is a linear combination of actual
tensor basis elements whose two factors are both reduced. -/
theorem cooperationCobarDiagonal_mem_span_reduced (n : ℤ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R n),
      cooperationCobarDiagonal H R K n a.val ∈ Submodule.span F2
        (cooperationTensorMilnorBasis H R B n '' {d | d.2.1.val ≠ 0 ∧ d.2.2.val ≠ 0}) := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  exact cooperationTensor_mem_span_reduced_of_normalized H R B n _
    (cooperationCobarDiagonal_reduced_normalized H R B K hU hM n a)

/-- In nonzero degree every cooperation is already reduced. In particular
this covers all degree-128 candidates in the actual incoming-image test. -/
theorem cooperationCobarDiagonal_mem_span_reduced_of_ne (n : ℤ) (hn : n ≠ 0)
    (a : Mod2Cooperations H n) :
    cooperationCobarDiagonal H R K n a ∈ Submodule.span F2
      (cooperationTensorMilnorBasis H R B n '' {d | d.2.1.val ≠ 0 ∧ d.2.2.val ≠ 0}) := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  have ha : a ∈ LinearMap.ker (cooperationCounitF2 H R n) := by
    rw [LinearMap.mem_ker, cooperationCounitF2_eq_zero_of_ne H R n hn, LinearMap.zero_apply]
  exact cooperationCobarDiagonal_mem_span_reduced H R B K hU hM n ⟨a, ha⟩

/-- Every reduced cooperation has a unique actual double-reduced corrected
coproduct. This existence is proved from below-page compatibility. -/
theorem cooperationCobarDiagonal_existsUnique_reduced (n : ℤ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R n),
      ∃! w : reducedCooperationSquare H R n,
        reducedCooperationSquareInclusion H R n w = cooperationCobarDiagonal H R K n a.val := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  exact cooperationTensor_existsUnique_reduced_of_normalized H R B n _
    (cooperationCobarDiagonal_reduced_normalized H R B K hU hM n a)

/-- In particular all nonzero-degree incoming candidates have a unique
double-reduced coproduct; no extra reducedness premise is required. -/
theorem cooperationCobarDiagonal_existsUnique_reduced_of_ne (n : ℤ) (hn : n ≠ 0)
    (a : Mod2Cooperations H n) :
    ∃! w : reducedCooperationSquare H R n,
      reducedCooperationSquareInclusion H R n w = cooperationCobarDiagonal H R K n a := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  have ha : a ∈ LinearMap.ker (cooperationCounitF2 H R n) := by
    rw [LinearMap.mem_ker, cooperationCounitF2_eq_zero_of_ne H R n hn, LinearMap.zero_apply]
  exact cooperationCobarDiagonal_existsUnique_reduced H R B K hU hM n ⟨a, ha⟩

end
end KIP126.StableHomotopy.Cohomology
