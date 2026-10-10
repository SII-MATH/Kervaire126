import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Reduced.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Square.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Steenrod.Milnor KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

/-- The positive tensor-basis span is contained in the image of the
actual double reduced inclusion. Each basis generator has an explicit lift. -/
theorem cooperationTensor_reduced_span_le_range (n : ℤ) :
    Submodule.span F2
      (cooperationTensorMilnorBasis H R B n '' {d | d.2.1.val ≠ 0 ∧ d.2.2.val ≠ 0}) ≤
      LinearMap.range (reducedCooperationSquareInclusion H R n) := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  apply Submodule.span_le.mpr
  rintro _ ⟨d, ⟨h₀, h₁⟩, rfl⟩
  refine ⟨DirectSum.lof F2 ℤ _ d.1
    (B.basis d.1 ⟨d.2.1.val, d.2.1.property, h₀⟩ ⊗ₜ[F2]
      B.basis (n - d.1) ⟨d.2.2.val, d.2.2.property, h₁⟩), ?_⟩
  rw [reducedCooperationSquareInclusion_lof_tmul]
  exact (cooperationTensorMilnorBasis_positive H R B n d h₀ h₁).symm

/-- Polynomial normalization supplies a unique actual double-reduced
tensor representative, rather than only a condition on coordinates. -/
theorem cooperationTensor_existsUnique_reduced_of_normalized (n : ℤ)
    (z : cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n)
    (hz : ∀ j : Fin 2, augmentSlot j (cooperationTensorMilnorPolynomial H R B n z) = 0) :
    ∃! w : reducedCooperationSquare H R n,
      reducedCooperationSquareInclusion H R n w = z := by
  obtain ⟨w, hw⟩ := cooperationTensor_reduced_span_le_range H R B n
    (cooperationTensor_mem_span_reduced_of_normalized H R B n z hz)
  refine ⟨w, hw, ?_⟩
  intro w' hw'
  exact reducedCooperationSquareInclusion_injective H R n (hw'.trans hw.symm)

end
end KIP126.StableHomotopy.Cohomology
