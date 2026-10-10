import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Data
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Steenrod.Milnor KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)
  (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

/-- One reduced basis factor and one word become their concatenated word. -/
theorem reducedTensorMilnorWordEquiv_basis_single (s : ℕ)
    (e : ∀ i, V i ≃ₗ[ZMod 2] (MilnorWord s (i + s) →₀ ZMod 2))
    (n k : ℤ) (a : PositiveMonomial k) (x : V (n + 1 - k))
    (d : MilnorWord s (n + (s + 1 : ℕ) - k)) (q : ZMod 2)
    (hx : (LinearEquiv.cast (R := ZMod 2) (M := fun t => MilnorWord s t →₀ ZMod 2)
      (show n + 1 - k + s = n + (s + 1 : ℕ) - k by omega)) (e _ x) = Finsupp.single d q) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    reducedTensorMilnorWordEquiv H R B V s e n
      (DirectSum.lof (ZMod 2) ℤ _ k ((B.basis k) a ⊗ₜ[ZMod 2] x)) =
      Finsupp.single (wordConsEquiv s (n + (s + 1 : ℕ)) ⟨k, a, d⟩) q := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  simp only [reducedTensorMilnorWordEquiv, LinearEquiv.trans_apply,
    DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
    LinearEquiv.coe_coe, TensorProduct.congr_tmul, Module.Basis.repr_self, hx]
  simpa only [one_mul] using wordTensorEquiv_single s (n + (s + 1 : ℕ)) k a d 1 q

end
end KIP126.StableHomotopy.Cohomology
