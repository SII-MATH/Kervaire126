import KIP126.LinProgram.Model.E2.Native.Data
import KIP126.Def.Algebra.GradedQuotient.PolynomialTruncation.Proofs

namespace KIP126.LinE2
open KIP126.Core.Algebra MvPolynomial
open KIP126.Algebra.PolynomialTruncation
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

local instance : GradedAlgebra (weightedHomogeneousSubmodule F2 generatorDegree) :=
  weightedGradedAlgebra F2 generatorDegree

 theorem weight_generatorDegree (m : Generator →₀ ℕ) :
    Finsupp.weight generatorDegree m = monomialDegree m := by
  rw [Finsupp.weight_apply]
  unfold monomialDegree
  apply Finsupp.sum_congr
  intro i _
  change (m i • generatorDegree i) = (m i * (generatorDegree i).1, m i * (generatorDegree i).2)
  exact Prod.ext (by simp) (by simp)


 theorem definingIdeal_eq_sup :
    definingIdeal = nativeIdeal ⊔ highIdeal (R := F2) generatorDegree 261 := by
  simpa only [definingIdeal, nativeIdeal, highIdeal, definingRelations, weight_generatorDegree, Set.setOf_or]
    using (Ideal.span_union
      {p : Poly | ∃ code ∈ RawData.relations, p = relationPolynomial code}
      {p : Poly | ∃ m : Generator →₀ ℕ, 261 < (monomialDegree m).2 ∧
        p = MvPolynomial.monomial m 1})

/-- A weighted homogeneous polynomial gives a class in the historical span component. -/
theorem projection_mem_of_weighted {p : Poly} {d : ℕ × ℕ}
    (hp : p.IsWeightedHomogeneous generatorDegree d) :
    projection p ∈ homogeneousPart d.1 d.2 := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simpa only [map_add] using
      (homogeneousPart d.1 d.2).add_mem ihp ihq
  | monomial m r hm =>
    have hb : projection (MvPolynomial.monomial m (1 : F2)) ∈ homogeneousPart d.1 d.2 :=
      Submodule.subset_span ⟨m, by simpa only [← weight_generatorDegree, Prod.mk.eta] using hm, rfl⟩
    have hh := (homogeneousPart d.1 d.2).smul_mem r hb
    change r • (Ideal.Quotient.mkₐ F2 definingIdeal) (MvPolynomial.monomial m 1) ∈ _ at hh
    simp only [← map_smul, smul_eq_mul, mul_one] at hh
    exact hh

/-- The previous monomial-span definition is exactly the quotient image of the polynomial grading. -/
theorem homogeneousPart_eq_map (s t : ℕ) :
    homogeneousPart s t = (weightedHomogeneousSubmodule F2 generatorDegree (s,t)).map
      (Ideal.Quotient.mkₐ F2 definingIdeal).toLinearMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨m, hm, rfl⟩
    exact ⟨MvPolynomial.monomial m 1,
      MvPolynomial.isWeightedHomogeneous_monomial generatorDegree m 1
        ((weight_generatorDegree m).trans hm), rfl⟩
  · rintro x ⟨p, hp, rfl⟩
    exact projection_mem_of_weighted hp

/-- The untruncated component has the same native monomial-span interpretation. -/
theorem nativeHomogeneousPart_eq_span (s t : ℕ) :
    nativeHomogeneousPart s t = Submodule.span F2
      {x | ∃ m : Generator →₀ ℕ, monomialDegree m = (s,t) ∧
        x = nativeProjection (MvPolynomial.monomial m 1)} := by
  apply le_antisymm
  · rintro x ⟨p, hp, rfl⟩
    induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p q hp hq ihp ihq => simpa only [map_add] using
        (Submodule.span F2 _).add_mem ihp ihq
    | monomial m r hm =>
      have hb : nativeProjection (MvPolynomial.monomial m (1 : F2)) ∈ Submodule.span F2
          {x | ∃ m : Generator →₀ ℕ, monomialDegree m = (s,t) ∧
            x = nativeProjection (MvPolynomial.monomial m 1)} :=
        Submodule.subset_span ⟨m, (weight_generatorDegree m).symm.trans hm, rfl⟩
      have hh := (Submodule.span F2 _).smul_mem r hb
      simp only [← map_smul, smul_eq_mul, mul_one] at hh
      exact hh
  · apply Submodule.span_le.mpr
    rintro x ⟨m, hm, rfl⟩
    exact ⟨MvPolynomial.monomial m 1,
      MvPolynomial.isWeightedHomogeneous_monomial generatorDegree m 1
        ((weight_generatorDegree m).trans hm), rfl⟩

 theorem truncate_mem {s t : ℕ} {x : NativeAlgebra}
    (hx : x ∈ nativeHomogeneousPart s t) : truncate x ∈ homogeneousPart s t := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact projection_mem_of_weighted hp

/-- The canonical restriction, before proving that it is a low-degree equivalence. -/
def truncateAt (s t : ℕ) : NativeAt s t →ₗ[F2] E2At s t :=
  (truncate.toLinearMap.comp (nativeHomogeneousPart s t).subtype).codRestrict _
    (fun x => truncate_mem x.property)

@[simp] theorem truncateAt_val (s t : ℕ) (x : NativeAt s t) :
    (truncateAt s t x).val = truncate x.val := rfl

 theorem truncateAt_surjective (s t : ℕ) : Function.Surjective (truncateAt s t) := by
  intro y
  have hy := (le_of_eq (homogeneousPart_eq_map s t)) y.property
  obtain ⟨p, hp, hpy⟩ := hy
  exact ⟨⟨nativeProjection p, ⟨p, hp, rfl⟩⟩, Subtype.ext hpy⟩

 theorem truncateAt_injective_of_homogeneous
    (hI : nativeIdeal.IsHomogeneous (weightedHomogeneousSubmodule F2 generatorDegree))
    (s t : ℕ) (ht : t ≤ 261) : Function.Injective (truncateAt s t) := by
  apply (injective_iff_map_eq_zero (truncateAt s t)).mpr
  intro x hx
  obtain ⟨p, hp, hpx⟩ := x.property
  change nativeProjection p = x.val at hpx
  have hz : projection p = 0 := by
    have h := congrArg Subtype.val hx
    change truncate x.val = 0 at h
    rw [← hpx, truncate_projection] at h
    exact h
  have hmem : p ∈ definingIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hz
  rw [definingIdeal_eq_sup] at hmem
  have hn : p ∈ nativeIdeal := (low_mem_sup_iff generatorDegree nativeIdeal hI 261 hp ht).mp hmem
  apply Subtype.ext
  change x.val = 0
  rw [← hpx]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hn

end
end KIP126.LinE2
