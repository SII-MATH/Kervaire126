module

public import KIP126.Def.StageInput.StandardSphere.Algebra.Components.Data
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Proofs

@[expose] public section


/-! Fixed actual E₂ multiplication: its defining comparison and the remaining
structural obligations. Left unitality and associativity remain unfinished here;
commutativity is derived from the explicit cobar commutator-boundary obligation.
All three concern the fixed cobar and tower construction, not native-certificate
inputs, and quantify over all nonnegative bidegrees. -/

namespace KIP126.Classical.Adams.Sphere.Internal

open KIP126.Core.Algebra
noncomputable section

set_option maxHeartbeats 1200000 in
/-- Bundling F₂-linearity does not replace the existing actual product. -/
theorem actualE2Product_apply (p q : ℕ × ℕ) (x : ActualE2At p) (y : ActualE2At q) :
    actualE2Product p q x y =
      product standardFoundation.hf2 standardMilnorCooperations
        (s := p.1) (t := p.2) (s' := q.1) (t' := q.2) x y := rfl

-- Avoid elaborator reduction through the fixed stable-homotopy model when
-- checking elementary identities of the already bundled linear maps.
attribute [local irreducible] ActualE2At actualE2AtModule actualE2Product
  actualE2ToCobar actualE2ToCobarInt

/-- The sphere-identity class is a left unit for the fixed transported cobar
product. This requires the actual identity/cobar-unit comparison. -/
theorem actualE2_one_mul (a : GradedMonoid ActualE2At) : 1 * a = a := by
  sorry

/-- Cobar concatenation descends associatively to the actual E₂ components,
including the indicated changes of total bidegree. -/
theorem actualE2_mul_assoc (a b c : GradedMonoid ActualE2At) :
    a * b * c = a * (b * c) := by
  sorry

private theorem actualE2ToCobar_symm_heq {p q : ℕ × ℕ} (h : p = q)
    (x : MilnorCohomology.Cohomology standardFoundation.hf2
      standardMilnorCooperations p.1 p.2)
    (y : MilnorCohomology.Cohomology standardFoundation.hf2
      standardMilnorCooperations q.1 q.2) (hxy : HEq x y) :
    HEq ((actualE2ToCobar p).symm x) ((actualE2ToCobar q).symm y) := by
  subst q
  cases hxy
  rfl

set_option maxHeartbeats 1200000 in
/-- Commutativity follows from the cobar statement that the concatenation
commutator of every two cycles is a boundary, via cohomology and the fixed
canonical comparison. The remaining mathematical obligation is exactly
`MilnorCohomology.cup_commutator_mem_boundaries`; concatenation itself is not
assumed commutative. -/
theorem actualE2_mul_comm (a b : GradedMonoid ActualE2At) : a * b = b * a := by
  obtain ⟨p, x⟩ := a
  obtain ⟨q, y⟩ := b
  apply Sigma.ext (add_comm p q)
  change HEq (actualE2Product p q x y) (actualE2Product q p y x)
  unfold actualE2Product
  apply actualE2ToCobar_symm_heq (add_comm p q)
  exact (heq_of_eq (MilnorCohomology.cup_comm standardFoundation.hf2
    standardMilnorCooperations (actualE2ToCobar p x) (actualE2ToCobar q y))).trans
      (MilnorCohomology.cohomologyReindex_heq standardFoundation.hf2
        standardMilnorCooperations _ _ _)

/-- Scalar multiplication in the first factor follows from the existing
bilinear map, before any multiplicative structural laws are used. -/
theorem actualE2_smul_mul (r : F2) (a b : GradedMonoid ActualE2At) :
    (r • a) * b = r • (a * b) := by
  obtain ⟨p, x⟩ := a
  obtain ⟨q, y⟩ := b
  exact Sigma.ext rfl
    (heq_of_eq (LinearMap.congr_fun ((actualE2Product p q).map_smul r x) y))

/-- Right unitality follows from the stated left-unit and commutativity
obligations; it is not a fourth independent assumption. -/
theorem actualE2_mul_one (a : GradedMonoid ActualE2At) : a * 1 = a := by
  rw [actualE2_mul_comm, actualE2_one_mul]

end
end KIP126.Classical.Adams.Sphere.Internal
