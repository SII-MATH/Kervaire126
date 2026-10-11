module

public import KIP126.LinProgram.Model.ModulePresentation.Grading.Data
public import KIP126.LinProgram.Model.ModulePresentation.Maps
public import KIP126.LinProgram.Model.E2.Proofs

@[expose] public section


set_option backward.isDefEq.respectTransparency false

namespace KIP126.LinModule.Presentation
open KIP126.Core.Algebra
variable {M : Type*} [AddCommGroup M] [Module LinE2.E2 M]
  [Module F2 M] [IsScalarTower F2 LinE2.E2 M]
  {n : Nat} {g : Fin n → M} {degree : Fin n → ℤ × ℤ}

theorem coefficientDegree_add (m m' : LinE2.Generator →₀ ℕ) :
    coefficientDegree (m + m') = coefficientDegree m + coefficientDegree m' := by
  simp [coefficientDegree, LinE2.monomialDegree_add]

@[simp] theorem coefficientDegree_zero : coefficientDegree 0 = 0 := by
  simp [coefficientDegree, LinE2.monomialDegree]

theorem generator_mem_homogeneousSpan (i : Fin n) :
    g i ∈ homogeneousSpan g degree (degree i) := by
  apply Submodule.subset_span
  exact ⟨i, 0, by simp, by simp⟩

theorem monomial_smul_mem_homogeneousSpan (m : LinE2.Generator →₀ ℕ)
    {d : ℤ × ℤ} {x : M} (hx : x ∈ homogeneousSpan g degree d) :
    LinE2.projection (MvPolynomial.monomial m 1) • x ∈
      homogeneousSpan g degree (coefficientDegree m + d) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, m', hd, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨i, m + m', ?_, ?_⟩
    · rw [coefficientDegree_add, add_assoc, hd]
    · simp only [smul_smul, ← map_mul, MvPolynomial.monomial_mul, one_mul]
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [smul_add] using
      (homogeneousSpan g degree (coefficientDegree m + d)).add_mem hx hy
  | smul r x _ hx =>
    rw [smul_comm]
    exact (homogeneousSpan g degree (coefficientDegree m + d)).smul_mem r hx

/-- Every scalar in the original sphere homogeneous part acts in its full
integer bidegree; no basis completeness hypothesis is used. -/
theorem smul_mem_homogeneousSpan {s t : ℕ} {a : LinE2.E2}
    (ha : a ∈ LinE2.homogeneousPart s t) {d : ℤ × ℤ} {x : M}
    (hx : x ∈ homogeneousSpan g degree d) :
    a • x ∈ homogeneousSpan g degree (((s : ℤ), (t : ℤ)) + d) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨m, hm, rfl⟩ := ha
    have hd : coefficientDegree m = ((s : ℤ), (t : ℤ)) := by
      simp [coefficientDegree, hm]
    exact hd ▸ monomial_smul_mem_homogeneousSpan m hx
  | zero =>
    change (0 : LinE2.E2) • x ∈ _
    convert (homogeneousSpan g degree (((s : ℤ), (t : ℤ)) + d)).zero_mem using 1
    exact zero_smul LinE2.E2 x
  | add a b _ _ ha hb =>
    simpa only [add_smul] using
      (homogeneousSpan g degree (((s : ℤ), (t : ℤ)) + d)).add_mem ha hb
  | smul r a _ ha =>
    simpa only [smul_assoc] using
      (homogeneousSpan g degree (((s : ℤ), (t : ℤ)) + d)).smul_mem r ha

variable {N : Type*} [AddCommGroup N] [Module LinE2.E2 N]
  [Module F2 N] [IsScalarTower F2 LinE2.E2 N]
  {k : Nat} {g' : Fin k → N} {degree' : Fin k → ℤ × ℤ}

/-- A map on the entire modules shifts every homogeneous span whenever its
values on the complete generator family have the specified degrees. -/
theorem map_mem_homogeneousSpan (f : M →ₗ[LinE2.E2] N) (shift : ℤ × ℤ)
    (hg : ∀ i, f (g i) ∈ homogeneousSpan g' degree' (degree i + shift))
    {d : ℤ × ℤ} {x : M} (hx : x ∈ homogeneousSpan g degree d) :
    f x ∈ homogeneousSpan g' degree' (d + shift) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, m, hd, rfl⟩ := hx
    rw [map_smul]
    have h := monomial_smul_mem_homogeneousSpan m (hg i)
    simpa only [← add_assoc, hd] using h
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add] using (homogeneousSpan g' degree' (d + shift)).add_mem hx hy
  | smul r x _ hx =>
    change (f.restrictScalars F2) (r • x) ∈ _
    rw [map_smul]
    exact (homogeneousSpan g' degree' (d + shift)).smul_mem r hx

/-- Descending through all original relations preserves the integer grading
on all elements, using only the original generator images. -/
theorem desc_mem_homogeneousSpan (images : Fin n → N) (relations : List String)
    (hrel : ∀ code ∈ relations, evaluateRelation images code = 0)
    (degree : Fin n → ℤ × ℤ) (shift : ℤ × ℤ)
    (hg : ∀ i, images i ∈ homogeneousSpan g' degree' (degree i + shift))
    {d : ℤ × ℤ} {x : Model n relations}
    (hx : x ∈ homogeneousPart n relations degree d) :
    desc images relations hrel x ∈ homogeneousSpan g' degree' (d + shift) := by
  apply map_mem_homogeneousSpan (desc images relations hrel) shift ?_ hx
  intro i
  simpa only [desc_generator] using hg i

end KIP126.LinModule.Presentation
