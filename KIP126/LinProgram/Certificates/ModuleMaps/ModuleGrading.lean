module

public import KIP126.LinProgram.Certificates.ModuleMaps.Grading
public import KIP126.LinProgram.Certificates.ModuleMaps.ModuleTerms

@[expose] public section


/-! Sound degree checks for native module terms, in the complete unchanged
target quotient and with the complete original sphere coefficient algebra. -/
set_option backward.isDefEq.respectTransparency false
namespace KIP126.LinModule.NativeMapCertificates
open KIP126.Core.Algebra KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates
open KIP126.LinModule.Presentation NamedElementCertificates
open KIP126.LinE2.NativeModuleCertificates.Support

variable {M : Type*} [AddCommGroup M] [Module LinE2.E2 M]
  [Module F2 M] [IsScalarTower F2 LinE2.E2 M]
  {n : Nat} {g : Fin n → M} {degree : Fin n → ℤ × ℤ}

theorem nativeMonomial_smul_mem (m : Monomial)
    {d : ℤ × ℤ} {x : M} (hx : x ∈ homogeneousSpan g degree d) :
    evaluateMonomial nativeScalar m • x ∈
      homogeneousSpan g degree (nativeMonomialDegree m + d) := by
  induction m with
  | nil =>
    simpa only [evaluateMonomial, List.map_nil, List.prod_nil,
      nativeMonomialDegree, List.sum_nil, zero_add, one_smul] using hx
  | cons i m ih =>
    simp only [evaluateMonomial, List.map_cons, List.prod_cons, mul_smul] at *
    simp only [nativeMonomialDegree, List.map_cons, List.sum_cons]
    by_cases hi : i < LinE2.RawData.generatorCount
    · rw [nativeScalar_eq_generator i hi]
      have h := smul_mem_homogeneousSpan (LinE2.generator_mem ⟨i, hi⟩) ih
      simpa only [nativeVariableDegree, dif_pos hi, nativeMonomialDegree,
        add_assoc] using h
    · simp only [nativeScalar, nativeVariable, dif_neg hi, map_zero]
      change (0 : E2) • ((m.map nativeScalar).prod • x) ∈ _
      have hz : (0 : E2) • ((m.map nativeScalar).prod • x) = (0 : M) :=
        Module.zero_smul _
      exact hz ▸ (homogeneousSpan g degree _).zero_mem

def homogeneousModuleTermsCheck (ts : ModuleTerms n)
    (degree : Fin n → ℤ × ℤ) (d : ℤ × ℤ) : Bool :=
  ts.all fun t => t.2.all fun m => nativeMonomialDegree m + degree t.1 == d

/-- The checker considers every monomial in every term, with the actual
degree of its original target generator. No support bound is assumed. -/
theorem homogeneousModuleTermsCheck_sound (ts : ModuleTerms n)
    (h : homogeneousModuleTermsCheck ts degree d = true) :
    ModuleExpressions.evaluate nativeScalar g (termsExpression ts) ∈
      homogeneousSpan g degree d := by
  induction ts with
  | nil =>
    simpa only [termsExpression, ModuleExpressions.evaluate_zero] using
      (homogeneousSpan g degree d).zero_mem
  | cons t ts ih =>
    rcases t with ⟨j,p⟩
    simp only [homogeneousModuleTermsCheck, List.all_cons, Bool.and_eq_true] at h
    simp only [termsExpression, ModuleExpressions.evaluate_add, evaluate_slot]
    apply (homogeneousSpan g degree d).add_mem ?_ (ih h.2)
    unfold NamedElementCertificates.evaluate
    rw [List.sum_smul]
    apply list_sum_mem
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hz
    have hd : nativeMonomialDegree m + degree j = d := by
      simpa using (List.all_eq_true.mp h.1) m hm
    exact hd ▸ nativeMonomial_smul_mem m (generator_mem_homogeneousSpan j)

end KIP126.LinModule.NativeMapCertificates
