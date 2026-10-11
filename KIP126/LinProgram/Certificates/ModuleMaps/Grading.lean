module

public import KIP126.LinProgram.Model.ModulePresentation.Grading.Proofs
public import KIP126.LinProgram.Certificates.ModuleMaps.Support

@[expose] public section


namespace KIP126.LinModule.NativeMapCertificates
open KIP126.Core.Algebra KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates
open KIP126.LinModule.Presentation NamedElementCertificates

noncomputable def coefficientPart (d : ℤ × ℤ) : Submodule F2 E2 :=
  homogeneousSpan (fun _ : Fin 1 => (1 : E2)) (fun _ => (0 : ℤ × ℤ)) d

theorem coefficientPart_nat (s t : ℕ) :
    coefficientPart ((s : ℤ), (t : ℤ)) = LinE2.homogeneousPart s t := by
  unfold coefficientPart homogeneousSpan LinE2.homogeneousPart
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, add_zero, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨i, m, hm, hx⟩
    refine ⟨m, ?_, hx⟩
    simpa only [coefficientDegree, Prod.mk.injEq, Nat.cast_inj, Prod.ext_iff] using hm
  · rintro ⟨m, hm, hx⟩
    exact ⟨0, m, by simp [coefficientDegree, hm], hx⟩

def nativeVariableDegree (i : Nat) : ℤ × ℤ :=
  if h : i < RawData.generatorCount then
    ((generatorDegree ⟨i, h⟩).1, (generatorDegree ⟨i, h⟩).2) else 0

def nativeMonomialDegree (m : Monomial) : ℤ × ℤ :=
  (m.map nativeVariableDegree).sum

def homogeneousPolynomialCheck (p : Polynomial) (d : ℤ × ℤ) : Bool :=
  p.all fun m => nativeMonomialDegree m == d

theorem nativeMonomial_mem (m : Monomial) :
    evaluateMonomial nativeScalar m ∈ coefficientPart (nativeMonomialDegree m) := by
  induction m with
  | nil =>
    have h := generator_mem_homogeneousSpan
      (g := fun _ : Fin 1 => (1 : E2)) (degree := fun _ => (0 : ℤ × ℤ)) 0
    simpa only [evaluateMonomial, List.map_nil, List.prod_nil, nativeMonomialDegree,
      List.sum_nil, coefficientPart] using h
  | cons i m ih =>
    simp only [evaluateMonomial, List.map_cons, List.prod_cons] at *
    simp only [nativeMonomialDegree, List.map_cons, List.sum_cons]
    by_cases hi : i < RawData.generatorCount
    · rw [nativeScalar_eq_generator i hi]
      have h := smul_mem_homogeneousSpan (generator_mem ⟨i, hi⟩) ih
      simpa only [nativeVariableDegree, dif_pos hi, smul_eq_mul,
        nativeMonomialDegree, coefficientPart] using h
    · simp only [nativeScalar, nativeVariable, dif_neg hi, map_zero, zero_mul]
      exact (coefficientPart _).zero_mem

theorem homogeneousPolynomialCheck_sound (p : Polynomial) (d : ℤ × ℤ)
    (h : homogeneousPolynomialCheck p d = true) :
    evaluate nativeScalar p ∈ coefficientPart d := by
  unfold evaluate
  apply list_sum_mem
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  have hd : nativeMonomialDegree m = d := by
    simpa using (List.all_eq_true.mp h) m hm
  exact hd ▸ nativeMonomial_mem m

end KIP126.LinModule.NativeMapCertificates
