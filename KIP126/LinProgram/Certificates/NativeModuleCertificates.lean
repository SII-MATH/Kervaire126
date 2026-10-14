module

public import KIP126.LinProgram.Model.E2.Data
public import KIP126.LinProgram.Model.ModulePresentation.Proofs
public import KIP126.LinProgram.Certificates.SquareDetection.Certificate
public import KIP126.LinProgram.Certificates.NamedElements.ModuleEvaluation
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.CharP.Algebra

import all Init.Data.List.SplitOn.Basic

@[expose] public section


namespace KIP126.LinE2.NativeModuleCertificates
open NamedElementCertificates
open scoped BigOperators
abbrev Expr := ModuleExpressions.Expression

/-- One slot of the full native generator set. -/
def slot {n : Nat} (i : Fin n) (p : Polynomial) : Expr n :=
  fun j => if j = i then p else []

def ceta13125 : Expr 887 :=
  ModuleExpressions.add (slot 12 [[195]])
    (ModuleExpressions.add (slot 2 [[385]]) (slot 0 [[456]]))
def ceta13126 : Expr 887 :=
  ModuleExpressions.add (slot 2 [[385]])
    (ModuleExpressions.add (slot 0 [[456]]) (slot 0 [[67, 107]]))
def cetaInput : Expr 887 := slot 12 [[195]]
def cetaOutput : Expr 887 := slot 0 [[67, 107]]
def cetaWitness : List Term := [⟨0, [[]]⟩, ⟨1, [[]]⟩]

def cw13675 : Expr 844 :=
  ModuleExpressions.add (slot 240 [[3]])
    (ModuleExpressions.add (slot 2 [[438]]) (slot 2 [[0, 0, 418]]))
def cwInput : Expr 844 := slot 240 [[3]]
def cwOutput : Expr 844 := ModuleExpressions.add (slot 2 [[438]]) (slot 2 [[0, 0, 418]])
def cwWitness : List Term := [⟨0, [[]]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem ceta_check :
    ModuleExpressions.check [ceta13125, ceta13126] cetaInput cetaOutput cetaWitness = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem cw_check :
    ModuleExpressions.check [cw13675] cwInput cwOutput cwWitness = true := by
  decide

theorem evaluate_slot {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (v : Nat → R) (g : Fin n → M) (i : Fin n) (p : Polynomial) :
    ModuleExpressions.evaluate v g (slot i p) = NamedElementCertificates.evaluate v p • g i := by
  classical
  unfold ModuleExpressions.evaluate
  rw [Finset.sum_eq_single i]
  · simp [slot]
  · intro j _ h
    simp [slot, h, NamedElementCertificates.evaluate]
  · simp

/-- Scalar extension is through the original quotient projection. This avoids
requiring a new nontriviality or characteristic instance on the quotient. -/
theorem check_sound_projection {M : Type*} [AddCommGroup M] [Module E2 M]
    (v : Nat → Poly) (g : Fin n → M) (rels : List (Expr n))
    (input output : Expr n) (terms : List Term)
    (hc : ModuleExpressions.check rels input output terms = true)
    (hr : ∀ r ∈ rels, ModuleExpressions.evaluate (fun i => projection (v i)) g r = 0) :
    ModuleExpressions.evaluate (fun i => projection (v i)) g input =
      ModuleExpressions.evaluate (fun i => projection (v i)) g output := by
  letI : Module Poly M := Module.compHom M projection
  letI : CharP Poly 2 :=
    charP_of_injective_ringHom (MvPolynomial.C_injective Generator KIP126.Core.Algebra.F2) 2
  have he (e : Expr n) : ModuleExpressions.evaluate v g e =
      ModuleExpressions.evaluate (fun i => projection (v i)) g e := by
    unfold ModuleExpressions.evaluate
    apply Finset.sum_congr rfl
    intro i _
    change projection (NamedElementCertificates.evaluate v (e i)) • g i = _
    congr 1
    simp [NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
      map_list_sum, map_list_prod, List.map_map, Function.comp_def]
    rfl
  rw [← he input, ← he output]
  apply ModuleExpressions.check_sound_evaluate v g rels input output terms hc
  intro r h
  rw [he]
  exact hr r h

noncomputable def nativeVariable (i : Nat) : Poly :=
  if h : i < RawData.generatorCount then MvPolynomial.X ⟨i, h⟩ else 0
noncomputable def nativeScalar (i : Nat) : E2 := projection (nativeVariable i)

theorem nativeScalar_eq_generator (i : Nat) (h : i < RawData.generatorCount) :
    nativeScalar i = generator ⟨i, h⟩ := by
  simp [nativeScalar, nativeVariable, generator, h]

theorem ceta_evaluate {M : Type*} [AddCommGroup M] [Module E2 M]
    (g : Fin 887 → M)
    (hr : ∀ r ∈ [ceta13125, ceta13126], ModuleExpressions.evaluate nativeScalar g r = 0) :
    ModuleExpressions.evaluate nativeScalar g cetaInput =
      ModuleExpressions.evaluate nativeScalar g cetaOutput :=
  check_sound_projection nativeVariable g _ _ _ _ ceta_check hr

theorem cw_evaluate {M : Type*} [AddCommGroup M] [Module E2 M]
    (g : Fin 844 → M)
    (hr : ∀ r ∈ [cw13675], ModuleExpressions.evaluate nativeScalar g r = 0) :
    ModuleExpressions.evaluate nativeScalar g cwInput =
      ModuleExpressions.evaluate nativeScalar g cwOutput :=
  check_sound_projection nativeVariable g _ _ _ _ cw_check hr

theorem ceta_native_equality {M : Type*} [AddCommGroup M] [Module E2 M]
    (g : Fin 887 → M)
    (hr : ∀ r ∈ [ceta13125, ceta13126], ModuleExpressions.evaluate nativeScalar g r = 0) :
    nativeScalar 195 • g 12 = (nativeScalar 67 * nativeScalar 107) • g 0 := by
  have h := ceta_evaluate g hr
  simpa only [cetaInput, cetaOutput, evaluate_slot, NamedElementCertificates.evaluate,
    NamedElementCertificates.evaluateMonomial, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] using h

theorem cw_native_equality {M : Type*} [AddCommGroup M] [Module E2 M]
    (g : Fin 844 → M)
    (hr : ∀ r ∈ [cw13675], ModuleExpressions.evaluate nativeScalar g r = 0) :
    nativeScalar 3 • g 240 = nativeScalar 438 • g 2 +
      (nativeScalar 0 ^ 2 * nativeScalar 418) • g 2 := by
  have h := cw_evaluate g hr
  simpa only [cwInput, cwOutput, ModuleExpressions.evaluate_add, evaluate_slot,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    List.sum_cons, List.sum_nil, mul_one, add_zero, pow_two, mul_assoc] using h

theorem ceta_generator_equality {M : Type*} [AddCommGroup M] [Module E2 M]
    (g : Fin 887 → M)
    (hr : ∀ r ∈ [ceta13125, ceta13126], ModuleExpressions.evaluate nativeScalar g r = 0) :
    generator ⟨195, by decide⟩ • g 12 =
      (generator ⟨67, by decide⟩ * generator ⟨107, by decide⟩) • g 0 := by
  simpa only [nativeScalar_eq_generator 195 (by decide),
    nativeScalar_eq_generator 67 (by decide), nativeScalar_eq_generator 107 (by decide)]
    using ceta_native_equality g hr

theorem cw_generator_equality {M : Type*} [AddCommGroup M] [Module E2 M]
    (g : Fin 844 → M)
    (hr : ∀ r ∈ [cw13675], ModuleExpressions.evaluate nativeScalar g r = 0) :
    generator ⟨3, by decide⟩ • g 240 = generator ⟨438, by decide⟩ • g 2 +
      (generator ⟨0, by decide⟩ ^ 2 * generator ⟨418, by decide⟩) • g 2 := by
  simpa only [nativeScalar_eq_generator 3 (by decide),
    nativeScalar_eq_generator 438 (by decide), nativeScalar_eq_generator 0 (by decide),
    nativeScalar_eq_generator 418 (by decide)] using cw_native_equality g hr

open NamedElementCertificates
open KIP126.LinModule

attribute [local cbv_eval] SquareDetection.splitOn_comma
  SquareDetection.splitOn_semicolon SquareDetection.toNat?_eq_chars

theorem projection_relation_words (n : Nat) (rels : List String) (code : String) :
    Presentation.projection n rels (Presentation.relationVector n code) =
      (((code.splitOn ";").map fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)).map
        (Presentation.evaluatePowers (Presentation.generator n rels))).sum := by
  simp only [Presentation.relationVector, map_list_sum, List.map_map, Function.comp_def, Presentation.monomialVector,
    Presentation.projection_ofPowers]

theorem ceta13125_projection (rels : List String) :
    ModuleExpressions.evaluate nativeScalar (Presentation.generator 887 rels) ceta13125 =
      Presentation.projection 887 rels (Presentation.relationVector 887 "195,1,12;385,1,2;456,1,0") := by
  have hp : (("195,1,12;385,1,2;456,1,0".splitOn ";").map
      fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
        [[195,1,12], [385,1,2], [456,1,0]] := by cbv
  rw [projection_relation_words, hp]
  simp [ceta13125, ModuleExpressions.evaluate_add, evaluate_slot,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, RawData.generatorCount,
    nativeScalar_eq_generator 195 (by decide), nativeScalar_eq_generator 385 (by decide),
    nativeScalar_eq_generator 456 (by decide)]

theorem ceta13126_projection (rels : List String) :
    ModuleExpressions.evaluate nativeScalar (Presentation.generator 887 rels) ceta13126 =
      Presentation.projection 887 rels (Presentation.relationVector 887 "385,1,2;456,1,0;67,1,107,1,0") := by
  have hp : (("385,1,2;456,1,0;67,1,107,1,0".splitOn ";").map
      fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
        [[385,1,2], [456,1,0], [67,1,107,1,0]] := by cbv
  rw [projection_relation_words, hp]
  simp [ceta13126, ModuleExpressions.evaluate_add, evaluate_slot,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, RawData.generatorCount, mul_smul,
    nativeScalar_eq_generator 385 (by decide), nativeScalar_eq_generator 456 (by decide),
    nativeScalar_eq_generator 67 (by decide), nativeScalar_eq_generator 107 (by decide)]

theorem cw13675_projection (rels : List String) :
    ModuleExpressions.evaluate nativeScalar (Presentation.generator 844 rels) cw13675 =
      Presentation.projection 844 rels (Presentation.relationVector 844 "3,1,240;438,1,2;0,2,418,1,2") := by
  have hp : (("3,1,240;438,1,2;0,2,418,1,2".splitOn ";").map
      fun w => (w.splitOn ",").map (fun a => a.toNat?.getD 0)) =
        [[3,1,240], [438,1,2], [0,2,418,1,2]] := by cbv
  rw [projection_relation_words, hp]
  simp [cw13675, ModuleExpressions.evaluate_add, evaluate_slot,
    NamedElementCertificates.evaluate, NamedElementCertificates.evaluateMonomial,
    Presentation.evaluatePowers, RawData.generatorCount, mul_smul, pow_two,
    nativeScalar_eq_generator 3 (by decide), nativeScalar_eq_generator 438 (by decide),
    nativeScalar_eq_generator 0 (by decide), nativeScalar_eq_generator 418 (by decide)]

theorem ceta_quotient_equality (rels : List String)
    (h13125 : "195,1,12;385,1,2;456,1,0" ∈ rels)
    (h13126 : "385,1,2;456,1,0;67,1,107,1,0" ∈ rels) :
    generator ⟨195, by decide⟩ • Presentation.generator 887 rels 12 =
      (generator ⟨67, by decide⟩ * generator ⟨107, by decide⟩) • Presentation.generator 887 rels 0 := by
  apply ceta_generator_equality
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [ceta13125_projection]
    exact Presentation.native_relation_zero _ _ _ h13125
  · rw [ceta13126_projection]
    exact Presentation.native_relation_zero _ _ _ h13126

theorem cw_quotient_equality (rels : List String)
    (h13675 : "3,1,240;438,1,2;0,2,418,1,2" ∈ rels) :
    generator ⟨3, by decide⟩ • Presentation.generator 844 rels 240 =
      generator ⟨438, by decide⟩ • Presentation.generator 844 rels 2 +
      (generator ⟨0, by decide⟩ ^ 2 * generator ⟨418, by decide⟩) • Presentation.generator 844 rels 2 := by
  apply cw_generator_equality
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  rw [cw13675_projection]
  exact Presentation.native_relation_zero _ _ _ h13675

end KIP126.LinE2.NativeModuleCertificates
