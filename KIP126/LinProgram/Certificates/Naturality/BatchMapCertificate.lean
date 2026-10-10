import KIP126.LinProgram.Certificates.Naturality.MapCertificate
import KIP126.LinProgram.Model.BasisCatalogue.Data

/-! Batch certificates for free-word evaluations under the complete native
Ceta-to-sphere graph. An empty target list means zero; nonempty lists describe
sums of strictly encoded basis monomials. The underlying complete quotients,
generator graphs and the older two-word certificate API are unchanged. -/
namespace KIP126.LinModule.BatchMapCertificate
open KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates
open NativeMapCertificates NamedElementCertificates
open NaturalityMapCertificate (BasisRecord images generatorImage wordDegree validBasisCode)

structure Entry where
  source : BasisRecord
  targetS : Nat
  targetT : Nat
  targets : List BasisRecord
  witness : List NamedElementCertificates.Term

def word (e : Entry) : List Nat :=
  (e.source.code.splitOn ",").map (fun a => a.toNat?.getD 0)

def basisRow (r : BasisRecord) : BasisRow := ⟨r.s, r.t, r.localIndex, r.code⟩

def targetPolynomial (e : Entry) : Polynomial :=
  e.targets.flatMap (fun r => parseMonomial r.code)

noncomputable def targetValue (e : Entry) : E2 :=
  (e.targets.map (fun r => basisValue (basisRow r))).sum

def check (relationCodes : List String) (e : Entry) : Bool :=
  (e.source.code.splitOn ",").all (fun a => a.toNat?.isSome) &&
  wordDegree (word e) == some ((e.source.s : ℤ), (e.source.t : ℤ)) &&
  e.source.s == e.targetS && e.source.t == e.targetT + 2 &&
  e.targets.all (fun r => validBasisCode r.code && r.s == e.targetS && r.t == e.targetT &&
    homogeneousPolynomialCheck (parseMonomial r.code) ((r.s : ℤ), (r.t : ℤ))) &&
  NamedElementCertificates.check (relationCodes.map parseNativeCode)
    (substituteWord images (word e)) (targetPolynomial e) e.witness

/-- The polynomial target parser agrees with the existing sphere basis-value
semantics, including the explicit empty-list convention for zero. -/
theorem evaluate_targetPolynomial (e : Entry) :
    evaluate nativeScalar (targetPolynomial e) = targetValue e := by
  rw [← projection_evaluate]
  simp only [targetPolynomial, evaluate_flatMap, evaluate_parseMonomial,
    targetValue, basisValue, basisRow, map_list_sum, List.map_map, Function.comp_def]

/-- Generic finite relation witnesses are sound in the unchanged sphere
quotient. Only the selected relation evaluations are hypotheses here; the
concrete batch proves them from the archived relation catalogue. -/
theorem check_sound (relationCodes : List String) (e : Entry)
    (hc : check relationCodes e = true)
    (hr : ∀ code ∈ relationCodes, nativeImage code = 0) :
    Presentation.evaluatePowers generatorImage (word e) = targetValue e := by
  have hc' : NamedElementCertificates.check (relationCodes.map parseNativeCode)
      (substituteWord images (word e)) (targetPolynomial e) e.witness = true := by
    simp only [check, Bool.and_eq_true] at hc
    exact hc.2
  letI : CharP Poly 2 :=
    charP_of_injective_ringHom
      (MvPolynomial.C_injective Generator KIP126.Core.Algebra.F2) 2
  obtain ⟨w, _, hcoeff⟩ := NamedElementCertificates.check_sound _ _ _ _ hc'
  have he := evaluate_coefficients nativeVariable
    (substituteWord images (word e) ++ targetPolynomial e)
    (combination (relationCodes.map parseNativeCode) w) hcoeff
  have hp := congrArg projection he
  rw [projection_evaluate, projection_evaluate, evaluate_append] at hp
  have hr' : ∀ p ∈ relationCodes.map parseNativeCode, evaluate nativeScalar p = 0 := by
    intro p hp
    obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp hp
    exact (evaluate_parseNativeCode code).trans (hr code hcode)
  rw [evaluate_combination nativeScalar _ _ hr'] at hp
  have hz : evaluate nativeScalar (targetPolynomial e) +
      evaluate nativeScalar (targetPolynomial e) = 0 := by
    rw [← projection_evaluate, ← map_add, CharTwo.add_self_eq_zero, map_zero]
  have ht := congrArg (fun z => z + evaluate nativeScalar (targetPolynomial e)) hp
  have heq : evaluate nativeScalar (substituteWord images (word e)) =
      evaluate nativeScalar (targetPolynomial e) := by
    simpa only [add_assoc, hz, add_zero, zero_add] using ht
  rw [evaluate_substituteWord, evaluate_targetPolynomial] at heq
  change Presentation.evaluatePowers
    (fun i : Ceta.Generator => nativeImage (RawData.Maps.CetaToSphere.imageCode i))
    (word e) = targetValue e
  simpa only [images, evaluate_parseNativeCode] using heq

/-- Descent uses every relation of the complete original Ceta presentation.
The finite batch never replaces that presentation with a truncated module. -/
theorem check_sound_desc (relationCodes : List String) (e : Entry)
    (hc : check relationCodes e = true)
    (hr : ∀ code ∈ relationCodes, nativeImage code = 0)
    (hrel : ∀ code ∈ RawData.Ceta.relations,
      Presentation.evaluateRelation generatorImage code = 0) :
    Presentation.desc generatorImage RawData.Ceta.relations hrel
      (Ceta.monomial e.source.code) = targetValue e := by
  rw [Ceta.monomial, Presentation.desc_monomialVector]
  exact check_sound relationCodes e hc hr

end KIP126.LinModule.BatchMapCertificate
