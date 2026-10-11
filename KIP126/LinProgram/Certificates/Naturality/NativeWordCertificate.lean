module

public import KIP126.LinProgram.Certificates.Naturality.BatchMapCertificate
public import KIP126.LinProgram.Certificates.SquareDetection.Native

@[expose] public section


/-! Interpret the original finite relation witnesses in the untruncated algebra.
The source is a free native word. The old Ceta quotient is a module over the
truncated algebra and is not silently made into a module over this new target. -/
namespace KIP126.LinModule.NativeWordCertificate
open KIP126.Core.Algebra KIP126.LinE2 NativeModuleCertificates
open NativeMapCertificates NamedElementCertificates BatchMapCertificate
noncomputable section

def scalar (i : Nat) : NativeAlgebra := nativeProjection (nativeVariable i)
def image (code : String) : NativeAlgebra :=
  if code = "" then 0 else nativeProjection (relationPolynomial code)
def generatorImage (i : Ceta.Generator) : NativeAlgebra :=
  image (RawData.Maps.CetaToSphere.imageCode i)

/-- Identical free-word convention, now evaluated in the untruncated algebra. -/
def evaluatePowers {n : Nat} (g : Fin n → NativeAlgebra) : List Nat → NativeAlgebra
  | [j] => if h : j < n then g ⟨j,h⟩ else 0
  | i :: a :: rest => if h : i < LinE2.RawData.generatorCount then
      nativeGenerator ⟨i,h⟩ ^ a * evaluatePowers g rest else 0
  | [] => 0

def targetValue (e : Entry) : NativeAlgebra :=
  (e.targets.map (fun r => nativeProjection (monomialOfString r.code))).sum

theorem evaluate_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (v : Nat → R) (p : Polynomial) :
    f (evaluate v p) = evaluate (fun i => f (v i)) p := by
  simp [evaluate, evaluateMonomial, map_list_sum, map_list_prod,
    List.map_map, Function.comp_def]
  rfl

theorem projection_evaluate (p : Polynomial) :
    nativeProjection (evaluate nativeVariable p) = evaluate scalar p :=
  evaluate_map nativeProjection.toRingHom nativeVariable p

theorem evaluate_parse_code (code : String) :
    evaluate scalar (parseNativeCode code) = image code := by
  by_cases h : code = ""
  · simp [parseNativeCode, image, h, evaluate]
  · rw [← projection_evaluate]
    simp only [parseNativeCode, image, if_neg h, evaluate_flatMap,
      evaluate_parseMonomial, relationPolynomial]

theorem scalar_eq_generator (i : Nat) (hi : i < LinE2.RawData.generatorCount) :
    scalar i = nativeGenerator ⟨i,hi⟩ := by simp [scalar, nativeVariable, nativeGenerator, hi]

theorem evaluate_substitute (g : Fin n → Polynomial) (w : List Nat) :
    evaluate scalar (substituteWord g w) =
      evaluatePowers (fun j => evaluate scalar (g j)) w := by
  induction w using Presentation.ofPowers.induct n with
  | case1 j hj => simp [substituteWord, evaluatePowers, hj]
  | case2 j hj => simp [substituteWord, evaluatePowers, hj, evaluate]
  | case3 i a rest hi ih =>
    simp only [substituteWord, evaluatePowers, dif_pos hi, if_pos hi, evaluate_multiply, ih]
    simp [evaluate, evaluateMonomial, scalar_eq_generator i hi]
  | case4 i a rest hi => simp [substituteWord, evaluatePowers, hi, evaluate]
  | case5 => simp [substituteWord, evaluatePowers, evaluate]

theorem evaluate_target (e : Entry) :
    evaluate scalar (targetPolynomial e) = targetValue e := by
  rw [← projection_evaluate]
  simp only [targetPolynomial, evaluate_flatMap, evaluate_parseMonomial,
    targetValue, map_list_sum, List.map_map, Function.comp_def]

/-- The same executable witness is interpreted directly in A. The only
relation premise is membership in the complete unchanged original catalogue. -/
theorem check_sound_evaluate (relationCodes : List String) (e : Entry)
    (hc : BatchMapCertificate.check relationCodes e = true)
    (hm : ∀ code ∈ relationCodes, code ∈ LinE2.RawData.relations) :
    evaluatePowers generatorImage (word e) = targetValue e := by
  letI : Nontrivial NativeAlgebra := SquareDetection.nativeAlgebra_nontrivial
  letI : CharP NativeAlgebra 2 :=
    CharP.of_ringHom_of_ne_zero (algebraMap F2 NativeAlgebra) 2 (by decide)
  have hc' : NamedElementCertificates.check (relationCodes.map parseNativeCode)
      (substituteWord NaturalityMapCertificate.images (word e)) (targetPolynomial e) e.witness = true := by
    simp only [BatchMapCertificate.check, Bool.and_eq_true] at hc
    exact hc.2
  have hr : ∀ p ∈ relationCodes.map parseNativeCode, evaluate scalar p = 0 := by
    intro p hp
    obtain ⟨code, hcode, rfl⟩ := List.mem_map.mp hp
    rw [evaluate_parse_code]
    unfold image
    split
    · rfl
    · exact native_csv_relation_zero code (hm code hcode)
  have h := NamedElementCertificates.check_sound_evaluate scalar _ _ _ _ hc' hr
  rw [evaluate_substitute, evaluate_target] at h
  simp only [NaturalityMapCertificate.images, evaluate_parse_code] at h
  exact h

@[simp] theorem truncate_image (code : String) : truncate (image code) = nativeImage code := by
  simp only [image, nativeImage]
  split <;> simp only [map_zero, truncate_projection]

@[simp] theorem truncate_generatorImage (i : Ceta.Generator) :
    truncate (generatorImage i) = NaturalityMapCertificate.generatorImage i := truncate_image _

theorem truncate_evaluatePowers (g : Fin n → NativeAlgebra) (w : List Nat) :
    truncate (evaluatePowers g w) = Presentation.evaluatePowers (fun i => truncate (g i)) w := by
  induction w using Presentation.ofPowers.induct n with
  | case1 j hj => simp [evaluatePowers, Presentation.evaluatePowers, hj]
  | case2 j hj => simp [evaluatePowers, Presentation.evaluatePowers, hj]
  | case3 i a rest hi ih =>
    simp only [evaluatePowers, Presentation.evaluatePowers, dif_pos hi,
      map_mul, map_pow, truncate_generator, ih, smul_eq_mul]
  | case4 i a rest hi => simp [evaluatePowers, Presentation.evaluatePowers, hi]
  | case5 => simp [evaluatePowers, Presentation.evaluatePowers]

@[simp] theorem truncate_targetValue (e : Entry) :
    truncate (targetValue e) = BatchMapCertificate.targetValue e := by
  simp only [targetValue, map_list_sum, List.map_map, Function.comp_def,
    truncate_projection, BatchMapCertificate.targetValue, basisValue, basisRow]
end
end KIP126.LinModule.NativeWordCertificate
