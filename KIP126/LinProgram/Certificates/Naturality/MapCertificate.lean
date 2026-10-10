import KIP126.LinProgram.Certificates.ModuleMaps.CetaToSphere.Grading

/-! A finite certificate for evaluation under the complete native Ceta-to-sphere
map graph. Its soundness theorem is about evaluation of a free-module word;
constructing a map on the full quotient still requires every original relation.
The record IDs locate transcribed rows; the exporter checks them against the
pinned databases, and separate Lean lemmas bind the sphere catalogue rows. -/
namespace KIP126.LinModule.NaturalityMapCertificate
open KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates
open KIP126.LinModule.NativeMapCertificates NamedElementCertificates

structure BasisRecord where
  id : Nat
  s : Nat
  t : Nat
  localIndex : Nat
  code : String
  deriving Repr, DecidableEq

structure Certificate where
  source : BasisRecord
  target : BasisRecord
  generatorId : Nat
  imageCode : String
  witness : List NamedElementCertificates.Term

/-- Parse with the same semantics as the existing native module presentation.
The checker additionally rejects malformed decimal fields. -/
def word (c : Certificate) : List Nat :=
  (c.source.code.splitOn ",").map (fun a => a.toNat?.getD 0)

def images (i : Ceta.Generator) : Polynomial :=
  parseNativeCode (RawData.Maps.CetaToSphere.imageCode i)

noncomputable def generatorImage (i : Ceta.Generator) : E2 :=
  nativeImage (RawData.Maps.CetaToSphere.imageCode i)

/-- A strict native module word has paired coefficient IDs/exponents followed
by one module-generator ID. All indices refer to the complete original data. -/
def wordDegree : List Nat → Option (ℤ × ℤ)
  | [j] => if h : j < RawData.Ceta.generatorCount then
      some (Ceta.generatorDegree ⟨j,h⟩) else none
  | i :: a :: rest => if i < LinE2.RawData.generatorCount then
      (wordDegree rest).map (fun d => a • nativeVariableDegree i + d) else none
  | [] => none

/-- Reject malformed decimal fields, unpaired exponents and invalid coefficient
indices before using the existing scalar parser. -/
def validScalarWord : List Nat → Bool
  | [] => true
  | i :: _ :: rest => i < LinE2.RawData.generatorCount && validScalarWord rest
  | [_] => false

/-- This certificate format targets a recorded nonempty basis monomial, not
an arbitrary polynomial or the empty native zero-image encoding. In particular,
its target uses the same monomial convention as `basisValue`. -/
def validBasisCode (code : String) : Bool :=
  code != "" && !code.contains ';' &&
    (code.splitOn ",").all (fun a => a.toNat?.isSome) &&
    validScalarWord ((code.splitOn ",").map (fun a => a.toNat?.getD 0))

def check (c : Certificate) : Bool :=
  (if h : c.generatorId < RawData.Ceta.generatorCount then
    c.imageCode == RawData.Maps.CetaToSphere.imageCode ⟨c.generatorId,h⟩
   else false) &&
  (c.source.code.splitOn ",").all (fun a => a.toNat?.isSome) &&
  (word c).getLast? == some c.generatorId &&
  wordDegree (word c) == some ((c.source.s : ℤ), (c.source.t : ℤ)) &&
  c.source.s == c.target.s && c.source.t == c.target.t + 2 &&
  validBasisCode c.target.code &&
  homogeneousPolynomialCheck (parseNativeCode c.target.code)
    ((c.target.s : ℤ), (c.target.t : ℤ)) &&
  NamedElementCertificates.check [] (substituteWord images (word c))
    (parseNativeCode c.target.code) c.witness

/-- A successful finite check proves the evaluation equation in the existing
sphere quotient. It assumes neither a Ceta quotient map nor an actual spectrum
comparison. No relation is needed in the two selected certificates. -/
theorem check_sound (c : Certificate) (h : check c = true) :
    Presentation.evaluatePowers generatorImage (word c) = nativeImage c.target.code := by
  have hc : NamedElementCertificates.check [] (substituteWord images (word c))
      (parseNativeCode c.target.code) c.witness = true :=
    by
      simp only [check, Bool.and_eq_true] at h
      exact h.2
  letI : CharP Poly 2 :=
    charP_of_injective_ringHom
      (MvPolynomial.C_injective Generator KIP126.Core.Algebra.F2) 2
  have he := NamedElementCertificates.check_sound_evaluate nativeVariable []
    (substituteWord images (word c)) (parseNativeCode c.target.code) c.witness hc
    (by simp)
  have hp := congrArg projection he
  rw [projection_evaluate, projection_evaluate, evaluate_substituteWord,
    evaluate_parseNativeCode] at hp
  change Presentation.evaluatePowers
    (fun i : Ceta.Generator => nativeImage (RawData.Maps.CetaToSphere.imageCode i))
    (word c) = nativeImage c.target.code
  simpa only [images, evaluate_parseNativeCode] using hp

/-- The same equation for a map from the complete Ceta quotient, conditional
on the original full relation obligation. No finite-degree replacement or
smaller relation family is used. -/
theorem check_sound_desc (c : Certificate) (h : check c = true)
    (hrel : ∀ code ∈ RawData.Ceta.relations,
      Presentation.evaluateRelation generatorImage code = 0) :
    Presentation.desc generatorImage RawData.Ceta.relations hrel
      (Presentation.projection RawData.Ceta.generatorCount RawData.Ceta.relations
        (Presentation.monomialVector RawData.Ceta.generatorCount c.source.code)) =
      nativeImage c.target.code := by
  rw [Presentation.desc_monomialVector]
  exact check_sound c h

end KIP126.LinModule.NaturalityMapCertificate
