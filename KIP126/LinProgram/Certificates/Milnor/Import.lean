import KIP126.LinProgram.Certificates.Milnor.Basic

namespace MilnorCertificates

structure Bundle where
  left : Polynomial
  right : Polynomial
  output : Polynomial
  certificate : Certificate
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Strict JSON roundtrip rejects duplicate/unknown keys and noncanonical syntax. -/
def parse (text : String) : Except String Bundle := do
  let json ← Lean.Json.parse text
  let b : Bundle ← Lean.fromJson? json
  if (Lean.toJson b).compress != text then
    throw "noncanonical JSON or duplicate/unknown field"
  return b

def decode (text : String) : Except String Bundle :=
  match parse text with
  | .error e => .error e
  | .ok b =>
    if check b.certificate.window b.left b.right b.output b.certificate then .ok b
    else .error (String.intercalate "; " (diagnose b.certificate.window b.left b.right b.output b.certificate))

theorem decode_sound (text : String) (b : Bundle) (h : decode text = .ok b) :
    IsMilnorProduct b.certificate.window b.left b.right b.output := by
  unfold decode at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hc
  cases h
  apply check_sound
  exact hc

/- JSON text is parsed during elaboration into data; `milnor_cert` still proves
the checker equality in the kernel. No parser result is an axiom. -/
open Lean Elab Term
elab "milnor_json% " text:str : term => do
  match decode text.getString with
  | .error e => throwError "Milnor certificate: {e}"
  | .ok b =>
    let stx ← `(term| (⟨$(quote b.left), $(quote b.right), $(quote b.output),
      ⟨$(quote b.certificate.version),
        ⟨$(quote b.certificate.window.rank), $(quote b.certificate.window.degree)⟩,
        $(quote b.certificate.expansions)⟩⟩ : MilnorCertificates.Bundle))
    elabTerm stx none

/-- File contents become explicit constructor data; the theorem must still run
the kernel checker. Paths are relative to the Lean invocation directory. -/
elab "milnor_bundle% " path:str : term => do
  let text ← IO.FS.readFile path.getString
  let stx ← `(term| milnor_json% $(quote text.trimAscii.toString))
  elabTerm stx none

end MilnorCertificates
