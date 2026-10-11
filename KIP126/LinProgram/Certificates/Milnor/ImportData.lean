module

public import KIP126.LinProgram.Certificates.Milnor.Basic

@[expose] public section


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

end MilnorCertificates
