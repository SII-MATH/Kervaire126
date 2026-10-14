module

public import KIP126.LinProgram.Certificates.Milnor.ImportData
public meta import KIP126.LinProgram.Certificates.Milnor.ImportData

@[expose] public section

/-! Elaboration-time readers for the ordinary mathematical bundle and decoder.
The parser and its soundness theorem remain usable by kernel proofs. -/
namespace MilnorCertificates

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
