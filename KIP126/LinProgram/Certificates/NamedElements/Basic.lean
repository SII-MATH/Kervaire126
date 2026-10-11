module

public import KIP126.LinProgram.Certificates.NamedElements.Data
public meta import KIP126.LinProgram.Certificates.NamedElements.Data

@[expose] public section

/-! Read an explicit named-element certificate during elaboration. The ordinary
checker, semantics, parser and soundness proof are defined in `Data`. -/
namespace NamedElementCertificates

open Lean Elab Term
elab "named_bundle% " path:str : term => do
  let text ← IO.FS.readFile path.getString
  match parse text.trimAscii.toString with
  | .error e => throwError "{path.getString}: {e}"
  | .ok b => return toExpr b

end NamedElementCertificates
