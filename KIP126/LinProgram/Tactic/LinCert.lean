module

public import Lean.Elab.Tactic
public import KIP126.LinProgram.Certificates.Verifier

@[expose] public section


namespace LinProgramCertificates

open Lean Elab Tactic

/-!
## 自动化 tactic

`lin_cert using c` 把目标命题作为 `P`，从对应的
`CertificateVerifier P` 实例取出 `check` 与 `sound`，并让内核约简
`check c = true`。这与手写 `exact verifier.sound c (by decide)` 等价，
因此 tactic 本身不是信任边界。
-/

syntax (name := linCert) "lin_cert" " using " term : tactic

elab_rules : tactic
  | `(tactic| lin_cert using $certificate:term) =>
      do
        evalTactic (← `(tactic|
          exact CertificateVerifier.sound $certificate (by decide)))

/-- Diagnostics are evaluated only to explain rejection; proof construction
always uses the soundness theorem and kernel reduction of the checker. -/
elab "lin_cert_diagnose" " using " certificate:term : tactic => do
  withMainContext do
    let goal ← getMainTarget
    let diagnosticClass := mkApp (mkConst ``DiagnosticCertificateVerifier) goal
    let diagnosticInstance ← Meta.synthInstance? diagnosticClass
    if let some inst := diagnosticInstance then
      let mut failure : Option VerificationFailure := none
      let saved ← saveState
      try
        let expected ← Meta.mkAppOptM ``DiagnosticCertificateVerifier.toCertificateVerifier #[some goal, some inst]
        let certType ← Meta.mkAppOptM ``CertificateVerifier.Cert #[some goal, some expected]
        let cert ← Term.elabTermEnsuringType certificate certType
        Term.synthesizeSyntheticMVarsNoPostponing
        let query ← Meta.mkAppOptM ``DiagnosticCertificateVerifier.diagnose #[some goal, some inst, some cert]
        let query ← instantiateMVars query
        if query.hasFVar || query.hasMVar then
          logInfo "Certificate diagnostics require a closed certificate; checking the proof goal."
        else
          failure ← unsafe Meta.evalExpr (Option VerificationFailure)
            (mkApp (mkConst ``Option [Level.zero]) (mkConst ``VerificationFailure)) query
      catch _ =>
        saved.restore
        logInfo "Certificate diagnostics could not be evaluated; checking the proof goal."
      if let some e := failure then
        throwError "{e.kind}: {e.location}: {e.message}"
    evalTactic (← `(tactic|
      exact CertificateVerifier.sound $certificate (by decide)))

end LinProgramCertificates
