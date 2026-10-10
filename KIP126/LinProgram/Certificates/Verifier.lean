namespace LinProgramCertificates

/-!
## 可执行检查器契约

`CertificateVerifier P` 将具体证书类型、可执行 Bool 检查器和可靠性证明绑定。
外部 C++ 只生成证书数据；内核只接受 `sound` 给出的证明。因而 tactic 不需要
信任 C++，也不能凭一个字符串直接制造 `P`。
-/

/-- 对命题 `P` 的证书检查器。每个具体数学结果定义一个实例。 -/
class CertificateVerifier (P : Prop) where
  /-- 证书的 Lean 表示。 -/
  Cert : Type
  /-- 可执行（且可在内核中约简的）检查器。 -/
  check : Cert → Bool
  /-- 检查器可靠性：通过即推出语义命题。 -/
  sound : ∀ certificate, check certificate = true → P

/-- 对一个证书执行内核可约简的检查。 -/
def verify {P : Prop} [v : CertificateVerifier P]
    (certificate : v.Cert) : Except String (PLift P) :=
  if h : v.check certificate = true then
    .ok ⟨v.sound certificate h⟩
  else
    .error "certificate checker rejected the certificate"

/-- 失败结果保留可读的检查器诊断。 -/
structure VerificationFailure where
  kind : String
  location : String
  message : String
  deriving Repr, DecidableEq

/-- 带失败位置的证书检查器扩展。旧的 `CertificateVerifier` 仍可直接使用。 -/
class DiagnosticCertificateVerifier (P : Prop) extends CertificateVerifier P where
  diagnose : Cert → Option VerificationFailure

end LinProgramCertificates
