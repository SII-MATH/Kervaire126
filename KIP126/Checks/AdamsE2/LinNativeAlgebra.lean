import KIP126.LinProgram.Model.E2.Native.Grading
import KIP126.LinProgram.Model.E2.Native.Descent
import KIP126.LinProgram.Model.E2.Native.Basis
import Lean.Elab.Command

/-! Boundary and trust checks for the untruncated native algebra migration. -/
namespace KIP126.Checks.LinNativeAlgebra
noncomputable section
open KIP126.Core.Algebra KIP126.LinE2 MvPolynomial
open KIP126.Algebra.PolynomialTruncation

-- Both boundary components use genuine equivalences, including the last archived degree.
example (s : ℕ) : NativeAt s 260 ≃ₗ[F2] E2At s 260 := truncateAtEquiv s 260 (by decide)
example (s : ℕ) : NativeAt s 261 ≃ₗ[F2] E2At s 261 := truncateAtEquiv s 261 (by decide)

-- The native multiplication exists in arbitrary degrees, including above the cutoff.
example (x : NativeAt 1 131) (y : NativeAt 1 131) : NativeAt 2 262 := nativeMultiply x y

/-- A toy polynomial algebra demonstrates why there is no unconditional extension
of the low-degree equivalence across the cutoff. -/
theorem cutoff_is_not_global :
    (X () : MvPolynomial Unit F2)^262 ≠ 0 ∧
    Ideal.Quotient.mk (highIdeal (R := F2) (fun _ : Unit => (0,1)) 261)
      ((X () : MvPolynomial Unit F2)^262) = 0 := by
  constructor
  · exact pow_ne_zero _ (X_ne_zero ())
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.subset_span
    refine ⟨Finsupp.single () 262, ?_, ?_⟩
    · simp [Finsupp.weight_single]
    · exact X_pow_eq_monomial

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf mod || (`KIP126.Interface).isPrefixOf mod then
      throwError "native algebra imports an actual-model delivery: {mod}"
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``KIP126.Algebra.GradedQuotient.gradedAlgebra,
      ``KIP126.Algebra.PolynomialTruncation.low_mem_sup_iff,
      ``nativeIdeal_isHomogeneous, ``nativeGradedAlgebra, ``nativeProjectionGraded,
      ``nativeHomogeneousPart_eq_span, ``native_csv_relation_zero,
      ``truncate_basisValue, ``truncate_basisRowAt,
      ``truncateAtEquiv, ``truncateAtEquiv_mul, ``nativeDesc,
      ``cutoff_is_not_global] do
    for ax in (← collectAxioms decl) do
      unless logical.contains ax do
        throwError "unexpected axiom in native algebra {decl}: {ax}"

#print axioms KIP126.LinE2.nativeIdeal_isHomogeneous
#print axioms KIP126.LinE2.nativeGradedAlgebra
#print axioms KIP126.LinE2.nativeProjectionGraded
#print axioms KIP126.LinE2.nativeHomogeneousPart_eq_span
#print axioms KIP126.LinE2.truncateAtEquiv
#print axioms KIP126.LinE2.truncateAtEquiv_mul
#print axioms KIP126.LinE2.truncate_basisRowAt
#print axioms KIP126.LinE2.nativeDesc
#print axioms cutoff_is_not_global
end
end KIP126.Checks.LinNativeAlgebra
