import KIP126.LinProgram.Certificates.SquareDetection.Archive.Proofs
import KIP126.LinProgram.Model.E2.Native.Data

/-! The existing detector certificate applies directly to the untruncated
relation ideal. No equation in the old truncated quotient is lifted backwards. -/
namespace KIP126.LinE2.SquareDetection
open KIP126.Core.Algebra
noncomputable section

theorem nativeIdeal_le_ker : nativeIdeal ≤ RingHom.ker evaluate := by
  apply Ideal.span_le.mpr
  rintro p ⟨code, hc, rfl⟩
  exact relationCheck_sound code (List.all_eq_true.mp allRelationsCheck_eq_true code hc)

/-- The detector on the original relation quotient, without truncation. -/
def nativeDetector : NativeAlgebra →+* Target :=
  Ideal.Quotient.lift nativeIdeal evaluate nativeIdeal_le_ker

@[simp] theorem nativeDetector_projection (p : Poly) :
    nativeDetector (nativeProjection p) = evaluate p := rfl

@[simp] theorem nativeDetector_h6 : nativeDetector (nativeGenerator h6Generator) = u := by
  change evaluate (MvPolynomial.X h6Generator) = u
  rw [evaluate_X, if_pos rfl]

theorem native_h6_square_ne_zero : nativeGenerator h6Generator ^ 2 ≠ 0 := by
  intro h
  have he := congrArg nativeDetector h
  rw [map_pow, nativeDetector_h6, map_zero] at he
  exact u_square_ne_zero he

theorem nativeAlgebra_nontrivial : Nontrivial NativeAlgebra :=
  nontrivial_of_ne (nativeGenerator h6Generator ^ 2) 0 native_h6_square_ne_zero

/-- The old square is the image of this same native square. -/
theorem truncate_h6_square : truncate (nativeGenerator h6Generator ^ 2) = dataH6Sq.val := by
  simp only [map_pow, truncate_generator]
  rfl
end
end KIP126.LinE2.SquareDetection
