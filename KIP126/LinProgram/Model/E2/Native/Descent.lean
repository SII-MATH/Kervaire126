module

public import KIP126.LinProgram.Model.E2.Native.Data

@[expose] public section


/-! The universal property of the original-relation quotient requires no
high-degree vanishing or choice of a truncated target. -/
namespace KIP126.LinE2
open KIP126.Core.Algebra
noncomputable section
variable {B : Type*} [CommRing B] [Algebra F2 B]

/-- Evaluation on the original generators descends exactly when the original
relations vanish. This retains every original CSV relation. -/
def nativeDesc (v : Generator → B)
    (hrel : ∀ code ∈ RawData.relations, MvPolynomial.aeval v (relationPolynomial code) = 0) :
    NativeAlgebra →ₐ[F2] B :=
  Ideal.Quotient.liftₐ nativeIdeal (MvPolynomial.aeval v) (by
    change nativeIdeal ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom
    apply Ideal.span_le.mpr
    rintro p ⟨code, hc, rfl⟩
    exact hrel code hc)

@[simp] theorem nativeDesc_projection (v : Generator → B)
    (hrel : ∀ code ∈ RawData.relations, MvPolynomial.aeval v (relationPolynomial code) = 0)
    (p : Poly) : nativeDesc v hrel (nativeProjection p) = MvPolynomial.aeval v p := rfl

@[simp] theorem nativeDesc_generator (v : Generator → B)
    (hrel : ∀ code ∈ RawData.relations, MvPolynomial.aeval v (relationPolynomial code) = 0)
    (i : Generator) : nativeDesc v hrel (nativeGenerator i) = v i := by
  simp [nativeGenerator]

end
end KIP126.LinE2
