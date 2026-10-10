import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Internal.Data
import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Proofs
import KIP126.Def.ClassicalAdams.SphereClasses.Proofs

/-! The internal classes preserve the actual Milnor quotient representatives. -/

namespace KIP126.Classical.Adams.Sphere.Internal

noncomputable section

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- For every index, the internal class has the specified original quotient image. -/
theorem hi_pageIso (i : ℕ) :
    (adamsTowerSSDataPageIso H.unit SphereSpectrum 1 ((2 ^ i : ℕ) : ℤ) 0).hom
      (hi H M i) = Sphere.hi H M i := by
  change (adamsTowerSSDataPageIso H.unit SphereSpectrum 1 ((2 ^ i : ℕ) : ℤ) 0).toLinearEquiv
    ((adamsTowerSSDataPageIso H.unit SphereSpectrum 1 ((2 ^ i : ℕ) : ℤ) 0).toLinearEquiv.symm
      (Sphere.hi H M i)) = Sphere.hi H M i
  exact LinearEquiv.apply_symm_apply _ _

/-- The same quotient isomorphism preserves each actual concatenation square. -/
theorem hiSquare_pageIso (i : ℕ) :
    (adamsTowerSSDataPageIso H.unit SphereSpectrum 2 ((2 ^ (i + 1) : ℕ) : ℤ) 0).hom
      (hiSquare H M i) = Sphere.hiSquare H M i := by
  change
    (adamsTowerSSDataPageIso H.unit SphereSpectrum 2 ((2 ^ (i + 1) : ℕ) : ℤ) 0).toLinearEquiv
      ((adamsTowerSSDataPageIso H.unit SphereSpectrum 2 ((2 ^ (i + 1) : ℕ) : ℤ) 0).toLinearEquiv.symm
        (Sphere.hiSquare H M i)) = Sphere.hiSquare H M i
  exact LinearEquiv.apply_symm_apply _ _

/-- The sixth internal class is the image of the previously fixed standard `h₆`. -/
@[simp] theorem hi_six : hi H M 6 =
    (adamsTowerSSDataPageIso H.unit SphereSpectrum 1 64 0).inv (Sphere.h6 H M) := rfl

/-- The sixth internal square is the image of the previously fixed standard square. -/
@[simp] theorem hiSquare_six : hiSquare H M 6 =
    (adamsTowerSSDataPageIso H.unit SphereSpectrum 2 128 0).inv (Sphere.h6Square H M) := rfl

/-- The specified internal square is nonzero by the standard cobar calculation.
No Lin data, basis certificate, or computed differential is used. -/
theorem hiSquare_six_ne_zero : hiSquare H M 6 ≠ 0 := by
  intro h
  apply Sphere.h6Square_ne_zero H M
  exact (hiSquare_pageIso H M 6).symm.trans
    ((congrArg (adamsTowerSSDataPageIso H.unit SphereSpectrum 2 128 0).hom.hom h).trans
      (map_zero _))

end

end KIP126.Classical.Adams.Sphere.Internal
