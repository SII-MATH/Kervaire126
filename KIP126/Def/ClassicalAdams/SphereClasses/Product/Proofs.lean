import KIP126.Def.ClassicalAdams.SphereClasses.Product.Data
import KIP126.Def.ClassicalAdams.SphereClasses.Products.Data
import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.Proofs

/-! Linearity of the fixed sphere product, transported from cobar cohomology. -/
namespace KIP126.Classical.Adams.Sphere.Internal
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
    (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

theorem product_add_right {s t s' t' : ℕ}
    (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s,t))
    (y z : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s',t')) :
    product H M (s := s) (t := t) (s' := s') (t' := t') x (y+z)=product H M (s := s) (t := t) (s' := s') (t' := t') x y+product H M (s := s) (t := t) (s' := s') (t' := t') x z := by
  unfold product
  rw [map_add,map_add,map_add]

theorem product_zsmul_right {s t s' t' : ℕ}
    (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s,t))
    (y : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s',t')) (n : ℤ) :
    product H M (s := s) (t := t) (s' := s') (t' := t') x (n • y)=n • product H M (s := s) (t := t) (s' := s') (t' := t') x y := by
  unfold product
  rw [map_zsmul,map_zsmul,map_zsmul]

/-! ### The sphere-only graded-commutativity obligation

The internal product is presently defined only for the actual sphere
second page.  We record its Koszul symmetry with the degree transport made
explicit: reversing the two factors changes `(s + s', t + t')` to
`(s' + s, t' + t)`.  The parity is the topological degree `t - s`; no
commutativity statement for an arbitrary spectrum is introduced here. -/

def spherePageDegreeTransport (s t s' t' : ℕ)
    (h : (((s' + s : ℕ) : ℤ), ((t' + t : ℕ) : ℤ)) =
      (((s + s' : ℕ) : ℤ), ((t + t' : ℕ) : ℤ))) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
        (s' + s, t' + t) ⟶
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
        (s + s', t + t') :=
  eqToHom (congrArg
    (fun p : ℤ × ℤ =>
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 p) h)

def SphereProductGradedCommutative : Prop :=
  ∀ {s t s' t' : ℕ}
    (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s, t))
    (y : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s', t')),
    product H M x y =
      ((-1 : ℤ) ^ ((((t : ℤ) - s) * ((t' : ℤ) - s')).natAbs)) •
        (spherePageDegreeTransport H s t s' t'
          (by apply Prod.ext <;> omega)).hom (product H M y x)

theorem sphere_product_graded_commutativity :
    SphereProductGradedCommutative H M := by
  sorry

/-! The forward order used by the one-line differential is definitionally the
named `h₀ h₅²` class.  This is a comparison calculation, not an additional
commutativity assumption. -/
theorem product_hi_zero_hiSquare_five_eq_h0HiSquare :
    product H M
        (hi H M 0)
        (hiSquare H M 5) =
      h0HiSquare H M 5 := by
  unfold product h0HiSquare
  rw [← MilnorCohomology.comparison_hi H M 0,
    ← MilnorCohomology.comparison_hiSquare H M 5]
  simp

end
end KIP126.Classical.Adams.Sphere.Internal
