module

public import KIP126.Def.StageInput.StandardSphere.Sequence.Data
public import KIP126.Def.StageInput.Milnor
public import KIP126.Def.ClassicalAdams.SphereClasses.Product.Data
public import KIP126.Def.ClassicalAdams.SphereMultiplication.Data
public import KIP126.Def.ClassicalAdams.Suspension.Data
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.DirectSum.Algebra

@[expose] public section


/-! Homogeneous pieces and operations for the fixed actual sphere E₂ algebra.
The page and product are fixed before any native presentation is supplied.
The scalar action is transported along the existing canonical cobar comparison;
it preserves the actual page's additive group. -/

namespace KIP126.Classical.Adams.Sphere.Internal

open KIP126.Core.Algebra KIP126.StableHomotopy
noncomputable section

/-- The existing fixed sphere second page, in every nonnegative bidegree.
This is a definitionally equal type alias: keeping it as a `def` prevents
scalar-instance search from unfolding the entire fixed spectral sequence. -/
def ActualE2At (p : ℕ × ℕ) : Type := sphereAdamsData.Page 2 ((p.1 : ℤ), (p.2 : ℤ))

instance actualE2AtAddCommGroup (p : ℕ × ℕ) : AddCommGroup (ActualE2At p) :=
  inferInstanceAs (AddCommGroup (sphereAdamsData.Page 2 ((p.1 : ℤ), (p.2 : ℤ))))

instance actualE2AtIntModule (p : ℕ × ℕ) : Module ℤ (ActualE2At p) :=
  inferInstanceAs (Module ℤ (sphereAdamsData.Page 2 ((p.1 : ℤ), (p.2 : ℤ))))

/-- The fixed cobar comparison, read from the actual page to cobar cohomology. -/
def actualE2ToCobarInt (p : ℕ × ℕ) : ActualE2At p ≃ₗ[ℤ]
    MilnorCohomology.Cohomology standardFoundation.hf2 standardMilnorCooperations p.1 p.2 :=
  (MilnorCohomology.comparison standardFoundation.hf2 standardMilnorCooperations p.1 p.2).symm

instance actualE2AtModule (p : ℕ × ℕ) : Module F2 (ActualE2At p) :=
  (actualE2ToCobarInt p).toAddEquiv.module F2

instance actualE2AtScalarTower (p : ℕ × ℕ) :
    @IsScalarTower ℤ F2 (ActualE2At p)
      (inferInstance : Module ℤ F2).toSMul
      (inferInstance : Module F2 (ActualE2At p)).toSMul
      (inferInstance : Module ℤ (ActualE2At p)).toSMul :=
  (actualE2ToCobarInt p).isScalarTower F2

instance actualE2AtIntSMulComm (p : ℕ × ℕ) :
    @SMulCommClass ℤ ℤ (ActualE2At p)
      (inferInstance : Module ℤ (ActualE2At p)).toSMul
      (inferInstance : Module ℤ (ActualE2At p)).toSMul :=
  @smulCommClass_self ℤ (ActualE2At p) _
    (inferInstance : Module ℤ (ActualE2At p)).toMulAction

/-- The same fixed comparison, now with its induced F₂-linearity. -/
def actualE2ToCobar (p : ℕ × ℕ) : ActualE2At p ≃ₗ[F2]
    MilnorCohomology.Cohomology standardFoundation.hf2 standardMilnorCooperations p.1 p.2 :=
  (actualE2ToCobarInt p).toAddEquiv.linearEquiv F2

/-- The previously fixed actual product, bundled as an F₂-bilinear map. -/
def actualE2Product (p q : ℕ × ℕ) :
    ActualE2At p →ₗ[F2] ActualE2At q →ₗ[F2] ActualE2At (p + q) where
  toFun x := (actualE2ToCobar (p + q)).symm.toLinearMap.comp
    ((MilnorCohomology.cup standardFoundation.hf2 standardMilnorCooperations
      (actualE2ToCobar p x)).comp (actualE2ToCobar q).toLinearMap)
  map_add' x y := by
    ext z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_add,
      LinearMap.add_apply]
  map_smul' r x := by
    ext z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul,
      LinearMap.smul_apply, RingHom.id_apply]

/-- The actual second-cycle class of the sphere identity, in degree (0,0). -/
def actualE2Unit : ActualE2At 0 :=
  Suspension.classOfSecondCycle standardFoundation.hf2 SphereSpectrum 0 0
    (Sphere.Multiplication.unitSecondCycle standardFoundation.hf2)

instance actualE2GradedOne : GradedMonoid.GOne ActualE2At := ⟨actualE2Unit⟩
instance actualE2GradedMul : GradedMonoid.GMul ActualE2At := ⟨fun {p q} x y => actualE2Product p q x y⟩

end
end KIP126.Classical.Adams.Sphere.Internal
