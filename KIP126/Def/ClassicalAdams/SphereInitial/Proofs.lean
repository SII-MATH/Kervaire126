import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Sphere.Proofs
import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs

/-! All cycle stages in sphere filtration zero are the full module.
Its boundaries vanish because the negative tower is constant. These
statements concern the actual tower and its internal SSData object. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))

/-- The initial exact-couple connecting map of the actual sphere tower is zero. -/
theorem sphereAdamsK_zero (t : ℤ) (x : adamsE1 H.unit SphereSpectrum 0 t) :
    adamsK H.unit SphereSpectrum 0 t x = 0 := by
  have h := adamsK_eq_resolutionBoundary H.unit SphereSpectrum 0 t x
  rw [sphereAdamsResolutionBoundary_zero] at h
  exact h

theorem sphereAdamsCycles_filtration_zero (r : ℕ) (hr : 1 ≤ r) (t : ℤ) :
    adamsCycles H.unit SphereSpectrum r hr 0 t = ⊤ := by
  apply top_unique
  intro x _
  change adamsK H.unit SphereSpectrum 0 t x ∈ LinearMap.range _
  rw [sphereAdamsK_zero]
  exact Submodule.zero_mem _

/-- Every outgoing differential from actual sphere filtration zero vanishes,
not only the first differential. -/
theorem sphereAdamsDifferential_filtration_zero (r : ℕ) (hr : 1 ≤ r) (t : ℤ)
    (x : adamsPage H.unit SphereSpectrum r hr 0 t) :
    adamsDifferential H.unit SphereSpectrum r hr 0 t x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change adamsDifferentialValue H.unit SphereSpectrum r hr 0 t x = 0
    exact adamsDifferentialValue_eq_zero_of_K H.unit SphereSpectrum r hr 0 t x
      (sphereAdamsK_zero H t x)

omit H in
/-- The constant negative extension gives no filtration-zero boundaries
for any actual Adams tower, independently of the coefficient spectrum. -/
theorem adamsBoundaries_filtration_zero {A : C} (unit : SphereSpectrum ⟶ A)
    (X : C) (r : ℕ) (hr : 1 ≤ r) (t : ℤ) :
    adamsBoundaries unit X r hr 0 t = ⊥ := by
  let f := adamsTowerMapAt unit X (0 - r + 1) 0 (by omega)
  haveI : IsIso f := adamsTowerMapAt_isIso_of_nonpositive unit X
    (0 - r + 1) 0 (by omega) le_rfl
  have hi : Function.Injective (adamsI unit X (t - 0) (0 - r + 1) 0 (by omega)) := by
    intro x y h
    change x ≫ f = y ≫ f at h
    exact (cancel_mono f).mp h
  rw [adamsBoundaries, LinearMap.ker_eq_bot.mpr hi, Submodule.map_bot]

theorem sphereAdamsCycleSubmodule_filtration_zero (t : ℤ) (n : WithTop ℕ) :
    adamsCycleSubmodule H.unit SphereSpectrum 0 t n = ⊤ := by
  induction n using WithTop.recTopCoe with
  | top =>
    simp [adamsCycleSubmodule, adamsFiniteCycleSubmodule, sphereAdamsCycles_filtration_zero]
  | coe n =>
    simp [adamsCycleSubmodule, adamsFiniteCycleSubmodule, sphereAdamsCycles_filtration_zero]

theorem sphereAdamsBoundarySubmodule_filtration_zero (t : ℤ) (n : WithTop ℕ) :
    adamsBoundarySubmodule H.unit SphereSpectrum 0 t n = ⊥ := by
  induction n using WithTop.recTopCoe with
  | top =>
    simp [adamsBoundarySubmodule, adamsFiniteBoundarySubmodule,
      adamsBoundaries_filtration_zero, Submodule.ker_subtype]
  | coe n =>
    simp [adamsBoundarySubmodule, adamsFiniteBoundarySubmodule,
      adamsBoundaries_filtration_zero, Submodule.ker_subtype]

/-- The actual internal sphere SSData has no loss of cycles in filtration zero,
including at its infinite intersection stage. -/
theorem sphereAdamsSSData_Z_filtration_zero (t : ℤ) (n : WithTop ℕ) :
    (adamsTowerSSData H.unit SphereSpectrum 0 t).Z n = ⊤ := by
  change (ModuleCat.subobjectModule
    (ModuleCat.of ℤ (adamsCycleAmbient H.unit SphereSpectrum 0 t))).symm
    (adamsCycleSubmodule H.unit SphereSpectrum 0 t n) = ⊤
  rw [sphereAdamsCycleSubmodule_filtration_zero, OrderIso.map_top]

/-- Nor does that internal object acquire a boundary at any finite or infinite stage. -/
theorem sphereAdamsSSData_B_filtration_zero (t : ℤ) (n : WithTop ℕ) :
    (adamsTowerSSData H.unit SphereSpectrum 0 t).B n = ⊥ := by
  change (ModuleCat.subobjectModule
    (ModuleCat.of ℤ (adamsCycleAmbient H.unit SphereSpectrum 0 t))).symm
    (adamsBoundarySubmodule H.unit SphereSpectrum 0 t n) = ⊥
  rw [sphereAdamsBoundarySubmodule_filtration_zero, OrderIso.map_bot]

end

end KIP126.Classical.Adams
