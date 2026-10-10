import KIP126.Def.ClassicalAdams.TowerHomology.Splitting.Data
import KIP126.Def.StableHomotopy.Cohomology.Coaction.Proofs

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The tower homology unit is exactly the coaction before Künneth. -/
theorem adamsHomologyUnit_eq_coaction (X : C) (n : ℤ) :
    adamsHomologyUnit H X n = (mod2CoactionMap H X n).toIntLinearMap := rfl

theorem adamsHomologyUnit_naturality {X Y : C} (f : X ⟶ Y) (n : ℤ)
    (x : Mod2Homology H n X) :
    Mod2Homology.pushforward H (H.HF2 ◁ f) n (adamsHomologyUnit H X n x) =
      adamsHomologyUnit H Y n (Mod2Homology.pushforward H f n x) :=
  mod2CoactionMap_naturality H f n x

theorem adamsHomologyAction_naturality {X Y : C} (f : X ⟶ Y) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    Mod2Homology.pushforward H f n (adamsHomologyAction H R X n x) =
      adamsHomologyAction H R Y n (Mod2Homology.pushforward H (H.HF2 ◁ f) n x) := by
  change (x ≫ _) ≫ _ = (x ≫ _) ≫ _
  rw [Category.assoc, mod2FreeAction_naturality, Category.assoc]

@[simp]
theorem adamsHomologyNormalize_apply (X : C) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    adamsHomologyNormalize H R X n x =
      x - adamsHomologyUnit H X n (adamsHomologyAction H R X n x) := rfl

theorem adamsHomologyNormalize_action (X : C) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    adamsHomologyAction H R X n (adamsHomologyNormalize H R X n x) = 0 := by
  rw [adamsHomologyNormalize_apply, map_sub, adamsHomologyAction_unit, sub_self]

theorem adamsHomologyNormalize_unit (X : C) (n : ℤ) (x : Mod2Homology H n X) :
    adamsHomologyNormalize H R X n (adamsHomologyUnit H X n x) = 0 := by
  rw [adamsHomologyNormalize_apply, adamsHomologyAction_unit, sub_self]

theorem adamsHomologyNormalize_eq_self (X : C) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    adamsHomologyNormalize H R X n x = x ↔ adamsHomologyAction H R X n x = 0 := by
  constructor
  · intro hx
    rw [← hx]
    exact adamsHomologyNormalize_action H R X n x
  · intro hx
    rw [adamsHomologyNormalize_apply, hx, map_zero, sub_zero]

theorem adamsHomologyNormalize_idempotent (X : C) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    adamsHomologyNormalize H R X n (adamsHomologyNormalize H R X n x) =
      adamsHomologyNormalize H R X n x := by
  exact (adamsHomologyNormalize_eq_self H R X n _).mpr
    (adamsHomologyNormalize_action H R X n x)

/-- Normalization commutes with maps of the remaining spectrum. -/
theorem adamsHomologyNormalize_naturality {X Y : C} (f : X ⟶ Y) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    Mod2Homology.pushforward H (H.HF2 ◁ f) n (adamsHomologyNormalize H R X n x) =
      adamsHomologyNormalize H R Y n (Mod2Homology.pushforward H (H.HF2 ◁ f) n x) := by
  simp only [adamsHomologyNormalize_apply, map_sub, adamsHomologyUnit_naturality,
    adamsHomologyAction_naturality]

theorem adamsHomologyNormalize_range (X : C) (n : ℤ) :
    LinearMap.range (adamsHomologyNormalize H R X n) =
      LinearMap.ker (adamsHomologyAction H R X n) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact adamsHomologyNormalize_action H R X n y
  · intro hx
    exact ⟨x, (adamsHomologyNormalize_eq_self H R X n x).mpr hx⟩

theorem adamsHomologyNormalize_ker (X : C) (n : ℤ) :
    LinearMap.ker (adamsHomologyNormalize H R X n) =
      LinearMap.range (adamsHomologyUnit H X n) := by
  ext x
  constructor
  · intro hx
    refine ⟨adamsHomologyAction H R X n x, ?_⟩
    exact (sub_eq_zero.mp hx).symm
  · rintro ⟨y, rfl⟩
    exact adamsHomologyNormalize_unit H R X n y

variable [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- Normalization does not change the class in the next actual tower stage. -/
theorem adamsHomologyBoundary_normalize (X : C) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    adamsHomologyBoundary H X n (adamsHomologyNormalize H R X n x) =
      adamsHomologyBoundary H X n x := by
  rw [adamsHomologyNormalize_apply, map_sub, adamsHomologyBoundary_unit, sub_zero]

@[simp]
theorem adamsHomologySplitEquiv_apply (X : C) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ X)) :
    adamsHomologySplitEquiv H R X n x =
      (adamsHomologyAction H R X n x, adamsHomologyBoundary H X n x) := rfl

@[simp]
theorem adamsHomologySplitEquiv_symm_apply (X : C) (n : ℤ)
    (x : Mod2Homology H n X) (y : Mod2Homology H (n - 1) (fiber (adamsUnit H.unit X))) :
    (adamsHomologySplitEquiv H R X n).symm (x, y) =
      adamsHomologyUnit H X n x + ((adamsHomologyKernelEquiv H R X n).symm y).val := rfl

end

end KIP126.Classical.Adams
