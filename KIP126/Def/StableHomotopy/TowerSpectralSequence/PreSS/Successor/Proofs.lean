import KIP126.Def.StableHomotopy.TowerSpectralSequence.PreSS.Data
import KIP126.Def.StableHomotopy.TowerSpectralSequence.NextPages.Proofs
import KIP126.Def.StableHomotopy.TowerSpectralSequence.SSData.Page.Proofs

namespace KIP126.StableHomotopy.TowerSpectralSequence
open CategoryTheory CategoryTheory.Limits KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

@[reassoc] theorem internalD_comparison (m : ℕ) (k n : ℤ) :
    internalD T P m k n ≫ (pageIso T P (k + (m + 1 : ℕ)) (n - 1) m).hom =
      (pageIso T P k n m).hom ≫ ModuleCat.ofHom (differential T P (m + 1) (by omega) k n) := by
  simp only [internalD, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem internalD_π_eq_zero_iff (k n : ℤ) (m : ℕ)
    (x : cycles T P (m + 1) (by omega) k n) :
    internalD T P m k n ((ssData T P k n).pageπ (m : WithTop ℕ)
      ((submoduleUnderlyingIso (M := ModuleCat.of ℤ (E1 T P k n))
        (cycles T P (m + 1) (by omega) k n)).inv x)) = 0 ↔
      x.val ∈ cycles T P ((m + 1) + 1) (by omega) k n := by
  let z := (ssData T P k n).pageπ (m : WithTop ℕ)
    ((submoduleUnderlyingIso (M := ModuleCat.of ℤ (E1 T P k n))
      (cycles T P (m + 1) (by omega) k n)).inv x)
  have hp := congrArg (fun f => f.hom x) (pageIso_π T P k n m)
  change (pageIso T P k n m).hom z = (cycleBoundaries T P (m + 1) (by omega) k n).mkQ x at hp
  have hd := congrArg (fun f => f.hom z) (internalD_comparison T P m k n)
  change (pageIso T P (k + (m + 1 : ℕ)) (n - 1) m).hom (internalD T P m k n z) =
    differential T P (m + 1) (by omega) k n ((pageIso T P k n m).hom z) at hd
  rw [hp, differential_mk] at hd
  have hx := differentialValue_eq_zero_iff T P (m + 1) (by omega) k n x
  constructor
  · intro h
    change internalD T P m k n z = 0 at h
    rw [h, map_zero] at hd
    exact hx.mp hd.symm
  · intro h
    apply (ModuleCat.mono_iff_injective (pageIso T P (k + (m + 1 : ℕ)) (n - 1) m).hom).mp inferInstance
    rw [map_zero, hd]
    exact hx.mpr h

/-- The next-cycle law for the existing categorical differential. -/
theorem internalD_kernel (k n : ℤ) (m : ℕ) :
    kernelSubobject (internalD T P m k n) =
      imageSubobject (Subobject.ofLE
        ((ssData T P k n).Z ((m + 1 : ℕ) : WithTop ℕ)) ((ssData T P k n).Z (m : WithTop ℕ))
        ((ssData T P k n).Z_anti (by exact_mod_cast Nat.le_succ m)) ≫
        (ssData T P k n).pageπ (m : WithTop ℕ)) := by
  let e (j : ℕ) := submoduleUnderlyingIso (M := ModuleCat.of ℤ (E1 T P k n))
    (cycles T P (j + 1) (by omega) k n)
  have hZ := cycles_antitone T P (m + 1) (m + 1 + 1) (by omega) (by omega) (by omega) k n
  have hi (w : cycles T P (m + 1 + 1) (by omega) k n) :
      Subobject.ofLE ((ssData T P k n).Z ((m + 1 : ℕ) : WithTop ℕ))
        ((ssData T P k n).Z (m : WithTop ℕ))
        ((ssData T P k n).Z_anti (by exact_mod_cast Nat.le_succ m)) ((e (m + 1)).inv w) =
          (e m).inv ⟨w.val, hZ w.property⟩ :=
    congrArg (fun f => f.hom w) (submoduleUnderlyingIso_inv_ofLE
      (M := ModuleCat.of ℤ (E1 T P k n)) _ _ hZ)
  apply (ModuleCat.subobjectModule _).injective
  rw [subobjectModule_kernel, subobjectModule_image]
  ext z
  change internalD T P m k n z = 0 ↔ ∃ y, _ = z
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := projection_surjective T P k n m z
    have hw := (internalD_π_eq_zero_iff T P k n m w).mp hz
    refine ⟨(e (m + 1)).inv ⟨w.val, hw⟩, ?_⟩
    exact congrArg (fun y => (ssData T P k n).pageπ (m : WithTop ℕ) y) (hi ⟨w.val, hw⟩)
  · rintro ⟨y, rfl⟩
    obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective (e (m + 1)).inv).mp inferInstance y
    exact (congrArg (fun y => internalD T P m k n
      ((ssData T P k n).pageπ (m : WithTop ℕ) y)) (hi w)).trans
      ((internalD_π_eq_zero_iff T P k n m _).mpr w.property)
theorem internalD_range_iff (m : ℕ) (k n : ℤ)
    (z : (ssData T P (k + (m + 1 : ℕ)) (n - 1)).page (m : WithTop ℕ)) :
    (∃ y, internalD T P m k n y = z) ↔
      ∃ y : page T P (m + 1) (by omega) k n,
        differential T P (m + 1) (by omega) k n y =
          (pageIso T P (k + (m + 1 : ℕ)) (n - 1) m).hom z := by
  let e := (pageIso T P k n m).toLinearEquiv
  let f := (pageIso T P (k + (m + 1 : ℕ)) (n - 1) m).toLinearEquiv
  change (∃ y, f.symm (differential T P (m + 1) (by omega) k n (e y)) = z) ↔
    ∃ y : page T P (m + 1) (by omega) k n,
      differential T P (m + 1) (by omega) k n y = f z
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨e y, f.symm_apply_eq.mp hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    rw [e.apply_symm_apply, hy, f.symm_apply_apply]

theorem internalD_π_range_iff (m : ℕ) (k n : ℤ)
    (x : cycles T P (m + 1) (by omega) (k + (m + 1 : ℕ)) (n - 1)) :
    (∃ y, internalD T P m k n y =
      (ssData T P (k + (m + 1 : ℕ)) (n - 1)).pageπ (m : WithTop ℕ)
        ((submoduleUnderlyingIso (M := ModuleCat.of ℤ (E1 T P (k + (m + 1 : ℕ)) (n - 1)))
          (cycles T P (m + 1) (by omega) (k + (m + 1 : ℕ)) (n - 1))).inv x)) ↔
      x.val ∈ boundaries T P (m + 1 + 1) (by omega) (k + (m + 1 : ℕ)) (n - 1) := by
  rw [internalD_range_iff]
  have hp := congrArg (fun f => f.hom x) (pageIso_π T P (k + (m + 1 : ℕ)) (n - 1) m)
  change (pageIso T P (k + (m + 1 : ℕ)) (n - 1) m).hom _ =
    (cycleBoundaries T P (m + 1) (by omega) (k + (m + 1 : ℕ)) (n - 1)).mkQ x at hp
  erw [hp]
  exact differential_range_iff T P (m + 1) (by omega) k n x

/-- The next-boundary law for the existing categorical differential. -/
theorem internalD_image (k n : ℤ) (m : ℕ) :
    imageSubobject (internalD T P m k n) =
      imageSubobject (Subobject.ofLE
        ((ssData T P (k + (m + 1 : ℕ)) (n - 1)).B ((m + 1 : ℕ) : WithTop ℕ))
        ((ssData T P (k + (m + 1 : ℕ)) (n - 1)).Z (m : WithTop ℕ))
        (le_trans ((ssData T P (k + (m + 1 : ℕ)) (n - 1)).B_le_Z ((m + 1 : ℕ) : WithTop ℕ))
          ((ssData T P (k + (m + 1 : ℕ)) (n - 1)).Z_anti (by exact_mod_cast Nat.le_succ m))) ≫
        (ssData T P (k + (m + 1 : ℕ)) (n - 1)).pageπ (m : WithTop ℕ)) := by
  let a : ℤ := k + (m + 1 : ℕ)
  let b : ℤ := n - 1
  let eB := submoduleUnderlyingIso (M := ModuleCat.of ℤ (E1 T P a b))
    (boundaries T P (m + 1 + 1) (by omega) a b)
  let eZ := submoduleUnderlyingIso (M := ModuleCat.of ℤ (E1 T P a b))
    (cycles T P (m + 1) (by omega) a b)
  have hB := boundaries_le_cycles T P (m + 1 + 1) (m + 1) (by omega) (by omega) a b
  let j := Subobject.ofLE
    ((ssData T P a b).B ((m + 1 : ℕ) : WithTop ℕ))
    ((ssData T P a b).Z (m : WithTop ℕ))
    (le_trans ((ssData T P a b).B_le_Z ((m + 1 : ℕ) : WithTop ℕ))
      ((ssData T P a b).Z_anti (by exact_mod_cast Nat.le_succ m)))
  have hi (w : boundaries T P (m + 1 + 1) (by omega) a b) :
      j (eB.inv w) = eZ.inv ⟨w.val, hB w.property⟩ :=
    congrArg (fun f => f.hom w) (submoduleUnderlyingIso_inv_ofLE
      (M := ModuleCat.of ℤ (E1 T P a b)) _ _ hB)
  apply (ModuleCat.subobjectModule _).injective
  rw [subobjectModule_image, subobjectModule_image]
  ext z
  change (∃ y, internalD T P m k n y = z) ↔ ∃ y, (ssData T P a b).pageπ (m : WithTop ℕ) (j y) = z
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := projection_surjective T P a b m z
    have hw := (internalD_π_range_iff T P m k n w).mp hz
    refine ⟨eB.inv ⟨w.val, hw⟩, ?_⟩
    exact congrArg (fun y => (ssData T P a b).pageπ (m : WithTop ℕ) y) (hi ⟨w.val, hw⟩)
  · rintro ⟨y, rfl⟩
    obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective eB.inv).mp inferInstance y
    obtain ⟨y, hy⟩ := (internalD_π_range_iff T P m k n ⟨w.val, hB w.property⟩).mpr w.property
    refine ⟨y, hy.trans ?_⟩
    exact (congrArg (fun x => (ssData T P a b).pageπ (m : WithTop ℕ) x) (hi w)).symm

/-- Reindexing the target of the existing image law changes only its equality transport. -/
theorem internalD_image_of_target_eq (m : ℕ) (k n : ℤ) (D : SSData (ModuleCat.{v} ℤ))
    (hD : ssData T P (k + (m + 1 : ℕ)) (n - 1) = D) :
    imageSubobject (internalD T P m k n ≫
      eqToHom (congrArg (fun E : SSData (ModuleCat.{v} ℤ) => E.page (m : WithTop ℕ)) hD)) =
      imageSubobject (Subobject.ofLE (D.B ((m + 1 : ℕ) : WithTop ℕ)) (D.Z (m : WithTop ℕ))
        (le_trans (D.B_le_Z ((m + 1 : ℕ) : WithTop ℕ))
          (D.Z_anti (by exact_mod_cast Nat.le_succ m))) ≫ D.pageπ (m : WithTop ℕ)) := by
  subst D
  simpa only [eqToHom_refl, Category.comp_id] using internalD_image T P k n m

end KIP126.StableHomotopy.TowerSpectralSequence
