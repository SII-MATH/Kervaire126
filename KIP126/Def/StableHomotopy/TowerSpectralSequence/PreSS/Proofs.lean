import KIP126.Def.StableHomotopy.TowerSpectralSequence.PreSS.Data
import KIP126.Def.StableHomotopy.TowerSpectralSequence.PreSS.Successor.Proofs

/-! The exact-couple square-zero and successor laws for the specified
quotient differential. Their proofs remain separate from the construction. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory CategoryTheory.Limits KIP126.Core.SpectralSequence

set_option backward.isDefEq.respectTransparency false

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

attribute [local irreducible] ssData

/-- The actual quotient differential remains square-zero under the canonical
comparison with categorical pages. -/
theorem internalD_comp (m : ℕ) (k n : ℤ) :
    internalD T P m k n ≫ internalD T P m (k + (m + 1 : ℕ)) (n - 1) = 0 := by
  have h : ModuleCat.ofHom (differential T P (m + 1) (by omega) k n) ≫
      ModuleCat.ofHom (differential T P (m + 1) (by omega) (k + (m + 1 : ℕ)) (n - 1)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact differential_comp T P (m + 1) (by omega) k n x
  simp only [internalD, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (ModuleCat.ofHom _) (ModuleCat.ofHom _), h, zero_comp, comp_zero]

/-- Equality transport commutes with the specified differential. This is the
same dependent-transport argument used in KIPBase's ShiftedDifferential. -/
@[reassoc] theorem internalD_transport (P' : C) (hP : P = P') (m : ℕ) (k n k' n' : ℤ) (hk : k = k') (hn : n = n') :
    eqToHom (by rw [hP, hk, hn]) ≫ internalD T P' m k' n' =
      internalD T P m k n ≫ eqToHom (by rw [hP, hk, hn]) := by
  subst P'
  subst k'
  subst n'
  simp

theorem preSS_d_comp_d (r : ℤ) (p : ℤ × ℤ) :
    (preSS T P).d r p ≫ (preSS T P).d r (p + (preSS T P).diffDeg r) = 0 := by
  by_cases hr : 1 ≤ r
  · dsimp only [preSS]
    simp only [dif_pos hr, Prod.fst_add, Prod.snd_add]
    rw [Category.assoc]
    rw [internalD_transport_assoc T P P rfl (r - 1).toNat
      (p.1 + ((r - 1).toNat + 1 : ℕ)) (p.2 - 1)
      (p.1 + r) (p.2 + -1) (by omega) (by omega)]
    rw [← Category.assoc, internalD_comp, zero_comp]
  · simp only [preSS, dif_neg hr, zero_comp]

theorem preSS_Z_succ (r : ℤ) (p : ℤ × ℤ) (hr : 1 ≤ r) :
    let m := (r - 1).toNat
    kernelSubobject ((preSS T P).d r p) =
      imageSubobject (Subobject.ofLE
        (((preSS T P).ssData p).Z ((m + 1 : ℕ) : WithTop ℕ))
        (((preSS T P).ssData p).Z (m : WithTop ℕ))
        (((preSS T P).ssData p).Z_anti (by exact_mod_cast Nat.le_succ m)) ≫
        ((preSS T P).ssData p).pageπ (m : WithTop ℕ)) := by
  simp only [preSS, dif_pos hr, kernelSubobject_comp_mono]
  exact internalD_kernel T P p.1 p.2 (r - 1).toNat

theorem preSS_B_succ (r : ℤ) (p : ℤ × ℤ) (hr : 1 ≤ r) :
    let m := (r - 1).toNat
    let D := (preSS T P).ssData (p + (preSS T P).diffDeg r)
    imageSubobject ((preSS T P).d r p) =
      imageSubobject (Subobject.ofLE (D.B ((m + 1 : ℕ) : WithTop ℕ))
        (D.Z (m : WithTop ℕ))
        (le_trans (D.B_le_Z ((m + 1 : ℕ) : WithTop ℕ))
          (D.Z_anti (by exact_mod_cast Nat.le_succ m))) ≫ D.pageπ (m : WithTop ℕ)) := by
  simp only [preSS, dif_pos hr]
  apply internalD_image_of_target_eq
  have hq : (((r - 1).toNat + 1 : ℕ) : ℤ) = r := by omega
  rw [hq]
  rfl

end KIP126.StableHomotopy.TowerSpectralSequence
