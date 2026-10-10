import KIP126.Def.StableHomotopy.TowerSpectralSequence.SSData.Page.Data
import KIP126.Def.StableHomotopy.TowerSpectralSequence.Differential.Data

/-! Intrinsic tower differentials in the common nested-subobject model.
The initial page is one. Synthetic page labels are a later regrading. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory KIP126.Core.SpectralSequence

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

-- Degree transports use the public SSData object, not its submodule implementation.
attribute [local irreducible] ssData

/-- Internal stage m is raw page m+1, including the first differential. -/
noncomputable def internalD (m : ℕ) (k n : ℤ) :
    (ssData T P k n).page (m : WithTop ℕ) ⟶
      (ssData T P (k + (m + 1 : ℕ)) (n - 1)).page (m : WithTop ℕ) :=
  (pageIso T P k n m).hom ≫
    ModuleCat.ofHom (differential T P (m + 1) (by omega) k n) ≫
      (pageIso T P (k + (m + 1 : ℕ)) (n - 1) m).inv

noncomputable def preSS : PreSS (ModuleCat.{v} ℤ) (ℤ × ℤ) where
  r₀ := 1
  ssData p := ssData T P p.1 p.2
  diffDeg r := (r, -1)
  d r p := if hr : 1 ≤ r then
    internalD T P (r - 1).toNat p.1 p.2 ≫ eqToHom (by
      have hn : (((r - 1).toNat + 1 : ℕ) : ℤ) = r := by omega
      change (ssData T P (p.1 + ((r - 1).toNat + 1 : ℕ)) (p.2 - 1)).page
        ((r - 1).toNat : WithTop ℕ) =
          (ssData T P (p + (r, -1)).1 (p + (r, -1)).2).page
            ((r - 1).toNat : WithTop ℕ)
      rw [hn]
      rfl)
    else 0

end KIP126.StableHomotopy.TowerSpectralSequence
