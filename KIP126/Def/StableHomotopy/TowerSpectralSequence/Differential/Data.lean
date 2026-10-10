import KIP126.Def.StableHomotopy.TowerSpectralSequence.Differential.Cycles.Proofs

/-! The intrinsic page differential descends the actual cycle formula to
the quotient by its actual boundary submodule. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

/-- The tower's actual intrinsic q-page differential, of degree (q,-1). -/
noncomputable def differential (q : ℕ) (hq : 1 ≤ q) (k n : ℤ) :
    page T P q hq k n →ₗ[ℤ] page T P q hq (k + q) (n - 1) :=
  (cycleBoundaries T P q hq k n).liftQ
    (differentialOnCycles T P q hq k n)
    (boundaries_le_differential_ker T P q hq k n)

end KIP126.StableHomotopy.TowerSpectralSequence
