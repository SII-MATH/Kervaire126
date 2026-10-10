import KIP126.Def.StableHomotopy.TowerSpectralSequence.ExactCouple.Data
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Kernel/image pages of the actual descending tower. Page one is retained:
the finite parameter q is the intrinsic differential length, with degree
(q, -1) in (tower level, represented suspension degree). -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

/-- A q-cycle is a first-page class whose connecting image lifts q-1 steps. -/
noncomputable def cycles (q : ℕ) (hq : 1 ≤ q) (k n : ℤ) :
    Submodule ℤ (E1 T P k n) :=
  (LinearMap.range (I T P (n - 1) (k + 1) (k + q) (by omega))).comap
    (K T P k n)

/-- A q-boundary is the layer image of a tower class killed q-1 steps below. -/
noncomputable def boundaries (q : ℕ) (hq : 1 ≤ q) (k n : ℤ) :
    Submodule ℤ (E1 T P k n) :=
  (LinearMap.ker (I T P n (k - q + 1) k (by omega))).map (J T P k n)

/-- Boundary representatives inside the specified cycle module. -/
noncomputable def cycleBoundaries (q : ℕ) (hq : 1 ≤ q) (k n : ℤ) :
    Submodule ℤ (cycles T P q hq k n) :=
  (boundaries T P q hq k n).comap (cycles T P q hq k n).subtype

/-- The actual quotient page. -/
abbrev page (q : ℕ) (hq : 1 ≤ q) (k n : ℤ) :=
  (cycles T P q hq k n) ⧸ cycleBoundaries T P q hq k n

/-- Select a preimage whose existence is precisely cycle membership.
The quotient differential must separately prove independence of this lift. -/
noncomputable def cycleLift (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : cycles T P q hq k n) : ShiftedHom P (n - 1) (T.obj (k + q)) :=
  Classical.choose x.property

end KIP126.StableHomotopy.TowerSpectralSequence
