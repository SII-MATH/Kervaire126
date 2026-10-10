import KIP126.Def.StableHomotopy.TowerSpectralSequence.Pages.Data
import KIP126.Def.StableHomotopy.DescendingTower.Proofs
import KIP126.Def.StableHomotopy.RepresentedHom.Proofs

/-! Properties of the specified kernel/image pages. These proofs do
not select an exact couple or substitute a new spectral-sequence object.

The cycle and incoming-boundary arguments adapt
`KIPBase/Synthetic/GeometricAdams.lean` (`sourceCycles_antitone`,
`incomingBoundaries_mono`, `incomingBoundaries_one`, and
`incomingBoundaries_le_sourceCycles`) to the existing integer-indexed tower
and its represented-Hom exact couple. No historical model is imported. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

theorem cycleLift_spec (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : cycles T P q hq k n) :
    I T P (n - 1) (k + 1) (k + q) (by omega) (cycleLift T P q hq k n x) =
      K T P k n x := Classical.choose_spec x.property

theorem J_mem_cycles (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : ShiftedHom P n (T.obj k)) : J T P k n x ∈ cycles T P q hq k n := by
  change ∃ y, I T P (n - 1) (k + 1) (k + q) _ y = K T P k n (J T P k n x)
  refine ⟨0, ?_⟩
  rw [map_zero]
  exact ((RepresentedHom.exact_g P (T.layerCofiberSequence k) n _).2 ⟨x, rfl⟩).symm

theorem cycles_one (k n : ℤ) : cycles T P 1 (by omega) k n = ⊤ := by
  apply top_unique
  intro x _
  refine ⟨K T P k n x, ?_⟩
  change K T P k n x ≫ T.map (k + 1) (k + ↑(1 : ℕ)) _ = _
  simp

theorem boundaries_one (k n : ℤ) : boundaries T P 1 (by omega) k n = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨y, hy, rfl⟩
  have hker (a : ℤ) (ha : a ≤ k) (he : a = k)
      (u : ShiftedHom P n (T.obj k)) (hu : I T P n a k ha u = 0) : u = 0 := by
    subst a
    simpa [I, postcomposeLinearMap, T.map_self] using hu
  have hy' : y = 0 := hker _ _ (by omega) y hy
  simp [hy']

theorem cycles_antitone (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r) (hqr : q ≤ r)
    (k n : ℤ) : cycles T P r hr k n ≤ cycles T P q hq k n := by
  rintro x ⟨y, hy⟩
  refine ⟨I T P (n - 1) (k + q) (k + r) (by omega) y, ?_⟩
  change (y ≫ T.map (k + q) (k + r) _) ≫ T.map (k + 1) (k + q) _ = _
  rw [Category.assoc, DescendingTower.map_comp]
  exact hy

theorem boundaries_monotone (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r) (hqr : q ≤ r)
    (k n : ℤ) : boundaries T P q hq k n ≤ boundaries T P r hr k n := by
  rintro x ⟨y, hy, hxy⟩
  refine ⟨y, ?_, hxy⟩
  change y ≫ T.map (k - r + 1) k _ = 0
  change y ≫ T.map (k - q + 1) k _ = 0 at hy
  rw [← T.map_comp (k - r + 1) (k - q + 1) k (by omega) (by omega),
    ← Category.assoc, hy, Limits.zero_comp]

/-- Every boundary has zero connecting image, hence is a cycle at every level. -/
theorem boundaries_le_cycles (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r) (k n : ℤ) :
    boundaries T P q hq k n ≤ cycles T P r hr k n := by
  rintro x ⟨y, _, rfl⟩
  exact J_mem_cycles T P r hr k n y

end KIP126.StableHomotopy.TowerSpectralSequence
