import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Sphere.Proofs
import KIP126.Def.ClassicalAdams.TowerSequence.NextHomology.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.Permanence.Proofs

/-! Nonzero filtration-one sphere cycles give nonzero second-page classes.
The representative is retained; no coordinates or page-comparison axiom
are used. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))

/-- A nonzero cycle in filtration one cannot be an incoming first-page
boundary, since the first differential from filtration zero vanishes. -/
theorem sphereAdamsPageTwo_nonzero_of_first_cycle (t : ℤ)
    (z : adamsPage H.unit SphereSpectrum 1 le_rfl 1 t) (hz : z ≠ 0)
    (hd : (adamsPageD H.unit SphereSpectrum 1 le_rfl (1, t) (2, t)).hom z = 0) :
    ∃ u : adamsCycles H.unit SphereSpectrum 2 (by decide) 1 t,
      adamsNextCycleToPage H.unit SphereSpectrum 1 le_rfl 1 t u = z ∧
      (adamsCycleBoundaries H.unit SphereSpectrum 2 (by decide) 1 t).mkQ u ≠ 0 := by
  obtain ⟨x, hx⟩ := (adamsCycleBoundaries H.unit SphereSpectrum 1 le_rfl 1 t).mkQ_surjective z
  have hd' : adamsDifferential H.unit SphereSpectrum 1 le_rfl 1 t z = 0 := by
    have ht : ((2, t) : ℤ × ℤ) = ((1 : ℤ) + (1 : ℕ), t + (1 : ℕ) - 1) := by
      apply Prod.ext <;> omega
    rw [ht, adamsPageD_target] at hd
    exact hd
  rw [← hx, adamsDifferential_mk] at hd'
  let u : adamsCycles H.unit SphereSpectrum 2 (by decide) 1 t :=
    ⟨x.val, (adamsDifferentialValue_eq_zero_iff H.unit SphereSpectrum 1 le_rfl 1 t x).mp hd'⟩
  have hu : adamsNextCycleToPage H.unit SphereSpectrum 1 le_rfl 1 t u = z := hx
  refine ⟨u, hu, ?_⟩
  intro hzero
  have hb : u.val ∈ adamsBoundaries H.unit SphereSpectrum 2 (by decide) 1 t :=
    (adamsPage_mk_eq_zero H.unit SphereSpectrum 2 (by decide) 1 t u).mp hzero
  have hin : ∃ y : adamsPage H.unit SphereSpectrum 1 le_rfl 0 t,
      (adamsPageD H.unit SphereSpectrum 1 le_rfl (0, t) (1, t)).hom y =
        adamsNextCycleToPage H.unit SphereSpectrum 1 le_rfl 1 t u := by
    have h := adamsNextBoundary_is_differential H.unit SphereSpectrum 1 le_rfl 0 t
    change ∀ x : adamsCycles H.unit SphereSpectrum 2 (by decide) (0 + 1) (t + 1 - 1),
      x.val ∈ adamsBoundaries H.unit SphereSpectrum 2 (by decide) (0 + 1) (t + 1 - 1) →
      ∃ y, (ModuleCat.ofHom (adamsDifferential H.unit SphereSpectrum 1 le_rfl 0 t)).hom y =
        adamsNextCycleToPage H.unit SphereSpectrum 1 le_rfl (0 + 1) (t + 1 - 1) x at h
    rw [← adamsPageD_target] at h
    erw [show (0 : ℤ) + 1 = 1 by omega, show t + 1 - 1 = t by omega] at h
    exact h u hb
  obtain ⟨y, hy⟩ := hin
  exact hz (hu.symm.trans (hy.symm.trans (sphereAdamsPageD_one_filtration_zero H t y)))

end

end KIP126.Classical.Adams
