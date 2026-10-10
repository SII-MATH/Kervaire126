import KIP126.Def.ClassicalAdams.SphereInitial.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))

/-- There is no new boundary in filtration one: the first incoming
differential is zero, and all later sources have negative filtration. -/
theorem sphereAdamsBoundaries_filtration_one_succ (r : ℕ) (hr : 1 ≤ r) (t : ℤ) :
    adamsBoundaries H.unit SphereSpectrum (r + 1) (by omega) 1 t =
      adamsBoundaries H.unit SphereSpectrum r hr 1 t := by
  by_cases he : r = 1
  · subst r
    have h := adamsBoundaries_succ_eq_of_differential_zero H.unit SphereSpectrum
      1 le_rfl 0 t (sphereAdamsDifferential_filtration_zero H 1 le_rfl t)
    have ht : t + (1 : ℕ) - 1 = t := by omega
    exact ht ▸ h
  · have h := adamsBoundaries_succ_eq_of_source_subsingleton H.unit SphereSpectrum
      r hr (1 - r) (t - r + 1)
      (adamsPage_subsingleton_of_negative H.unit SphereSpectrum r hr
        (1 - r) (t - r + 1) (by omega))
    have hs : (1 : ℤ) - r + r = 1 := by omega
    have ht : t - r + 1 + r - 1 = t := by omega
    exact hs ▸ ht ▸ h

/-- No boundary exists in sphere filtration one, in any internal degree
or finite page. This uses neither Lin data nor a multiplication hypothesis. -/
theorem sphereAdamsBoundaries_filtration_one (r : ℕ) (hr : 1 ≤ r) (t : ℤ) :
    adamsBoundaries H.unit SphereSpectrum r hr 1 t = ⊥ := by
  induction r, hr using Nat.le_induction with
  | base => exact adamsBoundaries_one H.unit SphereSpectrum 1 t
  | succ r hr ih =>
    exact (sphereAdamsBoundaries_filtration_one_succ H r hr t).trans ih

end
end KIP126.Classical.Adams
