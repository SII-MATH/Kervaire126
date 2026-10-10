import KIP126.Def.ClassicalAdams.SphereInitial.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.Permanence.Proofs

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Core.SpectralSequence

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))

/-- In filtration zero the actual internal sphere sequence has nonzero
survival exactly for its nonzero initial classes. This proves the starting
column, not the filtration-two `h₆²` assertion. No coordinate input is used. -/
theorem sphereAdams_nonzeroSurvival_filtration_zero_iff (t : ℤ)
    (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (0, t)) :
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (0, t) x ↔
      x ≠ 0 := by
  rw [adamsTower_nonzeroSurvival_iff]
  let e := adamsTowerSSDataPageIso H.unit SphereSpectrum 0 t 0
  constructor
  · rintro ⟨z, _, hb, hz⟩ hx
    have hzero : (adamsCycleBoundaries H.unit SphereSpectrum 2 (by omega) 0 t).mkQ z = 0 :=
      hz.trans (by rw [hx]; exact e.hom.hom.map_zero)
    exact hb 0 ((adamsPage_mk_eq_zero H.unit SphereSpectrum 2 (by omega) 0 t z).mp hzero)
  · intro hx
    obtain ⟨z, hz⟩ := (adamsCycleBoundaries H.unit SphereSpectrum 2 (by omega) 0 t).mkQ_surjective
      (e.hom x)
    refine ⟨z, ?_, ?_, hz⟩
    · intro n
      rw [sphereAdamsCycles_filtration_zero]
      exact Submodule.mem_top
    · intro n hb
      have hz0 : z = 0 := Subtype.ext (by simpa [adamsBoundaries_filtration_zero] using hb)
      apply hx
      apply e.toLinearEquiv.map_eq_zero_iff.mp
      exact hz.symm.trans (by rw [hz0]; exact map_zero _)

end

end KIP126.Classical.Adams
