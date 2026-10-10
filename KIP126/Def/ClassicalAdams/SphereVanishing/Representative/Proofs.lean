import KIP126.Def.ClassicalAdams.SphereVanishing.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.Permanence.Representative.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Core.SpectralSequence

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))

/-- Any specified actual second-page representative can be used for the
all-stage liftability test at the square's bidegree. There is no further
existential search for a better representative. -/
theorem sphereAdams_h6_nonzeroSurvival_iff_representative
    (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (2, 128))
    (u : adamsCycleAmbient H.unit SphereSpectrum 2 128)
    (hu : (adamsCycleBoundaries H.unit SphereSpectrum 2 (by decide) 2 128).mkQ u =
      (adamsTowerSSDataPageIso H.unit SphereSpectrum 2 128 0).hom x) :
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (2, 128) x ↔
      x ≠ 0 ∧ ∀ n : ℕ, u.val ∈ adamsCycles H.unit SphereSpectrum (n + 2) (by omega) 2 128 := by
  rw [sphereAdams_h6_nonzeroSurvival_iff]
  constructor
  · rintro ⟨hx, z, hz, he⟩
    refine ⟨hx, fun n => ?_⟩
    exact (adamsCycles_mem_iff_of_page_eq H.unit SphereSpectrum 2 (n + 2)
      (by decide) (by omega) 2 128 u z (hu.trans he.symm)).mpr (hz n)
  · rintro ⟨hx, huZ⟩
    exact ⟨hx, u, huZ, hu⟩

end
end KIP126.Classical.Adams
