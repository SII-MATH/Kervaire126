module

public import KIP126.Def.SpectralSequence.Permanence.Proofs

@[expose] public section

/-! Internal permanence keeps zero cycles separate from nonzero survival. -/

namespace KIP126.Checks.SpectralSequence.InternalPermanence

open CategoryTheory KIP126.Core.SpectralSequence
universe u v
variable {R : Type u} [Ring R]
  (E : KIP126.Core.SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)) (p : ℤ × ℤ)

example (r : ℤ) (hr : 2 ≤ r) : ReachesPage E r p 0 :=
  ⟨0, hr, 0, map_zero _, map_zero _⟩

example : IsPermanentCycle E p 0 := ⟨0, map_zero _⟩

example : ¬ NonzeroSurvival E p 0 := by
  rintro ⟨z, hz, hne⟩
  apply hne
  have h := (E.ssData p).infinity_projection_eq_of_page_projection_eq
    (↑(2 - E.r₀).toNat) z 0 (by simpa only [map_zero] using hz)
  simpa only [map_zero] using h

end KIP126.Checks.SpectralSequence.InternalPermanence
