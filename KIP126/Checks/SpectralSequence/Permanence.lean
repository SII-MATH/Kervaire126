import KIP126.Mathlib.SpectralSequence.Permanence.Data
import KIP126.Def.SpectralSequence.Permanence.Proofs

/-! Type-level regressions for the elementwise permanence interface. -/

namespace KIP126.Checks.SpectralSequence.Permanence

open CategoryTheory
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

universe w

variable {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ r : ℤ}
variable (E : CategoryTheory.SpectralSequence F2ModuleCat c r₀)
variable (hr : r₀ ≤ r) (p : κ) (x : (E.page r hr).X p)

example (h : IsPermanent E r hr p x) : x ≠ 0 := h.ne_zero

example (trajectory : PageTrajectory E r hr p x) :
    trajectory.classAt 0 = x := trajectory.classAt_zero

end KIP126.Checks.SpectralSequence.Permanence

/-! The internal paper predicates must keep zero cycles separate from
nonzero survival, independently of the Mathlib trajectory interface above. -/
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
