import KIP126.Def.SpectralSequence.Basic.Data
import Mathlib.Algebra.Category.ModuleCat.Abelian

namespace KIP126.Classical.Adams

/-- Internal Adams interface. The spectrum and table identity are separate
comparison obligations; this structure alone does not assert permanence. -/
structure AdamsSSData where
  sequence : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ)
  firstPage : sequence.r₀ = 2
  differentialDegree : ∀ r, sequence.diffDeg r = (r, r - 1)

end KIP126.Classical.Adams
