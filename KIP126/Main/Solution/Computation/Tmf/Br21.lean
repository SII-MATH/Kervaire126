import KIP126.Interface.Challenge.Challenge2
import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Proofs

/-! BR21's source differential on the same tmf coordinates consumed by Main.
The equation is derived from one Challenge2 delivery rather than added as a
new computation input. Its transport uses the existing, unfinished generic
Adams tower naturality theorem. -/

namespace KIP126.Main.Solution.Computation

open KIP126.Classical.Adams KIP126.Core.SpectralSequence

/-- Transport BR21's d₃(w₂²) = βg⁴ through the delivered source comparison,
then use the proved identity βg⁴ = β⁵g in that same coordinate algebra.
This gives a differential equation, without asserting later-page nonvanishing. -/
theorem tmf_br21_d3 (input : KIP126.Challenge2) :
    HasDifferential
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit
        KIP126.Def.standardTmfTarget.X)
      3 (16, 112) (19, 114)
      input.computation.bindings.tmfCoordinates.v2Sixteen
      input.computation.bindings.tmfCoordinates.betaFiveG := by
  have transported := adamsInternalE2Induced_hasDifferential
    standardFoundation.hf2.unit
    input.literature.bindings.route.tmfBinding.detectorIso.inv
    input.literature.results.br21
  rw [← input.computation.bindings.tmf_v2Sixteen,
    ← input.computation.bindings.tmf_betaGFour,
    Tmf.E2Presentation.betaGFour_eq_betaFiveG] at transported
  exact transported

end KIP126.Main.Solution.Computation
