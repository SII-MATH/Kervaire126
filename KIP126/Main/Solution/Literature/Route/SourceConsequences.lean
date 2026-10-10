import KIP126.Interface.Challenge.Challenge2
import KIP126.Def.StageInput.StandardSphere.EInfty.Data

/-! Internal specializations of the delivered literature on the fixed route.
These are Main proof obligations, not additional external input fields. -/
namespace KIP126.Main.Solution.Literature

open KIP126.Classical.Adams KIP126.Literature.Route

/-- Specialize the one general sphere Moss statement to the E₃ defining
system for ⟨h₅²,h₀,B⟩. The proof must compare the actual sphere mapping
sequence, its composition and detection with the fixed Milnor classes and
this delivery's source convergence. Defining systems, both noncrossing
conditions and residual injectivity remain in the conclusion's predicate.
The source theorem is projected from the same literature delivery; neither
an independent local Moss assumption nor a second model is selected. -/
theorem route_moss (literature : KIP126.Challenge2.LiteratureInterface) :
    MossSourceInput standardMilnorCooperations
      literature.bindings.route.classicalSource.convergence := by
  have sourceMoss := literature.results.moss
  sorry

/-- Naturality on every synthetic object is a consequence of the fixed
weight-tower construction. BHS's formulas on νX and its finite quotients
are not assumed to assert this full-category statement. The proof must use
the prescribed ambient map, naturality of the object weight isomorphism,
and naturality of the same tower presentation on E₂ before descent to E∞. -/
theorem eInfty_shift_natural
    (literature : KIP126.Challenge2.LiteratureInterface) :
    literature.bindings.eInftyWeightShift.Natural := by
  change KIP126.Def.standardEInftyWeightShift.Natural
  have canonical := Classical.choose_spec
    (KIP126.Synthetic.SpectralSequence.canonicalWeightShift_exists
      standardRouteModel.towerPresentation)
  sorry

end KIP126.Main.Solution.Literature
