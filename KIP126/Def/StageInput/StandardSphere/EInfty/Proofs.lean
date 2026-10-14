module

public import KIP126.Def.StageInput.StandardSphere.EInfty.Data

@[expose] public section

namespace KIP126.Def

/-- Naturality of the weight comparison fixed by the standard Adams tower.
This specializes the generic canonical-comparison theorem and retains its
unfinished tower-map comparison and the fixed model's construction debt. -/
theorem standardEInftyWeightShift_natural : standardEInftyWeightShift.Natural := by
  exact KIP126.Synthetic.SpectralSequence.CanonicalWeightShift.natural
    KIP126.Classical.Adams.standardRouteModel.towerPresentation
    standardEInftyWeightShift
    (Classical.choose_spec
      (KIP126.Synthetic.SpectralSequence.canonicalWeightShift_exists
        KIP126.Classical.Adams.standardRouteModel.towerPresentation))

end KIP126.Def
