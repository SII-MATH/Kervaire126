import KIP126.Def.Synthetic.EInfty.Shift.Canonical.Proofs
import KIP126.Def.StageInput.StandardSphere.Route.Fixed

/-! Fix the weight comparison from the one actual standard tower.
Its unfinished descent/invertibility obligations are named in the generic
existence theorem; no literature delivery chooses these isomorphisms. -/
namespace KIP126.Def

/-- The prescribed quotient of the actual standard weight-tower map. -/
noncomputable def standardEInftyWeightShift :
    KIP126.Synthetic.SpectralSequence.EInftyWeightShift
      KIP126.Classical.Adams.standardRouteModel.family :=
  Classical.choose
    (KIP126.Synthetic.SpectralSequence.canonicalWeightShift_exists
      KIP126.Classical.Adams.standardRouteModel.towerPresentation)

end KIP126.Def
