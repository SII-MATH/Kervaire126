import KIP126.Def.ClassicalAdams.SSDataModel.Data
import KIP126.Def.StageInput.Foundation
import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data

namespace KIP126.Classical.Adams

open KIP126.StableHomotopy

/-- The internal sphere Adams sequence constructed from the foundation in M.
This specializes the actual sphere tower; it does not select a second sequence
or require a Lin presentation, CSV basis certificate, or computed differential.
The foundation is fixed by Def's own implementation construction. -/
noncomputable def sphereAdamsModel : AdamsSSData where
  sequence := adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum
  firstPage := rfl
  differentialDegree _ := rfl

/-- The same internal sequence used by both the standard target and C(M). -/
noncomputable abbrev sphereAdamsData := sphereAdamsModel.sequence

end KIP126.Classical.Adams
