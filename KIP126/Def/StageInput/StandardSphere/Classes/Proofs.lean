import KIP126.Def.StageInput.StandardSphere.Classes.Data
import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Internal.Proofs

namespace KIP126.Classical.Adams

/-- Standard nonvanishing on E₂ uses the specified Milnor cocycle, not C(M).
It does not imply that this class survives to later pages. -/
theorem standardH6Square_ne_zero : standardH6Square ≠ 0 :=
  Sphere.Internal.hiSquare_six_ne_zero standardFoundation.hf2 standardMilnorCooperations

end KIP126.Classical.Adams
