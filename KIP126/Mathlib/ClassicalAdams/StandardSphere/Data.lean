import KIP126.Def.StageInput.Milnor
import KIP126.Def.ClassicalAdams.SphereClasses.Data
import KIP126.Def.ClassicalAdams.Mod2Sphere.Data

namespace KIP126.Classical.Adams

/-- The fixed standard sphere sequence: reuse the actual tower construction. -/
noncomputable def sphereAdams := mod2SphereAdams standardFoundation.hf2

/-- The fixed standard class, still defined by the Milnor cocycle, independently
of the Lin table and of the computational comparison. -/
noncomputable def sphereH6Square :
    (sphereAdams.page 2 (by decide)).X (2, 128) :=
  Sphere.h6Square standardFoundation.hf2 standardMilnorCooperations

end KIP126.Classical.Adams
