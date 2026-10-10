import KIP126.Mathlib.ClassicalAdams.StandardSphere.Data
import KIP126.Def.ClassicalAdams.SphereClasses.Proofs

namespace KIP126.Classical.Adams

/-- The fixed Milnor-specified square is nonzero on the constructed second
page. This uses the fixed foundation and Milnor coordinates, but neither
the Lin presentation nor the specified-class comparison or permanence. -/
theorem sphereH6Square_ne_zero : sphereH6Square ≠ 0 :=
  Sphere.h6Square_ne_zero standardFoundation.hf2 standardMilnorCooperations

end KIP126.Classical.Adams
