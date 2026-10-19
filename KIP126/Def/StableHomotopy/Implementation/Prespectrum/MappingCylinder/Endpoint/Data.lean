module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Adjunction.Hom.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u

/-- Both original endpoints include into the actual reduced cylinder,
using the actual strict binary coproduct. -/
noncomputable def cylinderEndpoints (X : Prespectrum.{u}) : X ⨿ X ⟶ cylinderFunctor.obj X :=
  coprod.desc (mappingCylinderInclusion (𝟙 X)) (mappingCylinderSection (𝟙 X))

end KIP126.StableHomotopy.Implementation.Prespectrum
