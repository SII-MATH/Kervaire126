module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Contraction.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual deformation is a strict map into the actual path prespectrum. -/
noncomputable def mappingCylinderHomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingCylinder f ⟶ pathPrespectrum (mappingCylinder f) where
  level n := (mappingCylinderContraction f n).curry
  point n := by
    apply ContinuousMap.ext
    intro s
    exact mappingCylinderContraction_point f n s
  bond n z t := by
    apply ContinuousMap.ext
    intro s
    exact mappingCylinderContraction_bond f n z s t

end KIP126.StableHomotopy.Implementation.Prespectrum
