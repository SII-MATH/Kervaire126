module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Coordinates.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Pushout.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
set_option backward.isDefEq.respectTransparency false

local instance (n : ℕ) : T2Space (cubeBoundaryObject.{0} n) :=
  inferInstanceAs (T2Space (ULift.{0} (↥(_root_.Cube.boundary (Fin n)))))

/-- The original successor boundary is the actual relative-cylinder
boundary pushout. Both endpoints and the whole lower-dimensional
boundary cylinder are retained by the displayed original maps. -/
theorem spaceSmashCubeBoundaryCylinder_isPushout (n : ℕ) (X : Prespectrum.{0})
    [∀ k, UCompactlyGeneratedSpace.{0} (X.level k)] :
    IsPushout (coprod.map (spaceSmashCubeBoundaryMap n X) (spaceSmashCubeBoundaryMap n X))
      (cylinderEndpoints (spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryObject n)) X))
      ((spaceSmashParameterEndpointsIso (cubeObject n) X).inv ≫
        spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductEndInclusion n)) (𝟙 X))
      ((spaceSmashParameterCylinderIso (cubeBoundaryObject n) X).inv ≫
        spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductSideInclusion n)) (𝟙 X)) := by
  apply (spaceSmashCubeBoundaryProduct_isPushout n X).of_iso
    (spaceSmashParameterEndpointsIso (cubeBoundaryObject n) X)
    (spaceSmashParameterEndpointsIso (cubeObject n) X)
    (spaceSmashParameterCylinderIso (cubeBoundaryObject n) X) (Iso.refl _)
  · exact spaceSmashParameterEndpointsIso_natural (cubeBoundaryInclusion n) X
  · exact spaceSmashParameterBoundaryToCylinder_square (cubeBoundaryObject n) X
  · change _ ≫ 𝟙 _ = _
    rw [Category.comp_id,Iso.hom_inv_id_assoc]
  · change _ ≫ 𝟙 _ = _
    rw [Category.comp_id,Iso.hom_inv_id_assoc]

end KIP126.StableHomotopy.Implementation.Prespectrum
