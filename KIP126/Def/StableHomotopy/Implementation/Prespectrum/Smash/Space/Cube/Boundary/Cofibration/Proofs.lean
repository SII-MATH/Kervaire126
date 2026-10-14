module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Coordinates.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Pushout.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Cylinder.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Relative.Pushout.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Empty.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Zero.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

private instance (n : ℕ) : T2Space (cubeBoundaryObject.{0} n) :=
  inferInstanceAs (T2Space (ULift.{0} (↥(_root_.Cube.boundary (Fin n)))))

/-- For every finite dimension, the whole original cube-boundary
tensor inclusion has the actual cubical left lifting property. The
successor step uses the proved end/side pushout and relative cylinder
lifting, with the original coordinate comparisons retained. -/
theorem spaceSmashCubeBoundaryMap_isCubicalCofibration
    {X : Prespectrum.{0}} (hX : IsCubicallyCofibrant X) (n : ℕ) :
    IsCubicalCofibration (spaceSmashCubeBoundaryMap n X) := by
  letI (k : ℕ) := hX.level_uCompactlyGeneratedSpace k
  induction n with
  | zero =>
    letI : IsEmpty (cubeBoundaryObject.{0} 0) := ⟨fun z => by
      obtain ⟨j,hj⟩ := z.down.property
      exact Fin.elim0 j⟩
    intro E B p hp
    exact IsCubicallyCofibrant.map_from_isZero (hX.spaceSmash_cube 0)
      (spaceSmash_adjoinPoint_isZero (cubeBoundaryObject 0) X) _ p hp
  | succ n ih =>
    let A := spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryObject n)) X
    let B := spaceSmash (BasedSpace.adjoinPoint (cubeObject n)) X
    let i : A ⟶ B := spaceSmashCubeBoundaryMap n X
    let e₁ := spaceSmashParameterEndpointsIso (cubeBoundaryObject n) X
    let e₂ := spaceSmashParameterEndpointsIso (cubeObject n) X
    let e₃ := spaceSmashParameterCylinderIso (cubeBoundaryObject n) X
    let E := spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductEndInclusion n)) (𝟙 X)
    let S := spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductSideInclusion n)) (𝟙 X)
    let a : B ⨿ B ⟶ spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) X := e₂.inv ≫ E
    let b : cylinderFunctor.obj A ⟶ spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) X := e₃.inv ≫ S
    have hp : IsPushout (coprod.map i i) (cylinderEndpoints A) a b :=
      spaceSmashCubeBoundaryCylinder_isPushout n X
    let e : spaceSmash (BasedSpace.adjoinPoint (cubeObject (n+1))) X ≅ cylinderFunctor.obj B :=
      spaceSmashIso (BasedSpace.adjoinPointCubeSuccIso n) (Iso.refl X) ≪≫
        spaceSmashParameterCylinderIso (cubeObject n) X
    let j := spaceSmashCubeBoundaryMap (n+1) X ≫ e.hom
    have hE : E ≫ j = e₂.hom ≫ cylinderEndpoints B := by
      change E ≫ spaceSmashCubeBoundaryMap (n+1) X ≫
        (spaceSmashIso (BasedSpace.adjoinPointCubeSuccIso n) (Iso.refl X)).hom ≫
          (spaceSmashParameterCylinderIso (cubeObject n) X).hom = _
      dsimp only [E]
      rw [spaceSmashCubeBoundaryEnd_coordinates_assoc]
      exact spaceSmashParameterBoundaryToCylinder_square (cubeObject n) X
    have hS : S ≫ j = e₃.hom ≫ cylinderFunctor.map i := by
      change S ≫ spaceSmashCubeBoundaryMap (n+1) X ≫
        (spaceSmashIso (BasedSpace.adjoinPointCubeSuccIso n) (Iso.refl X)).hom ≫
          (spaceSmashParameterCylinderIso (cubeObject n) X).hom = _
      dsimp only [S]
      rw [spaceSmashCubeBoundarySide_coordinates_assoc]
      exact spaceSmashParameterCylinderIso_natural (cubeBoundaryInclusion n) X
    have hj : IsCubicalCofibration j := by
      apply IsCubicalCofibration.cylinderPushoutProduct_of_isPushout ih hp j
      · dsimp only [a]
        rw [Category.assoc,hE,Iso.inv_hom_id_assoc]
      · dsimp only [b]
        rw [Category.assoc,hS,Iso.inv_hom_id_assoc]
    have he : spaceSmashCubeBoundaryMap (n+1) X = j ≫ e.inv := by
      dsimp only [j]
      rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    rw [he]
    intro U V p hUV
    exact IsCubicalCofibration.comp hj (isCubicalCofibration_of_isIso e.inv) p hUV

end KIP126.StableHomotopy.Implementation.Prespectrum
