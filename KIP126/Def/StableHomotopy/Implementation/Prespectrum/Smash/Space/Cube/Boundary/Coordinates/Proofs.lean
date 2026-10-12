module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Cylinder.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Product.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The two end faces retain exactly their endpoint and cube coordinates
after the actual successor-cube homeomorphism. -/
@[reassoc] theorem spaceSmashCubeBoundaryEnd_coordinates (n : ℕ) (X : Prespectrum.{0}) :
    spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductEndInclusion n)) (𝟙 X) ≫
      spaceSmashCubeBoundaryMap (n+1) X ≫
        (spaceSmashIso (BasedSpace.adjoinPointCubeSuccIso n) (Iso.refl X)).hom =
      spaceSmashMap (BasedSpace.adjoinPointMap
        (TopCat.ofHom (intervalBoundaryInclusion.hom.prodMap (ContinuousMap.id (cubeObject n))))) (𝟙 X) := by
  apply Hom.ext
  funext k
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,x⟩
  change (spaceSmashMap (BasedSpace.adjoinPointCubeSuccIso n).hom (𝟙 X)).level k
    ((spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryInclusion (n+1))) (𝟙 X)).level k
      ((spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductEndInclusion n)) (𝟙 X)).level k
        (BasedSpace.smashPoint _ _ a x))) = _
  rw [spaceSmashMap_apply,spaceSmashMap_apply,spaceSmashMap_apply]
  change _ = (spaceSmashMap _ (𝟙 X)).level k (BasedSpace.smashPoint _ _ a x)
  rw [spaceSmashMap_apply]
  cases a <;> rfl

/-- The side faces retain the original side-boundary inclusion in
the second coordinate of the successor cube. -/
@[reassoc] theorem spaceSmashCubeBoundarySide_coordinates (n : ℕ) (X : Prespectrum.{0}) :
    spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductSideInclusion n)) (𝟙 X) ≫
      spaceSmashCubeBoundaryMap (n+1) X ≫
        (spaceSmashIso (BasedSpace.adjoinPointCubeSuccIso n) (Iso.refl X)).hom =
      spaceSmashMap (BasedSpace.adjoinPointMap
        (TopCat.ofHom ((ContinuousMap.id I).prodMap (cubeBoundaryInclusion n).hom))) (𝟙 X) := by
  apply Hom.ext
  funext k
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,x⟩
  change (spaceSmashMap (BasedSpace.adjoinPointCubeSuccIso n).hom (𝟙 X)).level k
    ((spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryInclusion (n+1))) (𝟙 X)).level k
      ((spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductSideInclusion n)) (𝟙 X)).level k
        (BasedSpace.smashPoint _ _ a x))) = _
  rw [spaceSmashMap_apply,spaceSmashMap_apply,spaceSmashMap_apply]
  change _ = (spaceSmashMap _ (𝟙 X)).level k (BasedSpace.smashPoint _ _ a x)
  rw [spaceSmashMap_apply]
  cases a <;> rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
