module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Cylinder.Data
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Functor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Product.Naturality.Inverse.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

local instance : T2Space intervalBoundaryObject :=
  inferInstanceAs (T2Space {t : I // t = 0 ∨ t = 1})

/-- Cylinder identification retains the actual map of the second
parameter. -/
@[reassoc] theorem spaceSmashParameterCylinderIso_natural
    {T T' : TopCat.{0}} [CompactSpace T] [T2Space T] [CompactSpace T'] [T2Space T']
    (b : T ⟶ T') (X : Prespectrum.{0}) :
    spaceSmashMap (BasedSpace.adjoinPointMap
        (TopCat.ofHom ((ContinuousMap.id I).prodMap b.hom))) (𝟙 X) ≫
          (spaceSmashParameterCylinderIso T' X).hom =
      (spaceSmashParameterCylinderIso T X).hom ≫
        cylinderFunctor.map (spaceSmashMap (BasedSpace.adjoinPointMap b) (𝟙 X)) := by
  change _ ≫ ((spaceSmashParameterProductIso (TopCat.of I) T' X).inv ≫
    spaceSmashIntervalComparison _) =
      ((spaceSmashParameterProductIso (TopCat.of I) T X).inv ≫ spaceSmashIntervalComparison _) ≫ _
  refine (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫
    spaceSmashIntervalComparison (spaceSmash (BasedSpace.adjoinPoint T') X))
      (spaceSmashParameterProductInverse_natural_parameters (𝟙 (TopCat.of I)) b (𝟙 X))).trans ?_)
  rw [Category.assoc]
  rw [BasedSpace.adjoinPointMap_id]
  exact (congrArg (fun k => (spaceSmashParameterProductIso (TopCat.of I) T X).inv ≫ k)
    (spaceSmashIntervalComparison_natural (spaceSmashMap (BasedSpace.adjoinPointMap b) (𝟙 X)))).trans
      (Category.assoc _ _ _).symm

/-- Endpoint identification retains the two original copies of the
actual map of the second parameter. -/
@[reassoc] theorem spaceSmashParameterEndpointsIso_natural
    {T T' : TopCat.{0}} [CompactSpace T] [T2Space T] [CompactSpace T'] [T2Space T']
    (b : T ⟶ T') (X : Prespectrum.{0}) :
    spaceSmashMap (BasedSpace.adjoinPointMap
        (TopCat.ofHom ((ContinuousMap.id intervalBoundaryObject).prodMap b.hom))) (𝟙 X) ≫
          (spaceSmashParameterEndpointsIso T' X).hom =
      (spaceSmashParameterEndpointsIso T X).hom ≫
        coprod.map (spaceSmashMap (BasedSpace.adjoinPointMap b) (𝟙 X))
          (spaceSmashMap (BasedSpace.adjoinPointMap b) (𝟙 X)) := by
  change _ ≫ ((spaceSmashParameterProductIso intervalBoundaryObject T' X).inv ≫
    spaceSmashIntervalBoundaryComparison _) =
      ((spaceSmashParameterProductIso intervalBoundaryObject T X).inv ≫
        spaceSmashIntervalBoundaryComparison _) ≫ _
  refine (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫
    spaceSmashIntervalBoundaryComparison (spaceSmash (BasedSpace.adjoinPoint T') X))
      (spaceSmashParameterProductInverse_natural_parameters (𝟙 intervalBoundaryObject) b (𝟙 X))).trans ?_)
  rw [Category.assoc]
  rw [BasedSpace.adjoinPointMap_id]
  exact (congrArg (fun k => (spaceSmashParameterProductIso intervalBoundaryObject T X).inv ≫ k)
    (spaceSmashIntervalBoundaryComparison_natural (spaceSmashMap (BasedSpace.adjoinPointMap b) (𝟙 X)))).trans
      (Category.assoc _ _ _).symm

/-- Including both actual parameter endpoints is exactly the whole
endpoint map of the original cylinder, under the strict comparisons. -/
@[reassoc] theorem spaceSmashParameterBoundaryToCylinder_square
    (T : TopCat.{0}) [CompactSpace T] [T2Space T] (X : Prespectrum.{0}) :
    spaceSmashMap (BasedSpace.adjoinPointMap
        (TopCat.ofHom (intervalBoundaryInclusion.hom.prodMap (ContinuousMap.id T)))) (𝟙 X) ≫
          (spaceSmashParameterCylinderIso T X).hom =
      (spaceSmashParameterEndpointsIso T X).hom ≫
        cylinderEndpoints (spaceSmash (BasedSpace.adjoinPoint T) X) := by
  change _ ≫ ((spaceSmashParameterProductIso (TopCat.of I) T X).inv ≫
    spaceSmashIntervalComparison _) =
      ((spaceSmashParameterProductIso intervalBoundaryObject T X).inv ≫
        spaceSmashIntervalBoundaryComparison _) ≫ _
  refine (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫
    spaceSmashIntervalComparison (spaceSmash (BasedSpace.adjoinPoint T) X))
      (spaceSmashParameterProductInverse_natural_parameters intervalBoundaryInclusion (𝟙 T) (𝟙 X))).trans ?_)
  rw [Category.assoc]
  have h : spaceSmashMap (BasedSpace.adjoinPointMap (𝟙 T)) (𝟙 X) =
      𝟙 (spaceSmash (BasedSpace.adjoinPoint T) X) := by
    rw [BasedSpace.adjoinPointMap_id,spaceSmashMap_id]
  change _ ≫ spaceSmashMap (BasedSpace.adjoinPointMap intervalBoundaryInclusion)
    (spaceSmashMap (BasedSpace.adjoinPointMap (𝟙 T)) (𝟙 X)) ≫ _ = _
  rw [h]
  change _ ≫ spaceSmashIntervalBoundaryMap _ ≫ _ = _
  exact (congrArg (fun k => (spaceSmashParameterProductIso intervalBoundaryObject T X).inv ≫ k)
    (spaceSmashIntervalBoundary_comparison_square (spaceSmash (BasedSpace.adjoinPoint T) X))).trans
      (Category.assoc _ _ _).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
