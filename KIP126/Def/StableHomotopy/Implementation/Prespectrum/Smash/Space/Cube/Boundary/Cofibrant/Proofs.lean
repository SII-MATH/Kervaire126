module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Cylinder.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Coproduct.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting

set_option backward.isDefEq.respectTransparency false

/-- Every full original cube boundary, including the empty zero-dimensional
boundary, retains cubical cofibrancy when tensored with a cofibrant spectrum. -/
theorem IsCubicallyCofibrant.spaceSmash_cubeBoundary {X : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X) (n : ℕ) :
    IsCubicallyCofibrant (spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryObject n)) X) := by
  letI (k : ℕ) := hX.level_uCompactlyGeneratedSpace k
  induction n with
  | zero =>
    letI : IsEmpty (cubeBoundaryObject.{0} 0) := ⟨fun z => by
      obtain ⟨j,hj⟩ := z.down.property
      exact Fin.elim0 j⟩
    have hz := spaceSmash_adjoinPoint_isZero (cubeBoundaryObject 0) X
    intro E B p hp
    constructor
    intro a b sq
    exact CommSq.HasLift.mk' {
      l := zeroMap _ E
      fac_left := zeroPrespectrum_isZero.eq_of_src _ _
      fac_right := hz.eq_of_src _ _ }
  | succ n ih =>
    have hi : IsCubicalCofibration (spaceSmashCubeBoundaryMap n X) :=
      spaceSmashCubeBoundaryMap_isCubicalCofibration hX n
    intro E B p hp
    exact IsCubicallyCofibrant.of_cubicalCofibration (ih.mappingCylinder ih (𝟙 _))
      (IsCubicalCofibration.pushout (hi.coprod hi)
        (spaceSmashCubeBoundaryCylinder_isPushout n X)) p hp

/-- The actual intersection-to-end-faces map retains cubical cofibrancy,
through its strict identification with the two copies of the full boundary inclusion. -/
theorem spaceSmashCubeBoundaryProductTop_isCubicalCofibration {X : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X) (n : ℕ) :
    IsCubicalCofibration
      (spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductTop n)) (𝟙 X)) := by
  letI : T2Space (cubeBoundaryObject.{0} n) :=
    inferInstanceAs (T2Space (ULift.{0} (↥(_root_.Cube.boundary (Fin n)))))
  let e₁ := spaceSmashParameterEndpointsIso (cubeBoundaryObject n) X
  let e₂ := spaceSmashParameterEndpointsIso (cubeObject n) X
  let i := spaceSmashCubeBoundaryMap n X
  have hnat : spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductTop n)) (𝟙 X) ≫ e₂.hom =
      e₁.hom ≫ coprod.map i i := spaceSmashParameterEndpointsIso_natural (cubeBoundaryInclusion n) X
  have he : spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductTop n)) (𝟙 X) =
      e₁.hom ≫ coprod.map i i ≫ e₂.inv := by
    rw [← Category.assoc,← hnat,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rw [he]
  have hi : IsCubicalCofibration i := spaceSmashCubeBoundaryMap_isCubicalCofibration hX n
  intro E B p hp
  exact IsCubicalCofibration.comp (isCubicalCofibration_of_isIso e₁.hom)
    (IsCubicalCofibration.comp (hi.coprod hi) (isCubicalCofibration_of_isIso e₂.inv)) p hp

end KIP126.StableHomotopy.Implementation.Prespectrum
