module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Pushout.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Stability.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
set_option backward.isDefEq.respectTransparency false

private instance (n : ℕ) : T2Space (cubeBoundaryObject.{0} n) :=
  inferInstanceAs (T2Space (ULift.{0} (↥(_root_.Cube.boundary (Fin n)))))

private instance (n : ℕ) :
    UCompactlyGeneratedSpace.{0} (BasedSpace.adjoinPoint (cubeBoundaryObject.{0} n)) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{0} ((cubeBoundaryObject.{0} n) ⊕ PUnit))

private instance (n : ℕ) :
    UCompactlyGeneratedSpace.{0} (BasedSpace.adjoinPoint (cubeObject.{0} n)) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{0} ((cubeObject.{0} n) ⊕ PUnit))

/-- Smashing the inclusion of an actual attached cubical parameter
cell with a cofibrant spectrum gives an actual cubical cofibration. -/
theorem spaceSmashMap_cubeAttachment_isCubicalCofibration
    (n : ℕ) {C D : BasedSpace.{0}} [UCompactlyGeneratedSpace.{0} C]
    {a : BasedSpace.adjoinPoint (cubeBoundaryObject n) ⟶ C}
    {i : BasedSpace.adjoinPoint (cubeObject n) ⟶ D} {j : C ⟶ D}
    (h : IsPushout (BasedSpace.adjoinPointMap (cubeBoundaryInclusion n)) a i j)
    {X : Prespectrum.{0}} (hX : IsCubicallyCofibrant X) :
    IsCubicalCofibration (spaceSmashMap j (𝟙 X)) :=
  IsCubicalCofibration.pushout (spaceSmashCubeBoundaryMap_isCubicalCofibration hX n)
    (spaceSmashParameter_isPushout h X)

/-- An actual parameter-cell attachment retains the proved cofibrancy
of the old parameter smash, including dimension zero. -/
theorem IsCubicallyCofibrant.spaceSmash_cubeAttachment
    (n : ℕ) {C D : BasedSpace.{0}} [UCompactlyGeneratedSpace.{0} C]
    {a : BasedSpace.adjoinPoint (cubeBoundaryObject n) ⟶ C}
    {i : BasedSpace.adjoinPoint (cubeObject n) ⟶ D} {j : C ⟶ D}
    (h : IsPushout (BasedSpace.adjoinPointMap (cubeBoundaryInclusion n)) a i j)
    {X : Prespectrum.{0}} (hX : IsCubicallyCofibrant X)
    (hC : IsCubicallyCofibrant (spaceSmash C X)) :
    IsCubicallyCofibrant (spaceSmash D X) :=
  hC.of_cubicalCofibration (spaceSmashMap_cubeAttachment_isCubicalCofibration n h hX)

/-- Stable smash invariance extends across an actual cubical parameter
cell. The boundary, disk and their inclusion use their original maps,
and their required properties have already been proved for every dimension. -/
theorem spaceSmashMap_cubeAttachment_stableEquivalence
    (n : ℕ) {C D : BasedSpace.{0}} [UCompactlyGeneratedSpace.{0} C]
    {a : BasedSpace.adjoinPoint (cubeBoundaryObject n) ⟶ C}
    {i : BasedSpace.adjoinPoint (cubeObject n) ⟶ D} {j : C ⟶ D}
    (h : IsPushout (BasedSpace.adjoinPointMap (cubeBoundaryInclusion n)) a i j)
    {X Y : Prespectrum.{0}} (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y)
    (f : X ⟶ Y) (hf : stableEquivalences f)
    (hCX : IsCubicallyCofibrant (spaceSmash C X))
    (hCY : IsCubicallyCofibrant (spaceSmash C Y))
    (hC : stableEquivalences (spaceSmashMap (𝟙 C) f)) :
    stableEquivalences (spaceSmashMap (𝟙 D) f) :=
  spaceSmashMap_stableEquivalence_of_parameter_pushout h f
    (hX.spaceSmash_cubeBoundary n) hCX (hY.spaceSmash_cubeBoundary n) hCY
    (spaceSmashCubeBoundaryMap_isCubicalCofibration hX n)
    (spaceSmashCubeBoundaryMap_isCubicalCofibration hY n)
    (spaceSmashMap_cubeBoundary_stableEquivalence n hX hY f hf)
    (spaceSmashMap_cube_stableEquivalence n f hf) hC

end KIP126.StableHomotopy.Implementation.Prespectrum
