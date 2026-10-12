module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Colimit.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Functor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cube.Boundary.Stability.General.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
set_option backward.isDefEq.respectTransparency false

/-- Stable gluing for the original parameter pushout only needs actual
levelwise based homotopy extension of its specified tensor leg. -/
theorem spaceSmashMap_stableEquivalence_of_parameter_pushout_based
    {A B C D : BasedSpace.{0}} [UCompactlyGeneratedSpace.{0} A]
    [UCompactlyGeneratedSpace.{0} B] [UCompactlyGeneratedSpace.{0} C]
    {a : A ⟶ B} {b : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout a b i j) {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (haX : ∀ k, BasedSpace.HasBasedHomotopyExtension
      ((evaluationFunctor k).map (spaceSmashMap a (𝟙 X))))
    (haY : ∀ k, BasedSpace.HasBasedHomotopyExtension
      ((evaluationFunctor k).map (spaceSmashMap a (𝟙 Y))))
    (hfA : stableEquivalences (spaceSmashMap (𝟙 A) f))
    (hfB : stableEquivalences (spaceSmashMap (𝟙 B) f))
    (hfC : stableEquivalences (spaceSmashMap (𝟙 C) f)) :
    stableEquivalences (spaceSmashMap (𝟙 D) f) :=
  isPushout_stableEquivalence_gluing_of_based_homotopyExtension haX haY
    (spaceSmashParameter_isPushout h X) (spaceSmashParameter_isPushout h Y)
    (spaceSmashMap (𝟙 A) f) (spaceSmashMap (𝟙 B) f)
    (spaceSmashMap (𝟙 C) f) (spaceSmashMap (𝟙 D) f)
    (spaceSmashMap_parameter_natural a f) (spaceSmashMap_parameter_natural b f)
    (spaceSmashMap_parameter_natural i f) (spaceSmashMap_parameter_natural j f)
    hfA hfB hfC

/-- Stable invariance extends across one actual cubical parameter cell
for arbitrary original input spectra. The cubical boundary tensor's
based homotopy extension and stable invariance are proved, not assumed. -/
theorem spaceSmashMap_cubeAttachment_stableEquivalence_general
    (n : ℕ) {C D : BasedSpace.{0}} [UCompactlyGeneratedSpace.{0} C]
    {a : BasedSpace.adjoinPoint (cubeBoundaryObject n) ⟶ C}
    {i : BasedSpace.adjoinPoint (cubeObject n) ⟶ D} {j : C ⟶ D}
    (h : IsPushout (BasedSpace.adjoinPointMap (cubeBoundaryInclusion n)) a i j)
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (hf : stableEquivalences f)
    (hC : stableEquivalences (spaceSmashMap (𝟙 C) f)) :
    stableEquivalences (spaceSmashMap (𝟙 D) f) := by
  letI : T2Space (cubeBoundaryObject.{0} n) :=
    inferInstanceAs (T2Space (ULift.{0} (↥(_root_.Cube.boundary (Fin n)))))
  letI : UCompactlyGeneratedSpace.{0} (BasedSpace.adjoinPoint (cubeBoundaryObject n)) :=
    inferInstanceAs (UCompactlyGeneratedSpace.{0} ((cubeBoundaryObject.{0} n) ⊕ PUnit))
  letI : UCompactlyGeneratedSpace.{0} (BasedSpace.adjoinPoint (cubeObject n)) :=
    inferInstanceAs (UCompactlyGeneratedSpace.{0} ((cubeObject.{0} n) ⊕ PUnit))
  exact spaceSmashMap_stableEquivalence_of_parameter_pushout_based h f
    (spaceSmashCubeBoundaryMap_level_hasBasedHomotopyExtension n X)
    (spaceSmashCubeBoundaryMap_level_hasBasedHomotopyExtension n Y)
    (spaceSmashMap_cubeBoundary_stableEquivalence_general n f hf)
    (spaceSmashMap_cube_stableEquivalence n f hf) hC

end KIP126.StableHomotopy.Implementation.Prespectrum
