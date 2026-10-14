module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Unit.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Stability.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy
set_option backward.isDefEq.respectTransparency false

theorem spaceSmashUnit_levelHomotopy_bijective (X : Prespectrum.{0}) (n r : ℕ) :
    Function.Bijective ((spaceSmashUnit X).levelHomotopy n r) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h p =>
      induction y using Quotient.inductionOn with
      | h q =>
        intro h
        apply Quotient.sound
        exact (BasedSpace.smashUnitComparison_homotopicRel_iff
          (X.level n) p.val q.val (Cube.boundary (Fin r))).mp (Quotient.exact h)
  · intro x
    induction x using Quotient.inductionOn with
    | h p =>
      obtain ⟨q,hq⟩ := BasedSpace.genLoop_lift_smashUnitComparison (X.level n) r p
      refine ⟨⟦q⟧,congrArg Quotient.mk'' ?_⟩
      apply GenLoop.ext
      intro t
      exact ContinuousMap.congr_fun hq t

/-- Stable unit equivalence does not require the arbitrary spectrum
levels themselves to carry the compactly generated topology. -/
theorem spaceSmashUnit_stableEquivalence (X : Prespectrum.{0}) :
    stableEquivalences (spaceSmashUnit X) :=
  stableEquivalence_of_levelHomotopy_bijective _ (spaceSmashUnit_levelHomotopy_bijective X)

@[reassoc] theorem spaceSmashUnit_natural {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    spaceSmashMap (𝟙 BasedSpace.zeroSphere) f ≫ spaceSmashUnit Y = spaceSmashUnit X ≫ f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  rw [← BasedSpace.smashUnitComparison_section (X.level n) z]
  change (BasedSpace.smashUnitComparison (Y.level n)).map
    ((spaceSmashMap (𝟙 BasedSpace.zeroSphere) f).level n
      (BasedSpace.smashPoint _ (X.level n) (show BasedSpace.zeroSphere from (1 : Fin 2))
        ((BasedSpace.smashUnitComparison (X.level n)).map z))) = _
  rw [spaceSmashMap_apply]
  change (BasedSpace.smashUnitComparison (Y.level n)).map
    (BasedSpace.smashPoint _ (Y.level n) (show BasedSpace.zeroSphere from (1 : Fin 2))
      (f.level n ((BasedSpace.smashUnitComparison (X.level n)).map z))) = _
  rw [BasedSpace.smashUnitComparison_apply]
  change _ = f.level n ((BasedSpace.smashUnitComparison (X.level n)).map
    (BasedSpace.smashPoint _ (X.level n) (show BasedSpace.zeroSphere from (1 : Fin 2))
      ((BasedSpace.smashUnitComparison (X.level n)).map z)))
  rw [BasedSpace.smashUnitComparison_apply]

end KIP126.StableHomotopy.Implementation.Prespectrum
