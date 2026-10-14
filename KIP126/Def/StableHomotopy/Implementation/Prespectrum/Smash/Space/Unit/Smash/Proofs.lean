module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Unit.Smash.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.CompactlyGenerated.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

@[simp] theorem spaceSmashUnitInsertion_map (A : BasedSpace.{0}) (X : Prespectrum.{0}) :
    spaceSmashUnitInsertion A X ≫ spaceSmashMap (𝟙 A) (spaceSmashUnit X) = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,x⟩
  change (BasedSpace.smashMap (𝟙 A) (BasedSpace.smashUnitComparison (X.level n))).map
    (BasedSpace.smashPoint A _ a (BasedSpace.smashPoint BasedSpace.zeroSphere _
      (show BasedSpace.zeroSphere from (1 : Fin 2)) x)) = _
  rw [BasedSpace.smashMap_apply,BasedSpace.smashUnitComparison_apply]
  rfl

@[simp] theorem spaceSmashUnit_map_insertion (A : BasedSpace.{0}) (X : Prespectrum.{0}) :
    spaceSmashMap (𝟙 A) (spaceSmashUnit X) ≫ spaceSmashUnitInsertion A X = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,x⟩
  change (spaceSmashUnitInsertionLevel A (X.level n)).map
    ((BasedSpace.smashMap (𝟙 A) (BasedSpace.smashUnitComparison (X.level n))).map
      (BasedSpace.smashPoint A _ a x)) = _
  rw [BasedSpace.smashMap_apply]
  change BasedSpace.smashPoint A _ a (BasedSpace.smashPoint BasedSpace.zeroSphere _
    (show BasedSpace.zeroSphere from (1 : Fin 2))
    ((BasedSpace.smashUnitComparison (X.level n)).map x)) = _
  rw [BasedSpace.smashUnitComparison_section]
  rfl

/-- The actual zero-sphere unit becomes a strict isomorphism after an
additional smash, for arbitrary original inputs. -/
instance spaceSmashMap_unit_isIso (A : BasedSpace.{0}) (X : Prespectrum.{0}) :
    IsIso (spaceSmashMap (𝟙 A) (spaceSmashUnit X)) :=
  ⟨⟨spaceSmashUnitInsertion A X,spaceSmashUnit_map_insertion A X,
    spaceSmashUnitInsertion_map A X⟩⟩

/-- Stability of a fixed actual smash on compactly generated levels
implies stability on arbitrary original levels, through the explicit unit
comparison and the proved strict isomorphism after smashing it. -/
theorem spaceSmashMap_stableEquivalence_of_compactlyGenerated (A : BasedSpace.{0})
    (hA : ∀ {X Y : Prespectrum.{0}}
      [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)]
      [∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)]
      (f : X ⟶ Y), stableEquivalences f → stableEquivalences (spaceSmashMap (𝟙 A) f))
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (spaceSmashMap (𝟙 A) f) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _
    (hA (spaceSmashMap (𝟙 BasedSpace.zeroSphere) f)
      (spaceSmashMap_zeroSphere_stableEquivalence f hf))
  have e : spaceSmashMap (𝟙 A) (spaceSmashMap (𝟙 BasedSpace.zeroSphere) f) ≫
      spaceSmashMap (𝟙 A) (spaceSmashUnit Y) =
      spaceSmashMap (𝟙 A) (spaceSmashUnit X) ≫ spaceSmashMap (𝟙 A) f := by
    rw [← spaceSmashMap_comp,← spaceSmashMap_comp,spaceSmashUnit_natural]
  have e' := congrArg sourceLocalization.map e
  simp only [Functor.map_comp] at e'
  exact IsIso.of_isIso_fac_left e'.symm

end KIP126.StableHomotopy.Implementation.Prespectrum
