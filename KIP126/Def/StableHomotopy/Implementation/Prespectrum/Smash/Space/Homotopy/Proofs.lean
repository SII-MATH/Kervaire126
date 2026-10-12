module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- An actual based homotopy equivalence in the space factor gives a
stable equivalence of the smashed spectra, with the displayed strict inverse. -/
theorem spaceSmashMap_stableEquivalence_of_homotopyEquivalence
    {A B : BasedSpace.{0}} (a : A ⟶ B) (b : B ⟶ A)
    (hab : (b.map.comp a.map).HomotopicRel (ContinuousMap.id A) {A.point})
    (hba : (a.map.comp b.map).HomotopicRel (ContinuousMap.id B) {B.point})
    (X : Prespectrum.{0}) : stableEquivalences (spaceSmashMap a (𝟙 X)) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  refine ⟨sourceLocalization.map (spaceSmashMap b (𝟙 X)),?_,?_⟩
  · have h := source_map_eq_of_pathHomotopic
      ⟨spaceSmashHomotopy (a := a ≫ b) (b := 𝟙 A) hab.some (StrictHomotopy.refl (𝟙 X))⟩
    have hc : spaceSmashMap (a ≫ b) (𝟙 X) =
        spaceSmashMap a (𝟙 X) ≫ spaceSmashMap b (𝟙 X) := by
      simpa only [Category.id_comp] using spaceSmashMap_comp a b (𝟙 X) (𝟙 X)
    change sourceLocalization.map (spaceSmashMap (a ≫ b) (𝟙 X)) =
      sourceLocalization.map (spaceSmashMap (𝟙 A) (𝟙 X)) at h
    rw [hc,Functor.map_comp,spaceSmashMap_id,CategoryTheory.Functor.map_id] at h
    exact h
  · have h := source_map_eq_of_pathHomotopic
      ⟨spaceSmashHomotopy (a := b ≫ a) (b := 𝟙 B) hba.some (StrictHomotopy.refl (𝟙 X))⟩
    have hc : spaceSmashMap (b ≫ a) (𝟙 X) =
        spaceSmashMap b (𝟙 X) ≫ spaceSmashMap a (𝟙 X) := by
      simpa only [Category.id_comp] using spaceSmashMap_comp b a (𝟙 X) (𝟙 X)
    change sourceLocalization.map (spaceSmashMap (b ≫ a) (𝟙 X)) =
      sourceLocalization.map (spaceSmashMap (𝟙 B) (𝟙 X)) at h
    rw [hc,Functor.map_comp,spaceSmashMap_id,CategoryTheory.Functor.map_id] at h
    exact h

end KIP126.StableHomotopy.Implementation.Prespectrum
