module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Homotopy.Family
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Actual relative homotopies of the space factor and strict homotopies
of the spectrum factor smash to an actual strict homotopy. -/
noncomputable def spaceSmashHomotopy {A B : BasedSpace.{0}} {X Y : Prespectrum.{0}}
    {a b : A ⟶ B} {f g : X ⟶ Y}
    (H : ContinuousMap.HomotopyRel a.map b.map {A.point}) (K : StrictHomotopy f g) :
    StrictHomotopy (spaceSmashMap a f) (spaceSmashMap b g) := by
  let F : C(A × I,B) := ⟨fun p => H (p.2,p.1),H.continuous.comp continuous_swap⟩
  have hF (t : I) : F (A.point,t) = B.point :=
    (H.eq_fst t (Set.mem_singleton _)).trans a.point
  refine { hom := spaceSmashPathMap F hF K.hom, zero := ?_, one := ?_ }
  · apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨c,x⟩
    change (show C(I,(spaceSmash B Y).level n) from
      (spaceSmashPathMap F hF K.hom).level n (BasedSpace.smashPoint A (X.level n) c x)) 0 =
      (spaceSmashMap a f).level n (BasedSpace.smashPoint A (X.level n) c x)
    rw [spaceSmashPathMap_apply,spaceSmashMap_apply]
    change BasedSpace.smashPoint B (Y.level n) (H (0,c)) ((show C(I,Y.level n) from K.hom.level n x) 0) = _
    rw [H.apply_zero]
    exact congrArg (BasedSpace.smashPoint B (Y.level n) (a.map c))
      (congrArg (fun e : X ⟶ Y => e.level n x) K.zero)
  · apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨c,x⟩
    change (show C(I,(spaceSmash B Y).level n) from
      (spaceSmashPathMap F hF K.hom).level n (BasedSpace.smashPoint A (X.level n) c x)) 1 =
      (spaceSmashMap b g).level n (BasedSpace.smashPoint A (X.level n) c x)
    rw [spaceSmashPathMap_apply,spaceSmashMap_apply]
    change BasedSpace.smashPoint B (Y.level n) (H (1,c)) ((show C(I,Y.level n) from K.hom.level n x) 1) = _
    rw [H.apply_one]
    exact congrArg (BasedSpace.smashPoint B (Y.level n) (b.map c))
      (congrArg (fun e : X ⟶ Y => e.level n x) K.one)

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

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

end
