module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Cone.Level.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

@[simp] theorem spaceSmashConeComparisonLevel_inl (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ) (a : A) (y : Y.level n) :
    (spaceSmashConeComparisonLevel A f n).map
      (Quot.mk _ (.inl (BasedSpace.smashPoint A (Y.level n) a y))) =
      BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inl y)) :=
  (spaceSmashConeComparison_exists A f n).exists.choose_spec.1 a y

@[simp] theorem spaceSmashConeComparisonLevel_inr (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ) (a : A) (x : X.level n) (t : I) :
    (spaceSmashConeComparisonLevel A f n).map
      (Quot.mk _ (.inr (BasedSpace.smashPoint A (X.level n) a x,t))) =
      BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inr (x,t))) :=
  (spaceSmashConeComparison_exists A f n).exists.choose_spec.2 a x t

@[simp] theorem spaceSmashConeInverseLevel_inl (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ)
    [UCompactlyGeneratedSpace.{0} (X.level n)] [UCompactlyGeneratedSpace.{0} (Y.level n)]
    (a : A) (y : Y.level n) :
    (spaceSmashConeInverseLevel A f n).map
      (BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inl y))) =
      Quot.mk _ (.inl (BasedSpace.smashPoint A (Y.level n) a y)) :=
  (spaceSmashConeInverse_exists A f n).exists.choose_spec.1 a y

@[simp] theorem spaceSmashConeInverseLevel_inr (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ)
    [UCompactlyGeneratedSpace.{0} (X.level n)] [UCompactlyGeneratedSpace.{0} (Y.level n)]
    (a : A) (x : X.level n) (t : I) :
    (spaceSmashConeInverseLevel A f n).map
      (BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inr (x,t)))) =
      Quot.mk _ (.inr (BasedSpace.smashPoint A (X.level n) a x,t)) :=
  (spaceSmashConeInverse_exists A f n).exists.choose_spec.2 a x t

@[simp] theorem spaceSmashConeComparisonLevel_inverse (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ)
    [UCompactlyGeneratedSpace.{0} (X.level n)] [UCompactlyGeneratedSpace.{0} (Y.level n)] :
    spaceSmashConeComparisonLevel A f n ≫ spaceSmashConeInverseLevel A f n = 𝟙 _ := by
  apply BasedSpace.Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,t⟩)
  · refine Quot.inductionOn y ?_
    rintro ⟨a,y⟩
    change (spaceSmashConeInverseLevel A f n).map ((spaceSmashConeComparisonLevel A f n).map
      (Quot.mk _ (.inl (BasedSpace.smashPoint A (Y.level n) a y)))) = _
    rw [spaceSmashConeComparisonLevel_inl,spaceSmashConeInverseLevel_inl]
    rfl
  · refine Quot.inductionOn x ?_
    rintro ⟨a,x⟩
    change (spaceSmashConeInverseLevel A f n).map ((spaceSmashConeComparisonLevel A f n).map
      (Quot.mk _ (.inr (BasedSpace.smashPoint A (X.level n) a x,t)))) = _
    rw [spaceSmashConeComparisonLevel_inr,spaceSmashConeInverseLevel_inr]
    rfl

@[simp] theorem spaceSmashConeInverseLevel_comparison (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ)
    [UCompactlyGeneratedSpace.{0} (X.level n)] [UCompactlyGeneratedSpace.{0} (Y.level n)] :
    spaceSmashConeInverseLevel A f n ≫ spaceSmashConeComparisonLevel A f n = 𝟙 _ := by
  apply BasedSpace.Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,z⟩
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,t⟩)
  · change (spaceSmashConeComparisonLevel A f n).map ((spaceSmashConeInverseLevel A f n).map
      (BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inl y)))) = _
    rw [spaceSmashConeInverseLevel_inl,spaceSmashConeComparisonLevel_inl]
    rfl
  · change (spaceSmashConeComparisonLevel A f n).map ((spaceSmashConeInverseLevel A f n).map
      (BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inr (x,t))))) = _
    rw [spaceSmashConeInverseLevel_inr,spaceSmashConeComparisonLevel_inr]
    rfl
end KIP126.StableHomotopy.Implementation.Prespectrum
