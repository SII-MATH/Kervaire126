module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

@[simp] theorem spaceSmashIntervalComparison_apply (X : Prespectrum.{0})
    (n : ℕ) (t : I) (x : X.level n) :
    (spaceSmashIntervalComparison X).level n
      (BasedSpace.smashPoint (BasedSpace.adjoinPoint (TopCat.of I)) (X.level n) (.inl t) x) =
      mappingCylinderMk (𝟙 X) n (.inl (x, t)) := rfl

@[simp] theorem spaceSmashIntervalAt_apply (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] (t : I) (n : ℕ) (x : X.level n) :
    (spaceSmashIntervalAt X t).level n x =
      BasedSpace.smashPoint (BasedSpace.adjoinPoint (TopCat.of I)) (X.level n) (.inl t) x := rfl

@[simp] theorem spaceSmashIntervalInverse_inl (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] (n : ℕ) (x : X.level n) (t : I) :
    (spaceSmashIntervalInverse X).level n (mappingCylinderMk (𝟙 X) n (.inl (x, t))) =
      BasedSpace.smashPoint (BasedSpace.adjoinPoint (TopCat.of I)) (X.level n) (.inl t) x := rfl

@[simp] theorem spaceSmashIntervalInverse_inr (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] (n : ℕ) (x : X.level n) :
    (spaceSmashIntervalInverse X).level n (mappingCylinderMk (𝟙 X) n (.inr x)) =
      BasedSpace.smashPoint (BasedSpace.adjoinPoint (TopCat.of I)) (X.level n) (.inl 1) x := rfl

/-- The two actual comparisons are inverse on the original smash
quotient, including its collapsed disjoint basepoint. -/
theorem spaceSmashIntervalComparison_inverse (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashIntervalComparison X ≫ spaceSmashIntervalInverse X = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a, x⟩
  cases a with
  | inl t => rfl
  | inr t =>
    cases t
    change (spaceSmashIntervalInverse X).level n
      ((mappingCylinder (𝟙 X)).level n).point =
      BasedSpace.smashPoint (BasedSpace.adjoinPoint (TopCat.of I)) (X.level n)
        (BasedSpace.adjoinPoint (TopCat.of I)).point x
    rw [BasedSpace.smashPoint_base_left]
    exact (spaceSmashIntervalInverse X).point n

/-- The comparisons are also inverse on both original mapping-cylinder
summands, using its actual top-end gluing equation. -/
theorem spaceSmashIntervalInverse_comparison (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashIntervalInverse X ≫ spaceSmashIntervalComparison X = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  obtain ⟨q, rfl⟩ := mappingCylinderMk_surjective (𝟙 X) n z
  rcases q with ⟨x, t⟩ | x
  · rfl
  · exact mappingCylinderMk_top (𝟙 X) n x

/-- The full retained interval agrees with the original mapping-cylinder
path under the strict comparison. -/
@[reassoc] theorem spaceSmashIntervalPath_comparison (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashIntervalPath X ≫ pathMap (spaceSmashIntervalComparison X) =
      mappingCylinderPath (𝟙 X) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro t
  rfl

@[reassoc] theorem spaceSmashIntervalAt_zero_comparison (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashIntervalAt X 0 ≫ spaceSmashIntervalComparison X =
      mappingCylinderInclusion (𝟙 X) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

@[reassoc] theorem spaceSmashIntervalAt_one_comparison (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashIntervalAt X 1 ≫ spaceSmashIntervalComparison X =
      mappingCylinderSection (𝟙 X) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  exact mappingCylinderMk_top (𝟙 X) n

@[reassoc] theorem mappingCylinderInclusion_spaceSmashIntervalInverse (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    mappingCylinderInclusion (𝟙 X) ≫ spaceSmashIntervalInverse X = spaceSmashIntervalAt X 0 := rfl

@[reassoc] theorem mappingCylinderSection_spaceSmashIntervalInverse (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    mappingCylinderSection (𝟙 X) ≫ spaceSmashIntervalInverse X = spaceSmashIntervalAt X 1 := rfl

/-- The actual interval/cylinder comparison is natural in strict maps
of spectra, with the original mapping-cylinder functor on the right. -/
@[reassoc] theorem spaceSmashIntervalComparison_natural {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (TopCat.of I))) f ≫ spaceSmashIntervalComparison Y =
      spaceSmashIntervalComparison X ≫
        mappingCylinderMap (𝟙 X) (𝟙 Y) f f (by simp) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a, x⟩
  change (spaceSmashIntervalComparison Y).level n
    ((spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (TopCat.of I))) f).level n
      (BasedSpace.smashPoint _ (X.level n) a x)) = _
  rw [spaceSmashMap_apply]
  cases a with
  | inl t => rfl
  | inr t => exact (mappingCylinderMap (𝟙 X) (𝟙 Y) f f (by simp)).point n |>.symm

/-- Every specified interval coordinate is natural in the spectrum. -/
@[reassoc] theorem spaceSmashIntervalAt_natural {X Y : Prespectrum.{0}}
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)]
    [∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)] (f : X ⟶ Y) (t : I) :
    spaceSmashIntervalAt X t ≫ spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (TopCat.of I))) f =
      f ≫ spaceSmashIntervalAt Y t := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact spaceSmashMap_apply (𝟙 (BasedSpace.adjoinPoint (TopCat.of I))) f n (.inl t) x

end KIP126.StableHomotopy.Implementation.Prespectrum
