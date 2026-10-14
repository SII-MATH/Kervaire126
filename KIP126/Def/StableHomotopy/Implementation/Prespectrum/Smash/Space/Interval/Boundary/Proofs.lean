module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Boundary.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits _root_.Topology
open KIP126.Topology.HomotopyLifting
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

@[simp] theorem spaceSmashIntervalBoundaryComparison_apply (X : Prespectrum.{0})
    (n : ℕ) (e : intervalBoundaryObject) (x : X.level n) :
    (spaceSmashIntervalBoundaryComparison X).level n
      (BasedSpace.smashPoint (BasedSpace.adjoinPoint intervalBoundaryObject) (X.level n) (.inl e) x) =
      if e.val = 0 then (coprod.inl : X ⟶ X ⨿ X).level n x
        else (coprod.inr : X ⟶ X ⨿ X).level n x := by classical rfl

@[simp] theorem spaceSmashIntervalBoundaryAt_apply (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] (e : intervalBoundaryObject)
    (n : ℕ) (x : X.level n) :
    (spaceSmashIntervalBoundaryAt X e).level n x =
      BasedSpace.smashPoint (BasedSpace.adjoinPoint intervalBoundaryObject) (X.level n) (.inl e) x := rfl

@[reassoc] theorem spaceSmashIntervalBoundaryAt_zero_comparison (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashIntervalBoundaryAt X ⟨0,Or.inl rfl⟩ ≫ spaceSmashIntervalBoundaryComparison X =
      coprod.inl := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact (spaceSmashIntervalBoundaryComparison_apply X n ⟨0,Or.inl rfl⟩ x).trans (if_pos rfl)

@[reassoc] theorem spaceSmashIntervalBoundaryAt_one_comparison (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashIntervalBoundaryAt X ⟨1,Or.inr rfl⟩ ≫ spaceSmashIntervalBoundaryComparison X =
      coprod.inr := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact (spaceSmashIntervalBoundaryComparison_apply X n ⟨1,Or.inr rfl⟩ x).trans (if_neg one_ne_zero)

@[reassoc] theorem coprod_inl_spaceSmashIntervalBoundaryInverse (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    coprod.inl ≫ spaceSmashIntervalBoundaryInverse X =
      spaceSmashIntervalBoundaryAt X ⟨0,Or.inl rfl⟩ := coprod.inl_desc _ _

@[reassoc] theorem coprod_inr_spaceSmashIntervalBoundaryInverse (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    coprod.inr ≫ spaceSmashIntervalBoundaryInverse X =
      spaceSmashIntervalBoundaryAt X ⟨1,Or.inr rfl⟩ := coprod.inr_desc _ _

/-- The actual coproduct comparison followed by its inverse is the identity. -/
theorem spaceSmashIntervalBoundaryComparison_inverse (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashIntervalBoundaryComparison X ≫ spaceSmashIntervalBoundaryInverse X = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,x⟩
  cases a with
  | inl e =>
    change (spaceSmashIntervalBoundaryInverse X).level n
      ((spaceSmashIntervalBoundaryComparison X).level n
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint intervalBoundaryObject) (X.level n) (.inl e) x)) = _
    rw [spaceSmashIntervalBoundaryComparison_apply]
    rcases e.property with h | h
    · rw [if_pos h]
      have he : e = (⟨0,Or.inl rfl⟩ : intervalBoundaryObject) := Subtype.ext h
      subst e
      exact DFunLike.congr_fun (congrArg (fun f => f.level n)
        (coprod_inl_spaceSmashIntervalBoundaryInverse X)) x
    · have he : e = (⟨1,Or.inr rfl⟩ : intervalBoundaryObject) := Subtype.ext h
      subst e
      rw [if_neg one_ne_zero]
      exact DFunLike.congr_fun (congrArg (fun f => f.level n)
        (coprod_inr_spaceSmashIntervalBoundaryInverse X)) x
  | inr e =>
    cases e
    change (spaceSmashIntervalBoundaryInverse X).level n ((X ⨿ X).level n).point =
      BasedSpace.smashPoint (BasedSpace.adjoinPoint intervalBoundaryObject) (X.level n)
        (BasedSpace.adjoinPoint intervalBoundaryObject).point x
    rw [BasedSpace.smashPoint_base_left]
    exact (spaceSmashIntervalBoundaryInverse X).point n

/-- The two actual summands are retained by the reverse composite. -/
theorem spaceSmashIntervalBoundaryInverse_comparison (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashIntervalBoundaryInverse X ≫ spaceSmashIntervalBoundaryComparison X = 𝟙 _ := by
  apply coprod.hom_ext
  · rw [← Category.assoc,coprod_inl_spaceSmashIntervalBoundaryInverse,
      spaceSmashIntervalBoundaryAt_zero_comparison,Category.comp_id]
  · rw [← Category.assoc,coprod_inr_spaceSmashIntervalBoundaryInverse,
      spaceSmashIntervalBoundaryAt_one_comparison,Category.comp_id]

/-- Endpoint insertion remains the same actual parameter after its inclusion
into the interval. -/
@[reassoc] theorem spaceSmashIntervalBoundaryAt_map (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] (e : intervalBoundaryObject) :
    spaceSmashIntervalBoundaryAt X e ≫ spaceSmashIntervalBoundaryMap X =
      spaceSmashIntervalAt X e.val := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact spaceSmashMap_apply (BasedSpace.adjoinPointMap intervalBoundaryInclusion) (𝟙 X) n (.inl e) x

/-- Under the two strict comparisons, the whole boundary inclusion is exactly
the two original mapping-cylinder endpoints. -/
@[reassoc] theorem spaceSmashIntervalBoundary_comparison_square (X : Prespectrum.{0})
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)] :
    spaceSmashIntervalBoundaryMap X ≫ (spaceSmashIntervalIso X).hom =
      spaceSmashIntervalBoundaryComparison X ≫ cylinderEndpoints X := by
  have h : spaceSmashIntervalBoundaryInverse X ≫ spaceSmashIntervalBoundaryMap X ≫
      (spaceSmashIntervalIso X).hom = cylinderEndpoints X := by
    apply coprod.hom_ext
    · rw [← Category.assoc,coprod_inl_spaceSmashIntervalBoundaryInverse,
        spaceSmashIntervalBoundaryAt_map_assoc]
      exact (spaceSmashIntervalAt_zero_comparison X).trans (coprod.inl_desc _ _).symm
    · rw [← Category.assoc,coprod_inr_spaceSmashIntervalBoundaryInverse,
        spaceSmashIntervalBoundaryAt_map_assoc]
      exact (spaceSmashIntervalAt_one_comparison X).trans (coprod.inr_desc _ _).symm
  rw [← h,← Category.assoc,← Category.assoc,spaceSmashIntervalBoundaryComparison_inverse,
    Category.id_comp]

/-- The actual endpoint/coproduct identification is natural in strict maps,
even before compact-generation hypotheses are needed for its inverse. -/
@[reassoc] theorem spaceSmashIntervalBoundaryComparison_natural {X Y : Prespectrum.{0}}
    (f : X ⟶ Y) :
    spaceSmashMap (𝟙 (BasedSpace.adjoinPoint intervalBoundaryObject)) f ≫
        spaceSmashIntervalBoundaryComparison Y =
      spaceSmashIntervalBoundaryComparison X ≫ coprod.map f f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,x⟩
  change (spaceSmashIntervalBoundaryComparison Y).level n
      ((spaceSmashMap (𝟙 (BasedSpace.adjoinPoint intervalBoundaryObject)) f).level n
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint intervalBoundaryObject) (X.level n) a x)) = _
  rw [spaceSmashMap_apply]
  cases a with
  | inl e =>
    change (spaceSmashIntervalBoundaryComparison Y).level n
      (BasedSpace.smashPoint (BasedSpace.adjoinPoint intervalBoundaryObject) (Y.level n) (.inl e) (f.level n x)) =
      (coprod.map f f).level n ((spaceSmashIntervalBoundaryComparison X).level n
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint intervalBoundaryObject) (X.level n) (.inl e) x))
    rw [spaceSmashIntervalBoundaryComparison_apply,spaceSmashIntervalBoundaryComparison_apply]
    split_ifs
    · exact (DFunLike.congr_fun (congrArg (fun g => g.level n) (coprod.inl_map f f)) x).symm
    · exact (DFunLike.congr_fun (congrArg (fun g => g.level n) (coprod.inr_map f f)) x).symm
  | inr e => exact ((coprod.map f f).point n).symm

/-- Each actual endpoint insertion is natural in the spectrum. -/
@[reassoc] theorem spaceSmashIntervalBoundaryAt_natural {X Y : Prespectrum.{0}}
    [∀ n, UCompactlyGeneratedSpace.{0} (X.level n)]
    [∀ n, UCompactlyGeneratedSpace.{0} (Y.level n)] (f : X ⟶ Y)
    (e : intervalBoundaryObject) :
    spaceSmashIntervalBoundaryAt X e ≫
        spaceSmashMap (𝟙 (BasedSpace.adjoinPoint intervalBoundaryObject)) f =
      f ≫ spaceSmashIntervalBoundaryAt Y e := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact spaceSmashMap_apply (𝟙 (BasedSpace.adjoinPoint intervalBoundaryObject)) f n (.inl e) x

end KIP126.StableHomotopy.Implementation.Prespectrum
