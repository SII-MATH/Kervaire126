module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Tail.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Suspension.HomotopyMap.Naturality.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Stable.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy
universe u
set_option backward.isDefEq.respectTransparency false

theorem suspensionDesuspensionComparison_level_natural {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (n : ℕ) (x : (desuspension X).suspension.level n) :
    f.level n ((suspensionDesuspensionComparison X).level n x) =
      (suspensionDesuspensionComparison Y).level n ((suspensionMap (desuspensionMap f)).level n x) := by
  cases n with
  | zero => exact f.point 0
  | succ n =>
      induction x using Quot.inductionOn with
      | h x => exact f.bond n x.1 (suspensionDesuspensionSign n x.2)

theorem suspensionDesuspensionComparison_stableMap_natural {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (d : ℤ) (x : StableHomotopy (desuspension X).suspension d) :
    stableHomotopyMap f d ((suspensionDesuspensionComparison X).stableMap d x) =
      (suspensionDesuspensionComparison Y).stableMap d
        (stableHomotopyMap (suspensionMap (desuspensionMap f)) d x) := by
  induction x using Quot.inductionOn with
  | h a =>
      apply congrArg (Quot.mk _)
      cases a with
      | mk n r h p =>
          dsimp [Representative.map, HomotopyMap.mapRepresentative]
          congr 1
          apply Subtype.ext
          apply ContinuousMap.ext
          intro t
          exact suspensionDesuspensionComparison_level_natural f n (p.val t)

theorem suspensionMap_desuspensionMap_stableEquivalence {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (suspensionMap (desuspensionMap f)) := by
  intro d
  have hx := suspensionDesuspensionComparison_stableMap_bijective X d
  have hy := suspensionDesuspensionComparison_stableMap_bijective Y d
  constructor
  · intro a b hab
    apply hx.1
    apply (hf d).1
    rw [suspensionDesuspensionComparison_stableMap_natural,
      suspensionDesuspensionComparison_stableMap_natural,hab]
  · intro b
    obtain ⟨a,ha⟩ := (hf d).2 ((suspensionDesuspensionComparison Y).stableMap d b)
    obtain ⟨a,rfl⟩ := hx.2 a
    refine ⟨a,hy.1 ?_⟩
    rw [← suspensionDesuspensionComparison_stableMap_natural]
    exact ha

theorem suspensionMap_stableEquivalence {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (hf : stableEquivalences f) : stableEquivalences (suspensionMap f) :=
  levelTailMap_stableEquivalence (suspensionMap (desuspensionMap f))
    (suspensionMap_desuspensionMap_stableEquivalence f hf)


theorem suspensionDesuspensionComparison_bondHomotopy_natural {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (n : ℕ) (s : I) (x : (desuspension X).suspension.level n) (t : I) :
    f.level (n+1) ((suspensionDesuspensionComparison X).bondHomotopy n (s,(x,t))) =
      (suspensionDesuspensionComparison Y).bondHomotopy n
        (s,((suspensionMap (desuspensionMap f)).level n x,t)) := by
  cases n with
  | zero => exact f.point 1
  | succ n =>
      induction x using Quot.inductionOn with
      | h x =>
          change f.level (n+2) (X.bond (n+1) (X.bond n (x.1,_),_)) =
            Y.bond (n+1) (Y.bond n (f.level n x.1,_),_)
          rw [f.bond, f.bond]
          rfl

theorem suspensionDesuspensionComparison_sourceMap_natural {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) :
    sourceLocalization.map (suspensionMap (desuspensionMap f)) ≫
        (suspensionDesuspensionComparison Y).sourceMap =
      (suspensionDesuspensionComparison X).sourceMap ≫ sourceLocalization.map f :=
  HomotopyMap.sourceMap_natural _ _ _ _
    (suspensionDesuspensionComparison_level_natural f)
    (suspensionDesuspensionComparison_bondHomotopy_natural f)

instance suspensionDesuspensionComparison_sourceMap_isIso (X : Prespectrum.{u}) :
    IsIso (suspensionDesuspensionComparison X).sourceMap := by
  letI := (suspensionDesuspensionComparison X).sourceProjection_isIso
  letI := stableEquivalences.Q_inverts _
    (suspensionDesuspensionComparison_targetProjection_stableEquivalence X)
  dsimp [HomotopyMap.sourceMap]
  infer_instance

end KIP126.StableHomotopy.Implementation.Prespectrum
