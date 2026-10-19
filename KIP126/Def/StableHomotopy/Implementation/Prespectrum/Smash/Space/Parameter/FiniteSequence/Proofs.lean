module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Cells.Finite.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Instances

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open KIP126.Topology.HomotopyLifting
set_option backward.isDefEq.respectTransparency false

/-- Smashing any original spectrum with an actual one-point parameter
gives the strict zero object. -/
theorem spaceSmash_isZero_of_subsingleton
    (A : BasedSpace.{0}) [Subsingleton A] (X : Prespectrum.{0}) :
    IsZero (spaceSmash A X) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,x⟩
  change BasedSpace.smashPoint A (X.level n) a x = _
  rw [show a = A.point from Subsingleton.elim _ _]
  exact BasedSpace.smashPoint_base_left _ _ _

/-- Any finite initial segment of actual finite-family cubical parameter
attachments retains stable smash invariance for arbitrary original spectra. -/
theorem spaceSmashMap_finiteCellSequence_stableEquivalence
    (F : ℕ ⥤ BasedSpace.{0}) [∀ k, UCompactlyGeneratedSpace.{0} (F.obj k)]
    (c : ∀ k, AttachCells.{0}
      (fun n => BasedSpace.adjoinPointMap (cubeBoundaryInclusion.{0} n))
      (F.map (homOfLE (Nat.le_succ k))))
    [∀ k, Finite (c k).ι] {X Y : Prespectrum.{0}}
    (f : X ⟶ Y) (hf : stableEquivalences f)
    (h₀ : stableEquivalences (spaceSmashMap (𝟙 (F.obj 0)) f)) (k : ℕ) :
    stableEquivalences (spaceSmashMap (𝟙 (F.obj k)) f) := by
  induction k with
  | zero => exact h₀
  | succ k hk => exact spaceSmashMap_finiteCubeAttachCells_stableEquivalence (c k) f hf hk

/-- A finite cubical parameter built from the actual one-point parameter
preserves every stable equivalence of the original spectra. The statement
retains its actual finite cell presentation. -/
theorem spaceSmashMap_finiteCellSequence_from_point_stableEquivalence
    (F : ℕ ⥤ BasedSpace.{0}) [∀ k, UCompactlyGeneratedSpace.{0} (F.obj k)]
    [Subsingleton (F.obj 0)]
    (c : ∀ k, AttachCells.{0}
      (fun n => BasedSpace.adjoinPointMap (cubeBoundaryInclusion.{0} n))
      (F.map (homOfLE (Nat.le_succ k))))
    [∀ k, Finite (c k).ι] {X Y : Prespectrum.{0}}
    (f : X ⟶ Y) (hf : stableEquivalences f) (k : ℕ) :
    stableEquivalences (spaceSmashMap (𝟙 (F.obj k)) f) := by
  apply spaceSmashMap_finiteCellSequence_stableEquivalence F c f hf
  let a := spaceSmashMap (𝟙 (F.obj 0)) f
  letI : IsIso a := (spaceSmash_isZero_of_subsingleton (F.obj 0) X).isIso
    (spaceSmash_isZero_of_subsingleton (F.obj 0) Y) a
  exact (stableEquivalence_iff_source_isIso a).mpr inferInstance

end KIP126.StableHomotopy.Implementation.Prespectrum
