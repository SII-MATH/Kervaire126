module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Cells.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Comparison.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.ClosedEmbedding.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra _root_.Topology
open KIP126.Topology.HomotopyLifting
set_option backward.isDefEq.respectTransparency false

variable (F : ℕ ⥤ BasedSpace.{0}) [∀ k, UCompactlyGeneratedSpace.{0} (F.obj k)]
  (hF : ∀ k, Nonempty (AttachCells.{0}
    (fun n => BasedSpace.adjoinPointMap (cubeBoundaryInclusion.{0} n))
    (F.map (homOfLE (Nat.le_succ k)))))

include hF

/-- Actual sequential cubical parameter attachments preserve smash
cofibrancy at every finite stage. -/
theorem IsCubicallyCofibrant.spaceSmash_cellSequence_stage
    {X : Prespectrum.{0}} (hX : IsCubicallyCofibrant X)
    (h₀ : IsCubicallyCofibrant (spaceSmash (F.obj 0) X)) (k : ℕ) :
    IsCubicallyCofibrant (spaceSmash (F.obj k) X) := by
  induction k with
  | zero => exact h₀
  | succ k hk =>
      exact IsCubicallyCofibrant.spaceSmash_cubeAttachCells (hF k).some hX hk

/-- Smashing the specified actual colimit of a cubical parameter-cell
sequence gives a cofibrant spectrum whenever the initial smash is cofibrant. -/
theorem IsCubicallyCofibrant.spaceSmash_cellSequence_colimit
    (c : Cocone F) (hc : IsColimit c)
    {X : Prespectrum.{0}} (hX : IsCubicallyCofibrant X)
    (h₀ : IsCubicallyCofibrant (spaceSmash (F.obj 0) X)) :
    IsCubicallyCofibrant (spaceSmash c.pt X) := by
  intro E B p hp
  exact sequentialColimit_isCubicallyCofibrant (F ⋙ spaceSmashParameterFunctor X)
    ((spaceSmashParameterFunctor X).mapCocone c)
    (spaceSmashParameter_mapCocone_isColimit F c hc X)
    (fun k => spaceSmashMap_cubeAttachCells_isCubicalCofibration (hF k).some hX) h₀ p hp

/-- Stable smash invariance extends through an actual sequential
colimit of arbitrary simultaneous cubical parameter attachments. -/
theorem spaceSmashMap_cellSequence_stableEquivalence
    (c : Cocone F) (hc : IsColimit c)
    {X Y : Prespectrum.{0}} (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y)
    (f : X ⟶ Y) (hf : stableEquivalences f)
    (h₀X : IsCubicallyCofibrant (spaceSmash (F.obj 0) X))
    (h₀Y : IsCubicallyCofibrant (spaceSmash (F.obj 0) Y))
    (h₀ : stableEquivalences (spaceSmashMap (𝟙 (F.obj 0)) f)) :
    stableEquivalences (spaceSmashMap (𝟙 c.pt) f) := by
  have hFX (k : ℕ) : IsCubicallyCofibrant (spaceSmash (F.obj k) X) :=
    IsCubicallyCofibrant.spaceSmash_cellSequence_stage F hF hX h₀X k
  have hFY (k : ℕ) : IsCubicallyCofibrant (spaceSmash (F.obj k) Y) :=
    IsCubicallyCofibrant.spaceSmash_cellSequence_stage F hF hY h₀Y k
  letI (k n : ℕ) : T1Space (((F ⋙ spaceSmashParameterFunctor X).obj k).level n) :=
    IsCubicallyCofibrant.level_t1Space (hFX k) n
  letI (k n : ℕ) : T1Space (((F ⋙ spaceSmashParameterFunctor Y).obj k).level n) :=
    IsCubicallyCofibrant.level_t1Space (hFY k) n
  have hstage (k : ℕ) : stableEquivalences (spaceSmashMap (𝟙 (F.obj k)) f) := by
    induction k with
    | zero => exact h₀
    | succ k hk =>
        exact spaceSmashMap_cubeAttachCells_stableEquivalence
          (hF k).some hX hY f hf (hFX k) (hFY k) hk
  let α : F ⋙ spaceSmashParameterFunctor X ⟶ F ⋙ spaceSmashParameterFunctor Y := {
    app k := spaceSmashMap (𝟙 (F.obj k)) f
    naturality _ _ a := spaceSmashMap_parameter_natural (F.map a) f }
  exact stableEquivalence_of_sequentialColimit_map
    ((spaceSmashParameterFunctor X).mapCocone c)
    ((spaceSmashParameterFunctor Y).mapCocone c)
    (spaceSmashParameter_mapCocone_isColimit F c hc X)
    (spaceSmashParameter_mapCocone_isColimit F c hc Y)
    (fun k n => IsCubicalCofibration.level_isClosedEmbedding
      (spaceSmashMap_cubeAttachCells_isCubicalCofibration (hF k).some hX) (hFX k) n)
    (fun k n => IsCubicalCofibration.level_isClosedEmbedding
      (spaceSmashMap_cubeAttachCells_isCubicalCofibration (hF k).some hY) (hFY k) n)
    α (spaceSmashMap (𝟙 c.pt) f)
    (fun k => spaceSmashMap_parameter_natural (c.ι.app k) f) hstage

end KIP126.StableHomotopy.Implementation.Prespectrum
