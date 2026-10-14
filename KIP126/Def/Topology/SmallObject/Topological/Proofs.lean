module

public import KIP126.Def.Topology.SmallObject.Sequence.Proofs
public import KIP126.Def.Topology.Pushout.Separation.Proofs
public import KIP126.Def.Topology.SequentialColimit.Compact.Proofs

@[expose] public section

namespace KIP126.Topology.SmallObject

open CategoryTheory CategoryTheory.Limits _root_.Topology

universe u v

variable {I : Type v} [Small.{u} I] {A B : I → TopCat.{u}}
  (f : ∀ i, A i ⟶ B i) {S : TopCat.{u}} (X : Over S)

set_option backward.isDefEq.respectTransparency false

/-- Every step of the actual countable attachment construction is a
closed embedding whenever the specified cell boundaries are. -/
theorem cellularStageMap_isClosedEmbedding
    (hf : ∀ i, IsClosedEmbedding (f i)) (n : ℕ) :
    IsClosedEmbedding (cellularStageMap f X n) :=
  isClosedEmbedding_of_attachCells
    (CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u} f (cellularStage f X n).hom) hf

/-- The actual countable cell stages are T1, starting with a T1 base
and attaching arbitrary normal T1 cells along closed boundaries. -/
theorem cellularStage_t1Space [T1Space X.left]
    [∀ i, NormalSpace (B i)] [∀ i, T1Space (B i)]
    (hf : ∀ i, IsClosedEmbedding (f i)) (n : ℕ) :
    T1Space (cellularStage f X n).left := by
  induction n with
  | zero => exact ‹T1Space X.left›
  | succ n ih =>
    letI := ih
    exact t1Space_of_attachCells
      (CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u} f (cellularStage f X n).hom) hf

/-- All actual stage maps into the genuine countable attachment object
are closed embeddings. -/
theorem cellularStageInclusion_isClosedEmbedding
    (hf : ∀ i, IsClosedEmbedding (f i)) (n : ℕ) :
    IsClosedEmbedding (colimit.ι (cellularSequence f X) n) :=
  isClosedEmbedding_nat_colimit _ _ (colimit.isColimit _) (fun n => by
    rw [cellularSequence,Functor.ofSequence_map_homOfLE_succ]
    exact cellularStageMap_isClosedEmbedding f X hf n) n

/-- Compact domains really factor through a finite stage of the
constructed attachment sequence; no smallness premise is supplied. -/
theorem cellularReplacement_compact_factor
    [T1Space X.left] [∀ i, NormalSpace (B i)] [∀ i, T1Space (B i)]
    (hf : ∀ i, IsClosedEmbedding (f i))
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (g : C(K,↥(cellularReplacement (C := TopCat.{u}) f X))) :
    ∃ (n : ℕ) (g' : C(K,(cellularStage f X n).left)),
      ∀ x, colimit.ι (cellularSequence f X) n (g' x) = g x := by
  letI (n : ℕ) : T1Space ((cellularSequence f X).obj n) :=
    cellularStage_t1Space f X hf n
  exact continuousMap_factor_nat_colimit (cellularSequence f X) _ (colimit.isColimit _)
    (fun n => by
      rw [cellularSequence,Functor.ofSequence_map_homOfLE_succ]
      exact cellularStageMap_isClosedEmbedding f X hf n) g

/-- The comparison of the actual countable construction has the right
lifting property against every specified compact cell boundary. -/
theorem cellularComparison_hasLiftingProperty
    [T1Space X.left] [∀ i, CompactSpace (A i)]
    [∀ i, NormalSpace (B i)] [∀ i, T1Space (B i)]
    (hf : ∀ i, IsClosedEmbedding (f i)) (i : I) :
    HasLiftingProperty (f i) (cellularComparison f X) := by
  constructor
  intro t b sq
  obtain ⟨n,g,hg⟩ := cellularReplacement_compact_factor f X hf t.hom
  obtain ⟨l,hl,hπ⟩ := cellularComparison_extension f X i t b sq.w n
    (TopCat.ofHom g) (by ext x; exact hg x)
  exact CommSq.HasLift.mk' { l := l, fac_left := hl, fac_right := hπ }

end KIP126.Topology.SmallObject
