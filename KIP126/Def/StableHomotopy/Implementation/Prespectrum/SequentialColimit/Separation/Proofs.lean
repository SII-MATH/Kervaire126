module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Proofs
public import KIP126.Def.Topology.SequentialColimit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual sequential prespectrum colimit retains T₁ levels when its
actual transitions are levelwise closed embeddings. -/
theorem sequentialColimit_level_t1Space (F : ℕ ⥤ Prespectrum.{u})
    [∀ k n, T1Space ((F.obj k).level n)]
    (hF : ∀ k n, IsClosedEmbedding ((F.map (homOfLE (Nat.le_succ k))).level n)) (n : ℕ) :
    T1Space ((sequentialColimit F).level n) := by
  letI (k : ℕ) : T1Space ((sequentialLevelDiagram F n).obj k) :=
    inferInstanceAs (T1Space ((F.obj k).level n))
  constructor
  intro x
  obtain ⟨k,y,rfl⟩ := sequentialColimitLevelInclusion_jointly_surjective F n x
  have hι := KIP126.Topology.isClosedEmbedding_nat_colimit (sequentialLevelDiagram F n)
    (colimit.cocone _) (colimit.isColimit _) (fun k => hF k n) k
  change IsClosed ({(colimit.ι (sequentialLevelDiagram F n) k) y} :
    Set (↑(colimit (sequentialLevelDiagram F n) : TopCat.{u})))
  have hclosed := hι.isClosedMap {y} isClosed_singleton
  rw [Set.image_singleton] at hclosed
  exact hclosed

end KIP126.StableHomotopy.Implementation.Prespectrum
