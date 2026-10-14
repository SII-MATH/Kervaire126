module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.HomotopyExtension.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Relative.Topology.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits _root_.Topology
open KIP126.Topology.SmallObject

universe u

set_option backward.isDefEq.respectTransparency false

/-- A cubical cofibration whose original source levels are T1 is an
actual closed embedding at every level, by its strict cellular retract. -/
theorem IsCubicalCofibration.level_isClosedEmbedding_of_t1Space
    {A B : Prespectrum.{u}} {i : A ⟶ B} (hi : IsCubicalCofibration i)
    [∀ n, T1Space (A.level n)] (n : ℕ) : IsClosedEmbedding (i.level n) := by
  obtain ⟨s, hs, hsπ⟩ := hi.relativeCellular_hasSection
  let j := colimit.ι (cellularSequence cubicalCellBoundary (Over.mk i)) 0
  let q := cellularComparison cubicalCellBoundary (Over.mk i)
  have hsq : Function.LeftInverse (q.level n) (s.level n) := fun b =>
    congrArg (fun k : B ⟶ B => k.level n b) hsπ
  have hse : IsEmbedding (s.level n) :=
    IsEmbedding.of_leftInverse hsq (q.level n).continuous (s.level n).continuous
  apply IsClosedEmbedding.of_comp hse
  have his : (s.level n) ∘ (i.level n) = j.level n := by
    funext a
    exact congrArg (fun k : A ⟶ cellularReplacement cubicalCellBoundary (Over.mk i) => k.level n a) hs
  rw [his]
  exact cubicalCellularStageInclusion_level_isClosedEmbedding (Over.mk i) 0 n

/-- A cubical cofibration from an actually cofibrant object is closed
embedded in every original level. -/
theorem IsCubicalCofibration.level_isClosedEmbedding
    {A B : Prespectrum.{u}} {i : A ⟶ B} (hi : IsCubicalCofibration i)
    (hA : IsCubicallyCofibrant A) (n : ℕ) : IsClosedEmbedding (i.level n) := by
  letI (n : ℕ) : T1Space (A.level n) := hA.level_t1Space n
  exact hi.level_isClosedEmbedding_of_t1Space n

end KIP126.StableHomotopy.Implementation.Prespectrum
