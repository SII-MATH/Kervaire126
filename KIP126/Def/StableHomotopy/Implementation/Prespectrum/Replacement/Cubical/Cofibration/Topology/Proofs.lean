module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.ClosedEmbedding.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Topology.SmallObject

universe u

set_option backward.isDefEq.respectTransparency false

/-- Cubical cofibrations preserve levelwise T1 separation from their
actual source to their actual target through the relative cellular retract. -/
theorem IsCubicalCofibration.codomain_level_t1Space
    {A B : Prespectrum.{u}} {i : A ⟶ B} (hi : IsCubicalCofibration i)
    [∀ n, T1Space (A.level n)] (n : ℕ) : T1Space (B.level n) := by
  obtain ⟨s, hs, hsπ⟩ := hi.relativeCellular_hasSection
  let q := cellularComparison cubicalCellBoundary (Over.mk i)
  letI (n : ℕ) : T1Space ((Over.mk i).left.level n) := inferInstanceAs (T1Space (A.level n))
  letI := cubicalCellularReplacement_level_t1Space (Over.mk i) n
  have hsq : Function.LeftInverse (q.level n) (s.level n) := fun b =>
    congrArg (fun k : B ⟶ B => k.level n b) hsπ
  exact t1Space_of_injective_of_continuous hsq.injective (s.level n).continuous

/-- Cubical cofibrations preserve original compactly generated levels
from a T1, compactly generated source. The target is the proved continuous
retract of the actual relative attachment colimit. -/
theorem IsCubicalCofibration.codomain_level_uCompactlyGeneratedSpace
    {A B : Prespectrum.{u}} {i : A ⟶ B} (hi : IsCubicalCofibration i)
    [∀ n, T1Space (A.level n)] [∀ n, UCompactlyGeneratedSpace.{u} (A.level n)]
    (n : ℕ) : UCompactlyGeneratedSpace.{u} (B.level n) := by
  obtain ⟨s, hs, hsπ⟩ := hi.relativeCellular_hasSection
  let q := cellularComparison cubicalCellBoundary (Over.mk i)
  letI (n : ℕ) : UCompactlyGeneratedSpace.{u} ((Over.mk i).left.level n) :=
    inferInstanceAs (UCompactlyGeneratedSpace.{u} (A.level n))
  letI := cubicalCellularReplacement_level_uCompactlyGeneratedSpace (Over.mk i) n
  have hsq (b : B.level n) : q.level n (s.level n b) = b :=
    congrArg (fun k : B ⟶ B => k.level n b) hsπ
  apply uCompactlyGeneratedSpace_of_continuous_maps
  intro Y _ f hf
  have hc : Continuous (f ∘ q.level n) := by
    apply continuous_from_uCompactlyGeneratedSpace
    intro S g
    exact hf S ((q.level n).comp g)
  have ht := hc.comp (s.level n).continuous
  simpa only [Function.comp_def, hsq] using ht

end KIP126.StableHomotopy.Implementation.Prespectrum
