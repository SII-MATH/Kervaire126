module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Relative.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.HomotopyExtension.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Topology.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits
open KIP126.Topology.SmallObject KIP126.Topology.HomotopyExtension
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual relative cellular comparison has a strict section
retaining the original cofibration's source inclusion. -/
theorem IsCubicalCofibration.relativeCellular_hasSection
    {A B : Prespectrum.{u}} {i : A ⟶ B} (hi : IsCubicalCofibration i)
    [∀ n, T1Space (A.level n)] :
    ∃ s : B ⟶ cellularReplacement cubicalCellBoundary (Over.mk i),
      i ≫ s = colimit.ι (cellularSequence cubicalCellBoundary (Over.mk i)) 0 ∧
      s ≫ cellularComparison cubicalCellBoundary (Over.mk i) = 𝟙 B := by
  letI (n : ℕ) : T1Space ((Over.mk i).left.level n) := inferInstanceAs (T1Space (A.level n))
  letI := hi (cellularComparison cubicalCellBoundary (Over.mk i))
    (cubicalCellularComparison_level_hasCubeBoundaryLifting (Over.mk i))
  let sq : CommSq (colimit.ι (cellularSequence cubicalCellBoundary (Over.mk i)) 0) i
      (cellularComparison cubicalCellBoundary (Over.mk i)) (𝟙 B) := ⟨by
    rw [cellularComparison_stage, Category.comp_id]
    rfl⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- Actual cubical cofibrations with T1 source levels have genuine
levelwise homotopy extension, proved through their actual cellular arrow
retract rather than added as a separate hypothesis. -/
theorem IsCubicalCofibration.level_hasHomotopyExtension_of_t1Space
    {A B : Prespectrum.{u}} {i : A ⟶ B} (hi : IsCubicalCofibration i)
    [∀ n, T1Space (A.level n)] (n : ℕ) :
    HasHomotopyExtension (TopCat.ofHom (i.level n)) := by
  obtain ⟨s, hs, hsπ⟩ := hi.relativeCellular_hasSection
  let j := colimit.ι (cellularSequence cubicalCellBoundary (Over.mk i)) 0
  let q := cellularComparison cubicalCellBoundary (Over.mk i)
  have hjq : j ≫ q = i := cellularComparison_stage cubicalCellBoundary (Over.mk i) 0
  have hsq (b : B.level n) : q.level n (s.level n b) = b :=
    congrArg (fun k : B ⟶ B => k.level n b) hsπ
  have his (a : A.level n) : s.level n (i.level n a) = j.level n a :=
    congrArg (fun k : A ⟶ cellularReplacement cubicalCellBoundary (Over.mk i) => k.level n a) hs
  have hjq' (a : A.level n) : q.level n (j.level n a) = i.level n a :=
    congrArg (fun k : A ⟶ B => k.level n a) hjq
  intro Y f p hp
  obtain ⟨H, hH0, hHj⟩ := cubicalCellularInitialInclusion_level_hasHomotopyExtension (Over.mk i) n
    Y (f.comp (q.level n)) p (by
      intro a
      change p (a, 0) = f (q.level n (j.level n a))
      rw [hjq']
      exact hp a)
  let a : C(B.level n × I,
      (cellularReplacement cubicalCellBoundary (Over.mk i)).level n × I) :=
    ⟨fun z => (s.level n z.1, z.2),
      ((s.level n).continuous.comp continuous_fst).prodMk continuous_snd⟩
  refine ⟨H.comp a, ?_, ?_⟩
  · intro b
    change H (s.level n b, 0) = f b
    rw [hH0]
    exact congrArg f (hsq b)
  · intro x t
    change H (s.level n (i.level n x), t) = p (x, t)
    rw [his]
    exact hHj x t

/-- A cubical cofibration from an actually cofibrant source therefore
has full homotopy extension on every original level. -/
theorem IsCubicalCofibration.level_hasHomotopyExtension
    {A B : Prespectrum.{u}} {i : A ⟶ B} (hi : IsCubicalCofibration i)
    (hA : IsCubicallyCofibrant A) (n : ℕ) :
    HasHomotopyExtension (TopCat.ofHom (i.level n)) := by
  letI (n : ℕ) : T1Space (A.level n) := hA.level_t1Space n
  exact hi.level_hasHomotopyExtension_of_t1Space n

end KIP126.StableHomotopy.Implementation.Prespectrum
