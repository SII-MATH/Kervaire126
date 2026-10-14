module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Stability.Proofs
public import KIP126.Def.Topology.SequentialColimit.Compact.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits _root_.Topology
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

variable (F : ℕ ⥤ Prespectrum.{u}) [∀ k n, T1Space ((F.obj k).level n)]
    (hF : ∀ k n, IsClosedEmbedding ((F.map (homOfLE (Nat.le_succ k))).level n))

include hF

/-- Every actual level homotopy class of the closed sequential colimit comes
from a finite stage, with the given prespectrum basepoint. -/
theorem sequentialColimit_levelHomotopy_jointly_surjective (n r : ℕ)
    (x : _root_.HomotopyGroup (Fin r) ((sequentialColimit F).level n)
      ((sequentialColimit F).level n).point) :
    ∃ (k : ℕ) (y : _root_.HomotopyGroup (Fin r) ((F.obj k).level n) ((F.obj k).level n).point),
      (sequentialColimitInclusion F k).levelHomotopy n r y = x := by
  letI (k : ℕ) : T1Space ((sequentialLevelDiagram F n).obj k) :=
    inferInstanceAs (T1Space ((F.obj k).level n))
  induction x using Quotient.inductionOn with
  | h p =>
      obtain ⟨k, q, hq⟩ := KIP126.Topology.continuousMap_factor_nat_colimit
        (sequentialLevelDiagram F n) (colimit.cocone _) (colimit.isColimit _)
        (fun k => hF k n) p.val
      have hι := (KIP126.Topology.isClosedEmbedding_nat_colimit
        (sequentialLevelDiagram F n) (colimit.cocone _) (colimit.isColimit _)
        (fun k => hF k n) k).injective
      have hb (t) (ht : t ∈ Cube.boundary (Fin r)) : q t = ((F.obj k).level n).point := by
        apply hι
        exact (hq t).trans ((p.property t ht).trans (sequentialColimitLevelInclusion_point F n k).symm)
      refine ⟨k, ⟦⟨q, hb⟩⟧, ?_⟩
      apply congrArg Quotient.mk''
      exact GenLoop.ext _ _ hq

/-- Equality of actual level homotopy classes in the colimit is detected
after one finite transition of the actual prespectrum diagram. -/
theorem sequentialColimit_levelHomotopy_eq_eventually (k n r : ℕ)
    (x y : _root_.HomotopyGroup (Fin r) ((F.obj k).level n) ((F.obj k).level n).point)
    (h : (sequentialColimitInclusion F k).levelHomotopy n r x =
      (sequentialColimitInclusion F k).levelHomotopy n r y) :
    ∃ (l : ℕ) (hkl : k ≤ l),
      (F.map (homOfLE hkl)).levelHomotopy n r x = (F.map (homOfLE hkl)).levelHomotopy n r y := by
  letI (k : ℕ) : T1Space ((sequentialLevelDiagram F n).obj k) :=
    inferInstanceAs (T1Space ((F.obj k).level n))
  induction x using Quotient.inductionOn with
  | h p =>
      induction y using Quotient.inductionOn with
      | h q =>
          obtain ⟨l, hkl, hpq⟩ :=
            (KIP126.Topology.homotopicRel_nat_colimit_iff
              (sequentialLevelDiagram F n) (colimit.cocone _) (colimit.isColimit _)
              (fun k => hF k n) k p.val q.val (Cube.boundary (Fin r))).mp (Quotient.exact h)
          exact ⟨l, hkl, Quotient.sound hpq⟩

/-- Every actual stable class of the closed sequential colimit comes from
one actual prespectrum stage. -/
theorem sequentialColimit_stableHomotopy_jointly_surjective (d : ℤ)
    (x : StableHomotopy (sequentialColimit F) d) :
    ∃ (k : ℕ) (y : StableHomotopy (F.obj k) d),
      stableHomotopyMap (sequentialColimitInclusion F k) d y = x := by
  obtain ⟨i, p, _, hx, _⟩ := exists_stableLevelClass_pair (sequentialColimit F) d x x
  obtain ⟨k, q, hq⟩ := sequentialColimit_levelHomotopy_jointly_surjective F hF
    (stableGroupStage d i) (stableGroupDimension d i) p
  refine ⟨k, stableLevelClass (F.obj k) d i q, ?_⟩
  rw [stableLevelClass_natural, hq]
  exact hx.symm

/-- Equality of actual stable classes in the closed sequential colimit is
detected at a finite diagram stage, after a finite cubical stabilization. -/
theorem sequentialColimit_stableHomotopy_eq_eventually (k : ℕ) (d : ℤ)
    (x y : StableHomotopy (F.obj k) d)
    (h : stableHomotopyMap (sequentialColimitInclusion F k) d x =
      stableHomotopyMap (sequentialColimitInclusion F k) d y) :
    ∃ (l : ℕ) (hkl : k ≤ l),
      stableHomotopyMap (F.map (homOfLE hkl)) d x = stableHomotopyMap (F.map (homOfLE hkl)) d y := by
  obtain ⟨i, p, q, rfl, rfl⟩ := exists_stableLevelClass_pair (F.obj k) d x y
  have hc := congrArg (stableGroupCode (sequentialColimit F) d) h
  simp only [stableLevelClass_natural, stableGroupCode_levelClass] at hc
  obtain ⟨j, hp, hq, hpq⟩ := Quotient.exact hc
  rw [← (sequentialColimitInclusion F k).stableLevelTransition_natural,
    ← (sequentialColimitInclusion F k).stableLevelTransition_natural] at hpq
  obtain ⟨l, hkl, he⟩ := sequentialColimit_levelHomotopy_eq_eventually F hF k
    (stableGroupStage d j) (stableGroupDimension d j) _ _ hpq
  refine ⟨l, hkl, ?_⟩
  apply (stableHomotopyGroupEquiv (F.obj l) d).injective
  change stableGroupCode (F.obj l) d _ = stableGroupCode (F.obj l) d _
  rw [stableLevelClass_natural, stableLevelClass_natural,
    stableGroupCode_levelClass, stableGroupCode_levelClass]
  apply Quotient.sound
  refine ⟨j, hp, hq, ?_⟩
  rw [← (F.map (homOfLE hkl)).stableLevelTransition_natural,
    ← (F.map (homOfLE hkl)).stableLevelTransition_natural]
  exact he

/-- Stable homotopy of the actual sequential colimit is the actual colimit
of stable homotopy, for diagrams of levelwise closed embeddings of T1 spaces. -/
noncomputable def sequentialStableHomotopyCocone_isColimit (d : ℤ) :
    IsColimit (sequentialStableHomotopyCocone F d) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨k, y, hy⟩ := sequentialColimit_stableHomotopy_jointly_surjective F hF d x
    exact ⟨k, y, hy.symm⟩
  · intro k x y h
    obtain ⟨l, hkl, he⟩ := sequentialColimit_stableHomotopy_eq_eventually F hF k d x y h
    exact ⟨l, homOfLE hkl, he⟩

/-- A closed sequential diagram whose transitions from the initial stage
are stable equivalences has an actual stable-equivalence inclusion into
the constructed colimit. -/
theorem sequentialColimitInclusion_zero_stableEquivalence
    (hW : ∀ k, stableEquivalences (F.map (homOfLE (Nat.zero_le k)))) :
    stableEquivalences (sequentialColimitInclusion F 0) := by
  intro d
  constructor
  · intro x y h
    obtain ⟨k, h0k, hk⟩ := sequentialColimit_stableHomotopy_eq_eventually F hF 0 d x y h
    exact (hW k d).injective hk
  · intro x
    obtain ⟨k, y, hy⟩ := sequentialColimit_stableHomotopy_jointly_surjective F hF d x
    obtain ⟨z, hz⟩ := (hW k d).surjective y
    refine ⟨z, ?_⟩
    have hn := ConcreteCategory.congr_hom
      ((sequentialStableHomotopyCocone F d).w (homOfLE (Nat.zero_le k))) z
    change stableHomotopyMap (sequentialColimitInclusion F k) d
      (stableHomotopyMap (F.map (homOfLE (Nat.zero_le k))) d z) =
        stableHomotopyMap (sequentialColimitInclusion F 0) d z at hn
    rw [hz] at hn
    exact hn.symm.trans hy

end KIP126.StableHomotopy.Implementation.Prespectrum
