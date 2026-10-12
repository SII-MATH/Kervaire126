module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Homotopy.Proofs
public import Mathlib.CategoryTheory.Limits.Types.Filtered

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every stable homotopy class of the actual sequential homotopy colimit
comes from a finite stage of the given sequence. -/
theorem sourceHomotopyColimit_stableHomotopy_exists_rep
    (F : ℕ ⥤ SourceCategory.{u}) (d : ℤ)
    (x : (sourceStableHomotopyAddFunctor d).obj (sourceHomotopyColimit F)) :
    ∃ (n : ℕ) (y : (sourceStableHomotopyAddFunctor d).obj (F.obj n)),
      (sourceStableHomotopyAddFunctor d).map (sourceHomotopyColimitInclusion F n) y = x := by
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat)
      (sourceHomotopyColimit_stableHomotopy_isColimit F d)) x

/-- A class from a specified stage vanishes in the actual homotopy colimit
exactly when it vanishes at some later finite stage. -/
theorem sourceHomotopyColimit_stableHomotopy_eq_zero_iff
    (F : ℕ ⥤ SourceCategory.{u}) (d : ℤ) (n : ℕ)
    (x : (sourceStableHomotopyAddFunctor d).obj (F.obj n)) :
    (sourceStableHomotopyAddFunctor d).map (sourceHomotopyColimitInclusion F n) x = 0 ↔
      ∃ (m : ℕ) (h : n ≤ m),
        (sourceStableHomotopyAddFunctor d).map (F.map (homOfLE h)) x = 0 := by
  let G := sourceStableHomotopyAddFunctor d
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have H : G.map (sourceHomotopyColimitInclusion F n) x =
      G.map (sourceHomotopyColimitInclusion F n) 0 ↔
      ∃ (m : ℕ) (f : n ⟶ m), G.map (F.map f) x = G.map (F.map f) 0 :=
    Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget AddCommGrpCat)
        (sourceHomotopyColimit_stableHomotopy_isColimit F d)) x 0
  simp only [map_zero] at H
  constructor
  · intro hx
    obtain ⟨m, f, hf⟩ := H.mp hx
    refine ⟨m, leOfHom f, ?_⟩
    have he : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
    rw [he]
    exact hf
  · rintro ⟨m, hm, hx⟩
    exact H.mpr ⟨m, homOfLE hm, hx⟩

/-- Eventual vanishing in a fixed degree implies vanishing of that degree
in the actual homotopy colimit. No bound uniform in the degree is needed. -/
theorem sourceHomotopyColimit_stableHomotopy_subsingleton_of_eventually
    (F : ℕ ⥤ SourceCategory.{u}) (d : ℤ) (N : ℕ)
    (hN : ∀ n, N ≤ n → Subsingleton ((sourceStableHomotopyAddFunctor d).obj (F.obj n))) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceHomotopyColimit F)) := by
  have hz (x : (sourceStableHomotopyAddFunctor d).obj (sourceHomotopyColimit F)) : x = 0 := by
    obtain ⟨n, y, rfl⟩ := sourceHomotopyColimit_stableHomotopy_exists_rep F d x
    apply (sourceHomotopyColimit_stableHomotopy_eq_zero_iff F d n y).mpr
    letI := hN (max n N) (Nat.le_max_right _ _)
    exact ⟨max n N, Nat.le_max_left _ _, Subsingleton.elim _ _⟩
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Uniformly connective stages have a connective actual homotopy colimit. -/
theorem sourceHomotopyColimit_connective (F : ℕ ⥤ SourceCategory.{u}) (N : ℤ)
    (hF : ∀ n d, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj (F.obj n))) :
    ∀ d, d < N → Subsingleton
      ((sourceStableHomotopyAddFunctor d).obj (sourceHomotopyColimit F)) := by
  intro d hd
  exact sourceHomotopyColimit_stableHomotopy_subsingleton_of_eventually F d 0
    (fun n _ => hF n d hd)

end KIP126.StableHomotopy.Implementation
