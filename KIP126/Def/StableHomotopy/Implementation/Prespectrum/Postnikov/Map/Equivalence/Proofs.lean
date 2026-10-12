module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Functor
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Restriction.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Conservativity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- In every degree below the cutoff, the actual truncation map is a
bijection exactly when the original map is. -/
theorem sourcePostnikovMap_homotopy_bijective_iff {X Y : SourceCategory.{0}}
    (n d : ℤ) (hd : d < n) (f : X ⟶ Y) :
    Function.Bijective ((sourceStableHomotopyAddFunctor d).map (sourcePostnikovMap n f)) ↔
      Function.Bijective ((sourceStableHomotopyAddFunctor d).map f) := by
  let G := sourceStableHomotopyAddFunctor d
  have hcomm : G.map (sourcePostnikovMap n f) ∘ G.map (sourcePostnikovUnit X n) =
      G.map (sourcePostnikovUnit Y n) ∘ G.map f := by
    funext x
    change (G.map (sourcePostnikovUnit X n) ≫ G.map (sourcePostnikovMap n f)) x =
      (G.map f ≫ G.map (sourcePostnikovUnit Y n)) x
    rw [← G.map_comp, sourcePostnikovUnit_naturality, G.map_comp]
  rw [← Function.Bijective.of_comp_iff _
    (sourcePostnikovUnit_homotopy_bijective X n d hd), hcomm]
  exact Function.Bijective.of_comp_iff'
    (sourcePostnikovUnit_homotopy_bijective Y n d hd) _

/-- The actual Postnikov functor inverts precisely the maps inducing
isomorphisms on all original stable groups below its cutoff. -/
theorem sourcePostnikovMap_isIso_iff {X Y : SourceCategory.{0}}
    (n : ℤ) (f : X ⟶ Y) :
    IsIso (sourcePostnikovMap n f) ↔ ∀ d, d < n →
      Function.Bijective ((sourceStableHomotopyAddFunctor d).map f) := by
  constructor
  · intro hf d hd
    letI := hf
    apply (sourcePostnikovMap_homotopy_bijective_iff n d hd f).mp
    exact ConcreteCategory.bijective_of_isIso _
  · intro hf
    apply (source_isIso_iff_stableHomotopy_bijective _).mpr
    intro d
    have h : Function.Bijective
        ((sourceStableHomotopyAddFunctor d).map (sourcePostnikovMap n f)) := by
      by_cases hd : d < n
      · exact (sourcePostnikovMap_homotopy_bijective_iff n d hd f).mpr (hf d hd)
      · letI := sourcePostnikovTruncation_homotopy_subsingleton X n d (by omega)
        letI := sourcePostnikovTruncation_homotopy_subsingleton Y n d (by omega)
        exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
    change Function.Bijective ((forget AddCommGrpCat).map
      ((sourceStableHomotopyAddFunctor d).map (sourcePostnikovMap n f))) at h
    rwa [sourceStableHomotopyAddFunctor_forget_map] at h

/-- Restriction between cutoffs retains every original stable group below
the lower cutoff, via the same units. -/
theorem sourcePostnikovRestriction_homotopy_bijective
    (X : SourceCategory.{0}) (m n d : ℤ) (h : n ≤ m) (hd : d < n) :
    Function.Bijective ((sourceStableHomotopyAddFunctor d).map
      (sourcePostnikovRestriction X m n h)) := by
  let G := sourceStableHomotopyAddFunctor d
  apply (Function.Bijective.of_comp_iff _
    (sourcePostnikovUnit_homotopy_bijective X m d (hd.trans_le h))).mp
  have heq : G.map (sourcePostnikovRestriction X m n h) ∘
      G.map (sourcePostnikovUnit X m) = G.map (sourcePostnikovUnit X n) := by
    funext x
    change (G.map (sourcePostnikovUnit X m) ≫
      G.map (sourcePostnikovRestriction X m n h)) x = _
    rw [← G.map_comp, sourcePostnikovUnit_restriction]
  rw [heq]
  exact sourcePostnikovUnit_homotopy_bijective X n d hd

/-- Applying the smaller-cutoff functor to the larger-cutoff unit gives
an actual isomorphism, hence iterated truncation has the smaller cutoff. -/
theorem sourcePostnikovMap_unit_isIso (X : SourceCategory.{0}) (m n : ℤ) (h : n ≤ m) :
    IsIso (sourcePostnikovMap n (sourcePostnikovUnit X m)) :=
  (sourcePostnikovMap_isIso_iff n (sourcePostnikovUnit X m)).mpr
    (fun d hd => sourcePostnikovUnit_homotopy_bijective X m d (hd.trans_le h))

end KIP126.StableHomotopy.Implementation
