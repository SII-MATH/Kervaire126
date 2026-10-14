module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Predicates
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Proofs
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

theorem pathHomotopic_refl {X Y : Prespectrum.{u}} (f : X ⟶ Y) : pathHomotopic f f :=
  ⟨StrictHomotopy.refl f⟩

theorem pathHomotopic_symm {X Y : Prespectrum.{u}} {f g : X ⟶ Y} (h : pathHomotopic f g) :
    pathHomotopic g f := ⟨h.some.symm⟩

theorem pathHomotopic_trans {X Y : Prespectrum.{u}} {f g k : X ⟶ Y}
    (h : pathHomotopic f g) (j : pathHomotopic g k) : pathHomotopic f k :=
  ⟨h.some.trans j.some⟩

theorem pathHomotopic_precomp {A X Y : Prespectrum.{u}} (a : A ⟶ X)
    {f g : X ⟶ Y} (h : pathHomotopic f g) : pathHomotopic (a ≫ f) (a ≫ g) :=
  ⟨h.some.precomp a⟩

theorem pathHomotopic_postcomp {X Y Z : Prespectrum.{u}} {f g : X ⟶ Y}
    (h : pathHomotopic f g) (b : Y ⟶ Z) : pathHomotopic (f ≫ b) (g ≫ b) :=
  ⟨h.some.postcomp b⟩

/-- The actual path relation itself is a congruence; no further closure of
the relation will be needed to construct its homotopy category. -/
instance pathHomotopic_congruence : Congruence pathHomotopic.{u} where
  equivalence := ⟨pathHomotopic_refl,pathHomotopic_symm,pathHomotopic_trans⟩
  comp_left := pathHomotopic_precomp
  comp_right := fun b h => pathHomotopic_postcomp h b

/-- Genuine strict path homotopies are already identified in the specified
ordinary localization at actual stable equivalences. -/
theorem source_map_eq_of_pathHomotopic {X Y : Prespectrum.{u}} {f g : X ⟶ Y}
    (h : pathHomotopic f g) : sourceLocalization.map f = sourceLocalization.map g := by
  obtain ⟨H⟩ := h
  calc
    sourceLocalization.map f = sourceLocalization.map (H.hom ≫ pathEvaluation Y 0) :=
      congrArg sourceLocalization.map H.zero.symm
    _ = sourceLocalization.map (H.hom ≫ pathEvaluation Y 1) := by
      rw [Functor.map_comp,Functor.map_comp,source_pathEvaluation_eq Y 0 1]
    _ = sourceLocalization.map g := congrArg sourceLocalization.map H.one

/-- Actual stable equivalence is invariant under the actual path homotopy relation. -/
theorem stableEquivalence_iff_of_pathHomotopic {X Y : Prespectrum.{u}} {f g : X ⟶ Y}
    (h : pathHomotopic f g) : stableEquivalences f ↔ stableEquivalences g := by
  rw [stableEquivalence_iff_source_isIso,stableEquivalence_iff_source_isIso,
    source_map_eq_of_pathHomotopic h]

instance stableEquivalences_hasHomotopyQuotient : stableEquivalences.{u}.HasQuotient pathHomotopic where
  iff := fun {_ _ _ _} h => stableEquivalence_iff_of_pathHomotopic h

end KIP126.StableHomotopy.Implementation.Prespectrum
