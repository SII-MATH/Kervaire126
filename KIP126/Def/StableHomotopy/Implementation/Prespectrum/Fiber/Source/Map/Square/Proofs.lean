module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Map.Homotopy.Equivalence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- A commuting square in the original stable localization has a common
strict source square, with stable denominators and actual square homotopies. -/
theorem source_square_exists_homotopy_roof {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : sourceLocalization.obj X ⟶ sourceLocalization.obj X')
    (b : sourceLocalization.obj Y ⟶ sourceLocalization.obj Y')
    (hf : sourceLocalization.map f ≫ b = a ≫ sourceLocalization.map g) :
    ∃ (P Q : Prespectrum.{u}) (h : P ⟶ Q) (s : P ⟶ X) (t : Q ⟶ Y)
      (a' : P ⟶ X') (b' : Q ⟶ Y'),
      stableEquivalences s ∧ stableEquivalences t ∧
      sourceLocalization.map s ≫ a = sourceLocalization.map a' ∧
      sourceLocalization.map t ≫ b = sourceLocalization.map b' ∧
      Nonempty (StrictHomotopy (h ≫ t) (s ≫ f)) ∧
      Nonempty (StrictHomotopy (h ≫ b') (a' ≫ g)) := by
  obtain ⟨A, sa, ta, hsa, ha⟩ := source_morphism_exists_roof a
  obtain ⟨B, sb, tb, hsb, hb⟩ := source_morphism_exists_roof b
  let P := homotopyPullback sb (sa ≫ f)
  let v : P ⟶ B := homotopyPullbackFst sb (sa ≫ f)
  let u : P ⟶ A := homotopyPullbackSnd sb (sa ≫ f)
  have hu : stableEquivalences u :=
    homotopyPullbackSnd_stableEquivalence sb (sa ≫ f) hsb
  have hv : sourceLocalization.map v ≫ sourceLocalization.map sb =
      sourceLocalization.map u ≫ sourceLocalization.map (sa ≫ f) :=
    source_homotopyPullback_comm sb (sa ≫ f)
  have heq : sourceLocalization.map (v ≫ tb) = sourceLocalization.map ((u ≫ ta) ≫ g) := by
    calc
      sourceLocalization.map (v ≫ tb) =
          sourceLocalization.map v ≫ sourceLocalization.map sb ≫ b := by
        rw [CategoryTheory.Functor.map_comp, hb]
      _ = sourceLocalization.map u ≫ sourceLocalization.map sa ≫ sourceLocalization.map f ≫ b := by
        rw [← Category.assoc, hv, CategoryTheory.Functor.map_comp, Category.assoc,
          Category.assoc]
      _ = sourceLocalization.map u ≫ sourceLocalization.map ta ≫ sourceLocalization.map g := by
        rw [hf, ← Category.assoc (sourceLocalization.map sa), ha]
      _ = sourceLocalization.map ((u ≫ ta) ≫ g) := by
        simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  obtain ⟨R, w, hw, ⟨H⟩⟩ :=
    (source_map_eq_iff_exists_homotopy_precomp (v ≫ tb) ((u ≫ ta) ≫ g)).mp heq
  refine ⟨R, B, w ≫ v, (w ≫ u) ≫ sa, sb, (w ≫ u) ≫ ta, tb,
    ?_, hsb, ?_, hb, ?_, ?_⟩
  · apply (stableEquivalence_iff_source_isIso _).mpr
    letI := stableEquivalences.Q_inverts w hw
    letI := stableEquivalences.Q_inverts u hu
    letI := stableEquivalences.Q_inverts sa hsa
    simp only [CategoryTheory.Functor.map_comp]
    infer_instance
  · simp only [CategoryTheory.Functor.map_comp, Category.assoc, ha]
  · exact ⟨by simpa only [Category.assoc] using
      StrictHomotopy.precomp w (homotopyPullbackStrictHomotopy sb (sa ≫ f))⟩
  · exact ⟨by simpa only [Category.assoc] using H⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
