module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Cancellation.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyPullback.Stability.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[simp, reassoc] theorem homotopyPullbackDiagonal_fst {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    homotopyPullbackDiagonal f ≫ homotopyPullbackFst f f = 𝟙 X := rfl

@[simp, reassoc] theorem homotopyPullbackDiagonal_snd {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    homotopyPullbackDiagonal f ≫ homotopyPullbackSnd f f = 𝟙 X := rfl

/-- For a stable equivalence, its actual path diagonal is a stable equivalence. -/
theorem homotopyPullbackDiagonal_stableEquivalence {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (homotopyPullbackDiagonal f) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  haveI : IsIso (sourceLocalization.map (homotopyPullbackSnd f f)) :=
    (stableEquivalence_iff_source_isIso _).mp (homotopyPullbackSnd_stableEquivalence f f hf)
  haveI : IsIso (sourceLocalization.map (homotopyPullbackDiagonal f) ≫
      sourceLocalization.map (homotopyPullbackSnd f f)) := by
    rw [← Functor.map_comp,homotopyPullbackDiagonal_snd,sourceLocalization.map_id]
    infer_instance
  exact IsIso.of_isIso_comp_right (sourceLocalization.map (homotopyPullbackDiagonal f))
    (sourceLocalization.map (homotopyPullbackSnd f f))

/-- A genuine homotopy after a stable equivalence can be cancelled after
precomposition by an actual stable equivalence. The witness is an iterated
path homotopy pullback, and both equalities retain actual strict homotopies. -/
theorem pathHomotopic_cancel_stable {X Y Z : Prespectrum.{u}} (f g : X ⟶ Y)
    (s : Y ⟶ Z) (hs : stableEquivalences s) (h : pathHomotopic (f ≫ s) (g ≫ s)) :
    ∃ (A : Prespectrum.{u}) (t : A ⟶ X), stableEquivalences t ∧
      pathHomotopic (t ≫ f) (t ≫ g) := by
  obtain ⟨H⟩ := h
  let a : X ⟶ homotopyPullback s s := homotopyPullbackLift f g H.hom H.zero H.one
  let δ := homotopyPullbackDiagonal s
  let A := homotopyPullback δ a
  let t : A ⟶ X := homotopyPullbackSnd δ a
  have h₁ : pathHomotopic (homotopyPullbackFst δ a) (t ≫ f) := by
    have hh := pathHomotopic_postcomp (b := homotopyPullbackFst s s)
      (show pathHomotopic (homotopyPullbackFst δ a ≫ δ) (t ≫ a) from
        ⟨homotopyPullbackStrictHomotopy δ a⟩)
    simpa only [Category.assoc,δ,a,homotopyPullbackDiagonal_fst,
      homotopyPullbackLift_fst,Category.comp_id] using hh
  have h₂ : pathHomotopic (homotopyPullbackFst δ a) (t ≫ g) := by
    have hh := pathHomotopic_postcomp (b := homotopyPullbackSnd s s)
      (show pathHomotopic (homotopyPullbackFst δ a ≫ δ) (t ≫ a) from
        ⟨homotopyPullbackStrictHomotopy δ a⟩)
    simpa only [Category.assoc,δ,a,homotopyPullbackDiagonal_snd,
      homotopyPullbackLift_snd,Category.comp_id] using hh
  exact ⟨A,t,homotopyPullbackSnd_stableEquivalence δ a
    (homotopyPullbackDiagonal_stableEquivalence s hs),
    pathHomotopic_trans (pathHomotopic_symm h₁) h₂⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
