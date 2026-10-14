module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Localization.Roofs.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Two composable source maps have simultaneous roofs whose numerators
are a genuinely composable pair of strict prespectrum maps. -/
theorem source_composable_exists_roofs {X Y Z : Prespectrum.{u}}
    (a : sourceLocalization.obj X ⟶ sourceLocalization.obj Y)
    (b : sourceLocalization.obj Y ⟶ sourceLocalization.obj Z) :
    ∃ (A B : Prespectrum.{u}) (s : A ⟶ X) (t : B ⟶ Y) (f : A ⟶ B) (g : B ⟶ Z),
      stableEquivalences s ∧ stableEquivalences t ∧
        sourceLocalization.map s ≫ a = sourceLocalization.map f ≫ sourceLocalization.map t ∧
        sourceLocalization.map t ≫ b = sourceLocalization.map g := by
  obtain ⟨B,t,g,ht,hg⟩ := source_morphism_exists_roof b
  letI := stableEquivalences.Q_inverts t ht
  obtain ⟨A,s,f,hs,hf⟩ := source_morphism_exists_roof (a ≫ inv (sourceLocalization.map t))
  refine ⟨A,B,s,t,f,g,hs,ht,?_,hg⟩
  rw [← hf,Category.assoc,Category.assoc,IsIso.inv_hom_id,Category.comp_id]

/-- Every composable diagram in the original localization is isomorphic
on its three objects to a genuinely composable strict prespectrum diagram. -/
theorem source_composable_exists_strict {A B C : SourceCategory.{u}}
    (a : A ⟶ B) (b : B ⟶ C) :
    ∃ (X Y Z : Prespectrum.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (e₁ : A ≅ sourceLocalization.obj X) (e₂ : B ≅ sourceLocalization.obj Y)
      (e₃ : C ≅ sourceLocalization.obj Z),
      a ≫ e₂.hom = e₁.hom ≫ sourceLocalization.map f ∧
      b ≫ e₃.hom = e₂.hom ≫ sourceLocalization.map g := by
  rcases A with ⟨⟨A⟩⟩
  rcases B with ⟨⟨B⟩⟩
  rcases C with ⟨⟨C⟩⟩
  obtain ⟨X,Y,s,t,f,g,hs,ht,hf,hg⟩ := source_composable_exists_roofs a b
  letI := stableEquivalences.Q_inverts s hs
  letI := stableEquivalences.Q_inverts t ht
  refine ⟨X,Y,C,f,g,(asIso (sourceLocalization.map s)).symm,
    (asIso (sourceLocalization.map t)).symm,Iso.refl _,?_,?_⟩
  · change a ≫ inv (sourceLocalization.map t) =
      inv (sourceLocalization.map s) ≫ sourceLocalization.map f
    apply (cancel_epi (sourceLocalization.map s)).mp
    rw [← Category.assoc,hf,Category.assoc,IsIso.hom_inv_id,Category.comp_id,
      IsIso.hom_inv_id_assoc]
  · change b ≫ 𝟙 _ = inv (sourceLocalization.map t) ≫ sourceLocalization.map g
    rw [Category.comp_id,← hg,IsIso.inv_hom_id_assoc]

end KIP126.StableHomotopy.Implementation.Prespectrum
