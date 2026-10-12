module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Shift.Coefficient.Data
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

private theorem bijective_iff_of_equiv {A B C D : Type*}
    (a : A ≃ C) (b : B ≃ D) (f : A → B) (g : C → D)
    (h : ∀ x, b (f x) = g (a x)) : Function.Bijective f ↔ Function.Bijective g := by
  have hc : b ∘ f = g ∘ a := funext h
  rw [← Equiv.comp_bijective f b, hc, Equiv.bijective_comp a g]

private theorem precomp_bijective_target_iso
    {C : Type*} [Category* C] {A B T T' : C} (f : A ⟶ B) (e : T ≅ T') :
    Function.Bijective (fun a : B ⟶ T => f ≫ a) ↔
      Function.Bijective (fun a : B ⟶ T' => f ≫ a) := by
  apply bijective_iff_of_equiv (Iso.homCongr (Iso.refl B) e)
    (Iso.homCongr (Iso.refl A) e)
  intro a
  simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp, Category.assoc]

private theorem precomp_bijective_adjunction
    {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {A B : C} (f : A ⟶ B) (T : D) :
    Function.Bijective (fun a : F.obj B ⟶ T => F.map f ≫ a) ↔
      Function.Bijective (fun a : B ⟶ G.obj T => f ≫ a) :=
  bijective_iff_of_equiv (adj.homEquiv B T) (adj.homEquiv A T) _ _
    (fun a => adj.homEquiv_naturality_left f a)

/-- Actual source suspension preserves equivalences detected by all
integer shifts of the fixed source coefficient spectrum. -/
theorem HF2Equivalences.suspension {A B : SourceCategory.{0}} {f : A ⟶ B}
    (hf : HF2Equivalences f) : HF2Equivalences (Prespectrum.sourceSuspensionFunctor.map f) := by
  intro d
  apply (precomp_bijective_adjunction Prespectrum.sourceSuspensionEquivalence.toAdjunction
    f (sourceHF2Shift d)).mpr
  exact (precomp_bijective_target_iso f (sourceHF2DesuspensionShiftIso d)).mpr (hf (d - 1))

/-- Actual source desuspension preserves the same all-integer coefficient
equivalences. -/
theorem HF2Equivalences.desuspension {A B : SourceCategory.{0}} {f : A ⟶ B}
    (hf : HF2Equivalences f) : HF2Equivalences (Prespectrum.sourceDesuspensionFunctor.map f) := by
  intro d
  apply (precomp_bijective_adjunction Prespectrum.sourceSuspensionEquivalence.symm.toAdjunction
    f (sourceHF2Shift d)).mpr
  exact (precomp_bijective_target_iso f (sourceHF2SuspensionShiftIso d)).mpr (hf (d + 1))

/-- The actual suspension of an HF₂-local prespectrum is HF₂-local. -/
theorem Prespectrum.IsHF2Local.suspension {X : Prespectrum.{0}} (hX : X.IsHF2Local) :
    X.suspension.IsHF2Local := by
  intro A B f hf
  exact (precomp_bijective_adjunction sourceSuspensionEquivalence.symm.toAdjunction
    f (sourceLocalization.obj X)).mp
      (hX (sourceDesuspensionFunctor.map f) hf.desuspension)

/-- The actual padded desuspension of an HF₂-local prespectrum is HF₂-local. -/
theorem Prespectrum.IsHF2Local.desuspension {X : Prespectrum.{0}} (hX : X.IsHF2Local) :
    X.desuspension.IsHF2Local := by
  intro A B f hf
  exact (precomp_bijective_adjunction sourceSuspensionEquivalence.toAdjunction
    f (sourceLocalization.obj X)).mp
      (hX (sourceSuspensionFunctor.map f) hf.suspension)

end KIP126.StableHomotopy.Implementation
