module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Triangle.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Shift.CommShift
public import Mathlib.Algebra.FiveLemma

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Pretriangulated

universe u

set_option backward.isDefEq.respectTransparency false

private theorem triangle_precomp_exact (T : Triangle SourceCategory.{u})
    (hT : T ∈ distTriang SourceCategory) (L : SourceCategory.{u}) :
    Function.Exact (Preadditive.leftComp L T.mor₂) (Preadditive.leftComp L T.mor₁) := by
  intro a
  change T.mor₁ ≫ a = 0 ↔ ∃ b, T.mor₂ ≫ b = a
  constructor
  · intro h
    obtain ⟨b,hb⟩ := T.yoneda_exact₂ hT a h
    exact ⟨b,hb.symm⟩
  · rintro ⟨b,rfl⟩
    rw [← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, Limits.zero_comp]

/-- A morphism of actual distinguished triangles that induces bijections
into a target on the first two objects and their suspensions also does so
on the third object. This is the represented five lemma. -/
theorem sourceTriangle_precomp_third_bijective
    (T S : Triangle SourceCategory.{u}) (hT : T ∈ distTriang SourceCategory)
    (hS : S ∈ distTriang SourceCategory) (φ : T ⟶ S) (L : SourceCategory.{u})
    (h₁ : Function.Bijective (fun a : S.obj₁ ⟶ L => φ.hom₁ ≫ a))
    (h₂ : Function.Bijective (fun a : S.obj₂ ⟶ L => φ.hom₂ ≫ a))
    (h₁s : Function.Bijective (fun a : S.obj₁⟦(1 : ℤ)⟧ ⟶ L => φ.hom₁⟦1⟧' ≫ a))
    (h₂s : Function.Bijective (fun a : S.obj₂⟦(1 : ℤ)⟧ ⟶ L => φ.hom₂⟦1⟧' ≫ a)) :
    Function.Bijective (fun a : S.obj₃ ⟶ L => φ.hom₃ ≫ a) := by
  apply AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (Preadditive.leftComp L (-S.mor₁⟦(1 : ℤ)⟧'))
    (Preadditive.leftComp L S.mor₃) (Preadditive.leftComp L S.mor₂)
    (Preadditive.leftComp L S.mor₁)
    (Preadditive.leftComp L (-T.mor₁⟦(1 : ℤ)⟧'))
    (Preadditive.leftComp L T.mor₃) (Preadditive.leftComp L T.mor₂)
    (Preadditive.leftComp L T.mor₁)
    (Preadditive.leftComp L (φ.hom₂⟦(1 : ℤ)⟧'))
    (Preadditive.leftComp L (φ.hom₁⟦(1 : ℤ)⟧'))
    (Preadditive.leftComp L φ.hom₃) (Preadditive.leftComp L φ.hom₂)
    (Preadditive.leftComp L φ.hom₁)
  · ext z
    symm
    dsimp only [AddMonoidHom.comp_apply, Preadditive.leftComp, AddMonoidHom.mk',
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    simp only [← Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp,
      ← CategoryTheory.Functor.map_comp, φ.comm₁]
  · ext z
    symm
    change φ.hom₃ ≫ (S.mor₃ ≫ z) = T.mor₃ ≫ (φ.hom₁⟦(1 : ℤ)⟧' ≫ z)
    rw [← Category.assoc, ← Category.assoc, φ.comm₃]
  · ext z
    symm
    change φ.hom₂ ≫ (S.mor₂ ≫ z) = T.mor₂ ≫ (φ.hom₃ ≫ z)
    rw [← Category.assoc, ← Category.assoc, φ.comm₂]
  · ext z
    symm
    change φ.hom₁ ≫ (S.mor₁ ≫ z) = T.mor₁ ≫ (φ.hom₂ ≫ z)
    rw [← Category.assoc, ← Category.assoc, φ.comm₁]
  · exact triangle_precomp_exact S.rotate.rotate
      (rot_of_distTriang _ (rot_of_distTriang _ hS)) L
  · exact triangle_precomp_exact S.rotate (rot_of_distTriang _ hS) L
  · exact triangle_precomp_exact S hS L
  · exact triangle_precomp_exact T.rotate.rotate
      (rot_of_distTriang _ (rot_of_distTriang _ hT)) L
  · exact triangle_precomp_exact T.rotate (rot_of_distTriang _ hT) L
  · exact triangle_precomp_exact T hT L
  · exact h₂s.surjective
  · exact h₁s
  · exact h₂
  · exact h₁.injective

end KIP126.StableHomotopy.Implementation
