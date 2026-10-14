module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Triangle.Comparison.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Pretriangulated

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual Moore functor preserves distinguished triangles in the
original source category. The comparison is built by TR3 and proved
invertible by its represented universal property. -/
theorem sourceMooreCompletionFunctor_map_distinguished (p : ℕ)
    (T : Triangle SourceCategory.{u}) (hT : T ∈ distTriang SourceCategory) :
    (sourceMooreCompletionFunctor p).mapTriangle.obj T ∈ distTriang SourceCategory := by
  let f := sourceMooreCompletionMap p T.mor₁
  let S := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hS : S ∈ distTriang SourceCategory := HasFunctorialCofiber.cofib_distinguished f
  have hC : SourceIsScalarComplete p S.obj₃ :=
    SourceIsScalarComplete.triangle_third p S hS
      (sourceMooreCompletion_scalarComplete p T.obj₁)
      (sourceMooreCompletion_scalarComplete p T.obj₂)
  have hc₁ : T.mor₁ ≫ sourceMooreCompletionUnit p T.obj₂ =
      sourceMooreCompletionUnit p T.obj₁ ≫ S.mor₁ :=
    (sourceMooreCompletionMap_unit p T.mor₁).symm
  obtain ⟨q,hq₂,hq₃⟩ := complete_distinguished_triangle_morphism T S hT hS
    (sourceMooreCompletionUnit p T.obj₁) (sourceMooreCompletionUnit p T.obj₂) hc₁
  let φ : T ⟶ S := Triangle.homMk T S (sourceMooreCompletionUnit p T.obj₁)
    (sourceMooreCompletionUnit p T.obj₂) q hc₁ hq₂ hq₃
  have hq (L : SourceCategory.{u}) (hL : SourceIsScalarComplete p L) :
      Function.Bijective (fun a : S.obj₃ ⟶ L => q ≫ a) :=
    sourceTriangle_precomp_third_bijective T S hT hS φ L
      (sourceMooreCompletionUnit_precomp_bijective p T.obj₁ L hL)
      (sourceMooreCompletionUnit_precomp_bijective p T.obj₂ L hL)
      (sourceMooreCompletionUnit_shift_precomp_bijective p T.obj₁ L 1 hL)
      (sourceMooreCompletionUnit_shift_precomp_bijective p T.obj₂ L 1 hL)
  obtain ⟨k,hk⟩ := (sourceMooreCompletionUnit_precomp_bijective p T.obj₃ S.obj₃ hC).surjective q
  obtain ⟨l,hl⟩ := (hq (sourceMooreCompletion p T.obj₃)
    (sourceMooreCompletion_scalarComplete p T.obj₃)).surjective (sourceMooreCompletionUnit p T.obj₃)
  change sourceMooreCompletionUnit p T.obj₃ ≫ k = q at hk
  change q ≫ l = sourceMooreCompletionUnit p T.obj₃ at hl
  have hkl : k ≫ l = 𝟙 _ := by
    apply sourceMooreCompletion_hom_ext p
    rw [← Category.assoc, hk, hl, Category.comp_id]
  have hlk : l ≫ k = 𝟙 _ := by
    apply (hq S.obj₃ hC).injective
    change q ≫ (l ≫ k) = q ≫ 𝟙 _
    rw [← Category.assoc, hl, hk, Category.comp_id]
  letI : IsIso k := ⟨⟨l,hkl,hlk⟩⟩
  apply isomorphic_distinguished S hS _
  refine Triangle.isoMk _ S (Iso.refl _) (Iso.refl _) (asIso k) ?_ ?_ ?_
  · change sourceMooreCompletionMap p T.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ f
    simp only [Category.comp_id, Category.id_comp]
    rfl
  · change sourceMooreCompletionMap p T.mor₂ ≫ k = 𝟙 _ ≫ S.mor₂
    rw [Category.id_comp]
    apply (sourceMooreCompletionUnit_precomp_bijective p T.obj₂ S.obj₃ hC).injective
    change sourceMooreCompletionUnit p T.obj₂ ≫ (sourceMooreCompletionMap p T.mor₂ ≫ k) =
      sourceMooreCompletionUnit p T.obj₂ ≫ S.mor₂
    rw [← Category.assoc, sourceMooreCompletionMap_unit, Category.assoc, hk]
    exact hq₂
  · change (sourceMooreCompletionMap p T.mor₃ ≫ sourceMooreShiftComparison p 1 T.obj₁) ≫
      (𝟙 (sourceMooreCompletion p T.obj₁))⟦(1 : ℤ)⟧' = k ≫ S.mor₃
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    apply (sourceMooreCompletionUnit_precomp_bijective p T.obj₃ _
      ((sourceMooreCompletion_scalarComplete p T.obj₁).shift 1)).injective
    change sourceMooreCompletionUnit p T.obj₃ ≫
        (sourceMooreCompletionMap p T.mor₃ ≫ sourceMooreShiftComparison p 1 T.obj₁) =
      sourceMooreCompletionUnit p T.obj₃ ≫ (k ≫ S.mor₃)
    rw [← Category.assoc, sourceMooreCompletionMap_unit, Category.assoc,
      sourceMooreShiftComparison_unit, ← Category.assoc, hk]
    exact hq₃

/-- The existing actual additive Moore functor, with its already proved
coherent shift comparison, is a triangulated functor. -/
instance sourceMooreCompletionFunctor_isTriangulated (p : ℕ) :
    (sourceMooreCompletionFunctor.{u} p).IsTriangulated where
  map_distinguished := sourceMooreCompletionFunctor_map_distinguished p

end KIP126.StableHomotopy.Implementation
