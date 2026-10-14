module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Prism.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial MonoidalCategory

universe u

set_option backward.isDefEq.respectTransparency false

theorem realizationSimplexPrismHomeomorph_natural_source {K L : SSet.{u}}
    (φ : K ⟶ L) (n : ℕ) (x : |K ⊗ Δ[n]|) :
    realizationSimplexPrismHomeomorph L n (SSet.toTop.map (φ ▷ Δ[n]) x) =
      (SSet.toTop.map φ (realizationSimplexPrismHomeomorph K n x).1,
        (realizationSimplexPrismHomeomorph K n x).2) := by
  apply Prod.ext
  · change SSet.toTop.map (CartesianMonoidalCategory.fst L Δ[n])
      (SSet.toTop.map (φ ▷ Δ[n]) x) =
      SSet.toTop.map φ (SSet.toTop.map (CartesianMonoidalCategory.fst K Δ[n]) x)
    have h : (φ ▷ Δ[n]) ≫ CartesianMonoidalCategory.fst L Δ[n] =
        CartesianMonoidalCategory.fst K Δ[n] ≫ φ := by simp
    rw [← TopCat.comp_app,← Functor.map_comp,h,Functor.map_comp,TopCat.comp_app]
  · change SimplexCategory.toTopHomeo ⦋n⦌
      (SSet.toTop.map (CartesianMonoidalCategory.snd L Δ[n])
        (SSet.toTop.map (φ ▷ Δ[n]) x)) = _
    have h : (φ ▷ Δ[n]) ≫ CartesianMonoidalCategory.snd L Δ[n] =
        CartesianMonoidalCategory.snd K Δ[n] := by simp
    rw [← TopCat.comp_app,← Functor.map_comp,h]
    rfl

/-- Restricting the actual simplex prism to an actual simplicial source
map agrees strictly with lifting the restricted map. -/
theorem singularPrism_precomp {K L : SSet.{u}} (φ : K ⟶ L) (B : TopCat.{u})
    (n : ℕ) (f : C(|L| × stdSimplex ℝ (Fin (n+1)),B))
    (x : |K|) (s : stdSimplex ℝ (Fin (n+1))) :
    singularPrism L B n f (SSet.toTop.map φ x,s) =
      singularPrism K B n
        (f.comp ((SSet.toTop.map φ).hom.prodMap (ContinuousMap.id _))) (x,s) := by
  have he : (realizationSimplexPrismHomeomorph L n).symm
      (SSet.toTop.map φ x,s) = SSet.toTop.map (φ ▷ Δ[n])
        ((realizationSimplexPrismHomeomorph K n).symm (x,s)) := by
    apply (realizationSimplexPrismHomeomorph L n).injective
    rw [Homeomorph.apply_symm_apply,realizationSimplexPrismHomeomorph_natural_source,
      Homeomorph.apply_symm_apply]
  have h : (φ ▷ Δ[n]) ≫ singularPrismAdjoint L B n f =
      singularPrismAdjoint K B n
        (f.comp ((SSet.toTop.map φ).hom.prodMap (ContinuousMap.id _))) := by
    rw [singularPrismAdjoint,← sSetTopAdj.homEquiv_naturality_left]
    unfold singularPrismAdjoint
    apply congrArg (sSetTopAdj.homEquiv _ _)
    apply ConcreteCategory.hom_ext
    intro y
    change f (realizationSimplexPrismHomeomorph L n
      (SSet.toTop.map (φ ▷ Δ[n]) y)) = _
    rw [realizationSimplexPrismHomeomorph_natural_source]
    rfl
  change SSet.toTop.map (singularPrismAdjoint L B n f)
    ((realizationSimplexPrismHomeomorph L n).symm (SSet.toTop.map φ x,s)) = _
  rw [he,← TopCat.comp_app,← Functor.map_comp,h]
  rfl

/-- If the original map is independent of its simplex parameter, so is
its actual prism lift, with the realized adjoint as its exact value. -/
theorem singularPrism_timeIndependent (K : SSet.{u}) (B : TopCat.{u}) (n : ℕ)
    (f : C(|K|,B)) (x : |K|) (s : stdSimplex ℝ (Fin (n+1))) :
    singularPrism K B n (f.comp ContinuousMap.fst) (x,s) =
      SSet.toTop.map (sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B) f)) x := by
  have h : singularPrismAdjoint K B n (f.comp ContinuousMap.fst) =
      CartesianMonoidalCategory.fst K Δ[n] ≫
        sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B) f) := by
    rw [← sSetTopAdj.homEquiv_naturality_left]
    rfl
  change SSet.toTop.map (singularPrismAdjoint K B n (f.comp ContinuousMap.fst))
    ((realizationSimplexPrismHomeomorph K n).symm (x,s)) = _
  rw [h,Functor.map_comp,TopCat.comp_app]
  apply congrArg (SSet.toTop.map _)
  exact congrArg Prod.fst ((realizationSimplexPrismHomeomorph K n).apply_symm_apply (x,s))

/-- A simplex prism fixes an entire realized simplicial region whenever
the prescribed map is constant in the parameter on that region. -/
theorem singularPrism_fixed_subcomplex {K L : SSet.{u}} (φ : K ⟶ L)
    (B : TopCat.{u}) (n : ℕ)
    (f : C(|L| × stdSimplex ℝ (Fin (n+1)),B)) (g : C(|K|,B))
    (h : ∀ x s, f (SSet.toTop.map φ x,s) = g x)
    (x : |K|) (s : stdSimplex ℝ (Fin (n+1))) :
    singularPrism L B n f (SSet.toTop.map φ x,s) =
      SSet.toTop.map (sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B) g)) x := by
  rw [singularPrism_precomp]
  have he : f.comp ((SSet.toTop.map φ).hom.prodMap (ContinuousMap.id _)) =
      g.comp ContinuousMap.fst := by
    apply ContinuousMap.ext
    intro z
    exact h z.1 z.2
  rw [he,singularPrism_timeIndependent]

end KIP126.StableHomotopy.Implementation
