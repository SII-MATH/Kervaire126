module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Prism.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial MonoidalCategory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual prism homeomorphism commutes with every face and
degeneracy map in its simplex coordinate. -/
theorem realizationSimplexPrismHomeomorph_natural_simplex (K : SSet.{u})
    {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (x : |K ⊗ Δ[m]|) :
    realizationSimplexPrismHomeomorph K n
      (SSet.toTop.map (K ◁ SSet.stdSimplex.map θ) x) =
      ((realizationSimplexPrismHomeomorph K m x).1,
        stdSimplex.map θ.toOrderHom (realizationSimplexPrismHomeomorph K m x).2) := by
  apply Prod.ext
  · change SSet.toTop.map (CartesianMonoidalCategory.fst K Δ[n])
      (SSet.toTop.map (K ◁ SSet.stdSimplex.map θ) x) =
      SSet.toTop.map (CartesianMonoidalCategory.fst K Δ[m]) x
    have h : (K ◁ SSet.stdSimplex.map θ) ≫ CartesianMonoidalCategory.fst K Δ[n] =
        CartesianMonoidalCategory.fst K Δ[m] := by simp
    have h' := congrArg SSet.toTop.map h
    simp only [Functor.map_comp] at h'
    exact ConcreteCategory.congr_hom h' x
  · change SimplexCategory.toTopHomeo ⦋n⦌
      (SSet.toTop.map (CartesianMonoidalCategory.snd K Δ[n])
        (SSet.toTop.map (K ◁ SSet.stdSimplex.map θ) x)) = _
    have h : (K ◁ SSet.stdSimplex.map θ) ≫ CartesianMonoidalCategory.snd K Δ[n] =
        CartesianMonoidalCategory.snd K Δ[m] ≫ SSet.stdSimplex.map θ := by simp
    rw [← TopCat.comp_app,← Functor.map_comp,h,Functor.map_comp,TopCat.comp_app,
      SimplexCategory.toTopHomeo_naturality_apply]
    rfl

/-- Evaluation of the actual prism lift is exactly the original map. -/
theorem singularPrism_evaluation (K : SSet.{u}) (B : TopCat.{u}) (n : ℕ)
    (f : C(|K| × stdSimplex ℝ (Fin (n+1)),B))
    (z : |K| × stdSimplex ℝ (Fin (n+1))) :
    sSetTopAdj.counit.app B (singularPrism K B n f z) = f z := by
  have h := (sSetTopAdj.homEquiv _ _).symm_apply_apply
    (TopCat.ofHom (Y := B) (f.comp ⟨realizationSimplexPrismHomeomorph K n,
      (realizationSimplexPrismHomeomorph K n).continuous⟩))
  rw [Adjunction.homEquiv_counit] at h
  have hz := ConcreteCategory.congr_hom h ((realizationSimplexPrismHomeomorph K n).symm z)
  change sSetTopAdj.counit.app B (singularPrism K B n f z) =
    f (realizationSimplexPrismHomeomorph K n ((realizationSimplexPrismHomeomorph K n).symm z)) at hz
  simpa only [Homeomorph.apply_symm_apply] using hz

/-- Every face or degeneracy of the actual singular prism is exactly
the singular lift of that face or degeneracy of the original map. -/
theorem singularPrism_simplex (K : SSet.{u}) (B : TopCat.{u})
    {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (f : C(|K| × stdSimplex ℝ (Fin (n+1)),B))
    (x : |K|) (s : stdSimplex ℝ (Fin (m+1))) :
    singularPrism K B n f (x,stdSimplex.map θ.toOrderHom s) =
      singularPrism K B m
        (f.comp ((ContinuousMap.id _).prodMap ⟨stdSimplex.map θ.toOrderHom,stdSimplex.continuous_map θ.toOrderHom⟩)) (x,s) := by
  have he : (realizationSimplexPrismHomeomorph K n).symm
      (x,stdSimplex.map θ.toOrderHom s) =
      SSet.toTop.map (K ◁ SSet.stdSimplex.map θ)
        ((realizationSimplexPrismHomeomorph K m).symm (x,s)) := by
    apply (realizationSimplexPrismHomeomorph K n).injective
    rw [Homeomorph.apply_symm_apply,realizationSimplexPrismHomeomorph_natural_simplex,
      Homeomorph.apply_symm_apply]
  have h : (K ◁ SSet.stdSimplex.map θ) ≫ singularPrismAdjoint K B n f =
      singularPrismAdjoint K B m
        (f.comp ((ContinuousMap.id _).prodMap ⟨stdSimplex.map θ.toOrderHom,stdSimplex.continuous_map θ.toOrderHom⟩)) := by
    rw [singularPrismAdjoint,← sSetTopAdj.homEquiv_naturality_left]
    unfold singularPrismAdjoint
    apply congrArg (sSetTopAdj.homEquiv _ _)
    apply ConcreteCategory.hom_ext
    intro y
    change f (realizationSimplexPrismHomeomorph K n
      (SSet.toTop.map (K ◁ SSet.stdSimplex.map θ) y)) = _
    rw [realizationSimplexPrismHomeomorph_natural_simplex]
    rfl
  change SSet.toTop.map (singularPrismAdjoint K B n f)
    ((realizationSimplexPrismHomeomorph K n).symm (x,stdSimplex.map θ.toOrderHom s)) = _
  rw [he,← TopCat.comp_app,← Functor.map_comp,h]
  rfl

end KIP126.StableHomotopy.Implementation
