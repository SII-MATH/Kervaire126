module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Product.Level.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Scalar

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Opposite Simplicial
open HF2Bond
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- The cone evaluation used by the coefficient spectrum is natural in
the actual simplicial map. -/
theorem coneEvaluation_natural {A B : SSet.{0}} (f : A ⟶ B)
    (x : |decalage A|) (t : I) :
    SSet.toTop.map f (coneEvaluation A (x,t)) =
      coneEvaluation B (SSet.toTop.map (Functor.whiskerLeft coneFunctor.op f) x,t) := by
  let l : |decalage A| ⟶ |B| := TopCat.ofHom
    ⟨fun x => SSet.toTop.map f (coneEvaluation A (x,t)),
      (SSet.toTop.map f).hom.continuous.comp
        ((coneEvaluation A).continuous.comp (continuous_id.prodMk continuous_const))⟩
  let r : |decalage A| ⟶ |B| := TopCat.ofHom
    ⟨fun x => coneEvaluation B
      (SSet.toTop.map (Functor.whiskerLeft coneFunctor.op f) x,t),
      (coneEvaluation B).continuous.comp
        ((SSet.toTop.map (Functor.whiskerLeft coneFunctor.op f)).hom.continuous.prodMk
          continuous_const)⟩
  have h : l = r := by
    apply realization_hom_ext
    intro a z u
    change SSet.toTop.map f (coneEvaluation A (realizeSimplex (decalage A) z u,t)) =
      coneEvaluation B
        (SSet.toTop.map (Functor.whiskerLeft coneFunctor.op f)
          (realizeSimplex (decalage A) z u),t)
    erw [coneEvaluation_realizeSimplex,realizeSimplex_map,realizeSimplex_map,
      coneEvaluation_realizeSimplex]
    rfl
  exact ConcreteCategory.congr_hom h x

@[simp] theorem pairLevel_fst_point (n : ℕ) :
    SSet.toTop.map (fst (hf2SimplicialSet n) (hf2SimplicialSet n)) (pairLevel n).point =
      (hf2RealizationLevel n).point := by
  change SSet.toTop.map _ (realizeSimplex _ _ _) = _
  rw [realizeSimplex_map]
  exact realizeSimplex_zero _ _ _

@[simp] theorem pairLevel_snd_point (n : ℕ) :
    SSet.toTop.map (snd (hf2SimplicialSet n) (hf2SimplicialSet n)) (pairLevel n).point =
      (hf2RealizationLevel n).point := by
  change SSet.toTop.map _ (realizeSimplex _ _ _) = _
  rw [realizeSimplex_map]
  exact realizeSimplex_zero _ _ _

theorem pairBond_fst (n : ℕ) (x : pairLevel n) (t : I) :
    SSet.toTop.map (fst (hf2SimplicialSet (n+1)) (hf2SimplicialSet (n+1)))
        (pairBond n (x,t)) =
      bond n (SSet.toTop.map (fst (hf2SimplicialSet n) (hf2SimplicialSet n)) x,t) := by
  change SSet.toTop.map _ (coneEvaluation _ (_,t)) = _
  rw [coneEvaluation_natural]
  change coneEvaluation _ (SSet.toTop.map _ (SSet.toTop.map _ x),t) =
    coneEvaluation _ (SSet.toTop.map _ (SSet.toTop.map _ (SSet.toTop.map _ x)),t)
  simp only [← TopCat.comp_app,← Functor.map_comp]
  congr 2

theorem pairBond_snd (n : ℕ) (x : pairLevel n) (t : I) :
    SSet.toTop.map (snd (hf2SimplicialSet (n+1)) (hf2SimplicialSet (n+1)))
        (pairBond n (x,t)) =
      bond n (SSet.toTop.map (snd (hf2SimplicialSet n) (hf2SimplicialSet n)) x,t) := by
  change SSet.toTop.map _ (coneEvaluation _ (_,t)) = _
  rw [coneEvaluation_natural]
  change coneEvaluation _ (SSet.toTop.map _ (SSet.toTop.map _ x),t) =
    coneEvaluation _ (SSet.toTop.map _ (SSet.toTop.map _ (SSet.toTop.map _ x)),t)
  simp only [← TopCat.comp_app,← Functor.map_comp]
  congr 2

theorem pairBond_zero (n : ℕ) (x : pairLevel n) :
    pairBond n (x,0) = (pairLevel (n+1)).point := by
  apply (KIP126.Topology.SimplicialRealization.productComparison_bijective
    (hf2SimplicialSet (n+1)) (hf2SimplicialSet (n+1))).1
  apply Prod.ext
  · exact (pairBond_fst n x 0).trans ((bond_zero n _).trans (pairLevel_fst_point _).symm)
  · exact (pairBond_snd n x 0).trans ((bond_zero n _).trans (pairLevel_snd_point _).symm)

theorem pairBond_one (n : ℕ) (x : pairLevel n) :
    pairBond n (x,1) = (pairLevel (n+1)).point := by
  apply (KIP126.Topology.SimplicialRealization.productComparison_bijective
    (hf2SimplicialSet (n+1)) (hf2SimplicialSet (n+1))).1
  apply Prod.ext
  · exact (pairBond_fst n x 1).trans ((bond_one n _).trans (pairLevel_fst_point _).symm)
  · exact (pairBond_snd n x 1).trans ((bond_one n _).trans (pairLevel_snd_point _).symm)

theorem pairBond_point (n : ℕ) (t : I) :
    pairBond n ((pairLevel n).point,t) = (pairLevel (n+1)).point := by
  apply (KIP126.Topology.SimplicialRealization.productComparison_bijective
    (hf2SimplicialSet (n+1)) (hf2SimplicialSet (n+1))).1
  apply Prod.ext
  · change SSet.toTop.map _ (pairBond n (_,t)) = SSet.toTop.map _ _
    rw [pairBond_fst,pairLevel_fst_point,pairLevel_fst_point,bond_point]
  · change SSet.toTop.map _ (pairBond n (_,t)) = SSet.toTop.map _ _
    rw [pairBond_snd,pairLevel_snd_point,pairLevel_snd_point,bond_point]

end KIP126.StableHomotopy.Implementation.HF2Scalar
