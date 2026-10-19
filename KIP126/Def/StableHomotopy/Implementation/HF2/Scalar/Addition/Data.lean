module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Addition.Simplicial.Proofs
public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Product.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Scalar
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Opposite Simplicial
open HF2Bond Prespectrum
set_option backward.isDefEq.respectTransparency false

/-- The actual coefficient addition, a strict map on the paired
realization prespectrum. -/
noncomputable def addition : pairPrespectrum ⟶ hf2RealizationPrespectrum where
  level n := (SSet.toTop.map (additionSet n)).hom
  point n := by
    have h : (additionSet n).app (op ⦋0⦌)
        ((0 : (hf2SimplicialModule n).obj (op ⦋0⦌)),
          (0 : (hf2SimplicialModule n).obj (op ⦋0⦌))) =
        (0 : (hf2SimplicialModule n).obj (op ⦋0⦌)) :=
      @zero_add ((hf2SimplicialModule n).obj (op ⦋0⦌)) _ 0
    have hm := realizeSimplex_map (additionSet n) (op ⦋0⦌)
      ((0 : (hf2SimplicialModule n).obj (op ⦋0⦌)),
        (0 : (hf2SimplicialModule n).obj (op ⦋0⦌))) default
    rw [h] at hm
    exact hm.trans (realizeSimplex_zero _ _ _)
  bond n x t := by
    have h := coneSquare_realize (pairConeMap n)
      (coefficientToLoopSet n ≫ loopSetInclusion n) (additionSet n) (additionSet (n+1))
      (additionSet_cone n) x t
    simp only [Functor.map_comp,TopCat.comp_app] at h
    exact h

noncomputable def diagonal : hf2RealizationPrespectrum ⟶ pairPrespectrum where
  level n := (SSet.toTop.map (diagonalSet n)).hom
  point n := by
    change SSet.toTop.map _ (realizeSimplex _ _ _) = _
    rw [realizeSimplex_map]
    rfl
  bond n x t := by
    have h := coneSquare_realize (coefficientToLoopSet n ≫ loopSetInclusion n)
      (pairConeMap n) (diagonalSet n) (diagonalSet (n+1)) (diagonalSet_cone n) x t
    simp only [Functor.map_comp,TopCat.comp_app] at h
    exact h

noncomputable def inl : hf2RealizationPrespectrum ⟶ pairPrespectrum where
  level n := (SSet.toTop.map (inlSet n)).hom
  point n := by
    change SSet.toTop.map _ (realizeSimplex _ _ _) = _
    rw [realizeSimplex_map]
    rfl
  bond n x t := by
    have h := coneSquare_realize (coefficientToLoopSet n ≫ loopSetInclusion n)
      (pairConeMap n) (inlSet n) (inlSet (n+1)) (inlSet_cone n) x t
    simp only [Functor.map_comp,TopCat.comp_app] at h
    exact h

noncomputable def inr : hf2RealizationPrespectrum ⟶ pairPrespectrum where
  level n := (SSet.toTop.map (inrSet n)).hom
  point n := by
    change SSet.toTop.map _ (realizeSimplex _ _ _) = _
    rw [realizeSimplex_map]
    rfl
  bond n x t := by
    have h := coneSquare_realize (coefficientToLoopSet n ≫ loopSetInclusion n)
      (pairConeMap n) (inrSet n) (inrSet (n+1)) (inrSet_cone n) x t
    simp only [Functor.map_comp,TopCat.comp_app] at h
    exact h

end KIP126.StableHomotopy.Implementation.HF2Scalar
