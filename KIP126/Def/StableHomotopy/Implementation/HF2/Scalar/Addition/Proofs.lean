module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Addition.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Instances

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Scalar
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Simplicial
open HF2Bond Prespectrum
set_option backward.isDefEq.respectTransparency false

@[simp] theorem inl_pairFst : inl ≫ pairFst = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  change SSet.toTop.map (fst _ _) (SSet.toTop.map (inlSet n) x) = _
  have h : inlSet n ≫ fst (hf2SimplicialSet n) (hf2SimplicialSet n) = 𝟙 _ := by
    ext a z
    rfl
  rw [← TopCat.comp_app,← Functor.map_comp,h]
  exact ConcreteCategory.congr_hom (SSet.toTop.map_id _) x

@[simp] theorem inl_pairSnd : inl ≫ pairSnd = 0 := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  change SSet.toTop.map (snd _ _) (SSet.toTop.map (inlSet n) x) = _
  have h : inlSet n ≫ snd (hf2SimplicialSet n) (hf2SimplicialSet n) = zeroSet n := by
    ext a z
    rfl
  rw [← TopCat.comp_app,← Functor.map_comp,h]
  exact realization_zeroSet n x

@[simp] theorem inr_pairFst : inr ≫ pairFst = 0 := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  change SSet.toTop.map (fst _ _) (SSet.toTop.map (inrSet n) x) = _
  have h : inrSet n ≫ fst (hf2SimplicialSet n) (hf2SimplicialSet n) = zeroSet n := by
    ext a z
    rfl
  rw [← TopCat.comp_app,← Functor.map_comp,h]
  exact realization_zeroSet n x

@[simp] theorem inr_pairSnd : inr ≫ pairSnd = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  change SSet.toTop.map (snd _ _) (SSet.toTop.map (inrSet n) x) = _
  have h : inrSet n ≫ snd (hf2SimplicialSet n) (hf2SimplicialSet n) = 𝟙 _ := by
    ext a z
    rfl
  rw [← TopCat.comp_app,← Functor.map_comp,h]
  exact ConcreteCategory.congr_hom (SSet.toTop.map_id _) x

@[simp] theorem diagonal_pairFst : diagonal ≫ pairFst = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  change SSet.toTop.map (fst _ _) (SSet.toTop.map (diagonalSet n) x) = _
  have h : diagonalSet n ≫ fst (hf2SimplicialSet n) (hf2SimplicialSet n) = 𝟙 _ := by
    ext a z
    rfl
  rw [← TopCat.comp_app,← Functor.map_comp,h]
  exact ConcreteCategory.congr_hom (SSet.toTop.map_id _) x

@[simp] theorem diagonal_pairSnd : diagonal ≫ pairSnd = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  change SSet.toTop.map (snd _ _) (SSet.toTop.map (diagonalSet n) x) = _
  have h : diagonalSet n ≫ snd (hf2SimplicialSet n) (hf2SimplicialSet n) = 𝟙 _ := by
    ext a z
    rfl
  rw [← TopCat.comp_app,← Functor.map_comp,h]
  exact ConcreteCategory.congr_hom (SSet.toTop.map_id _) x

@[simp] theorem inl_addition : inl ≫ addition = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  change SSet.toTop.map (additionSet n) (SSet.toTop.map (inlSet n) x) = _
  rw [← TopCat.comp_app,← Functor.map_comp,inlSet_additionSet]
  exact ConcreteCategory.congr_hom (SSet.toTop.map_id _) x

@[simp] theorem inr_addition : inr ≫ addition = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  change SSet.toTop.map (additionSet n) (SSet.toTop.map (inrSet n) x) = _
  rw [← TopCat.comp_app,← Functor.map_comp,inrSet_additionSet]
  exact ConcreteCategory.congr_hom (SSet.toTop.map_id _) x

@[simp] theorem diagonal_addition : diagonal ≫ addition = 0 := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  change SSet.toTop.map (additionSet n) (SSet.toTop.map (diagonalSet n) x) = _
  rw [← TopCat.comp_app,← Functor.map_comp,diagonalSet_additionSet]
  exact realization_zeroSet n x

end KIP126.StableHomotopy.Implementation.HF2Scalar
