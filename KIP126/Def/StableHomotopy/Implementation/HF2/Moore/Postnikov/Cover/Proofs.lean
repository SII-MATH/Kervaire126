module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Moore.Postnikov.Cover.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Coproduct.Vanishing.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- The actual cover retains the representative of each original stable class. -/
@[reassoc (attr := simp)]
theorem sourceModTwoMooreHeartCoverMap_ι
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, 1 ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0)
    (y : (sourceStableHomotopyAddFunctor 0).obj Y) :
    Sigma.ι (fun _ : (sourceStableHomotopyAddFunctor 0).obj Y => sourceModTwoMooreHeart) y ≫
        sourceModTwoMooreHeartCoverMap Y hY h₂ =
      (sourceModTwoMooreHeartHomEquiv Y hY h₂).symm y := by
  simp only [sourceModTwoMooreHeartCoverMap,Sigma.ι_desc]

/-- Every original degree-zero stable class is hit by its own actual
Moore-heart summand. -/
theorem sourceModTwoMooreHeartCoverMap_surjective
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, 1 ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) :
    Function.Surjective ((sourceStableHomotopyAddFunctor 0).map
      (sourceModTwoMooreHeartCoverMap Y hY h₂)) := by
  let F := sourceStableHomotopyAddFunctor 0
  let A (_ : F.obj Y) := sourceModTwoMooreHeart
  let u := F.map sourceModTwoMooreHeartUnit (Prespectrum.sourceSphereGenerator 0)
  intro y
  refine ⟨F.map (Sigma.ι A y) u,?_⟩
  change (F.map (Sigma.ι A y) ≫ F.map (sourceModTwoMooreHeartCoverMap Y hY h₂)) u = y
  rw [← F.map_comp,sourceModTwoMooreHeartCoverMap_ι]
  have he := (sourceModTwoMooreHeartHomEquiv Y hY h₂).apply_symm_apply y
  change sourceModTwoMooreHeartEvaluation Y ((sourceModTwoMooreHeartHomEquiv Y hY h₂).symm y) = y at he
  rw [sourceModTwoMooreHeartEvaluation_apply] at he
  exact he

/-- The actual coproduct cover is itself concentrated in degree zero. -/
theorem sourceModTwoMooreHeartCover_homotopy_subsingleton
    (Y : SourceCategory.{0}) (d : ℤ) (hd : d ≠ 0) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceModTwoMooreHeartCover Y)) :=
  sourceCoproduct_homotopy_subsingleton _ d
    (fun _ => sourceModTwoMooreHeart_homotopy_subsingleton d hd)

/-- The actual coproduct cover, including its original identity, has characteristic two. -/
theorem sourceModTwoMooreHeartCover_two_id (Y : SourceCategory.{0}) :
    2 • 𝟙 (sourceModTwoMooreHeartCover Y) = 0 := by
  change 2 • 𝟙 (∐ fun _ : (sourceStableHomotopyAddFunctor 0).obj Y => sourceModTwoMooreHeart) = 0
  apply Sigma.hom_ext
  intro y
  rw [Preadditive.comp_nsmul,Category.comp_id,comp_zero]
  have hm : (2 • 𝟙 sourceModTwoMooreHeart) ≫
      Sigma.ι (fun _ : (sourceStableHomotopyAddFunctor 0).obj Y => sourceModTwoMooreHeart) y = 0 := by
    rw [sourceModTwoMooreHeart_two_id,zero_comp]
  simpa only [Preadditive.nsmul_comp,Category.id_comp] using hm

end KIP126.StableHomotopy.Implementation

