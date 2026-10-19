module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Moore.Postnikov.Relations.Data
public import KIP126.Def.StableHomotopy.Implementation.HF2.Moore.Postnikov.Cover.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Chosen.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- For a single-degree target the actual cover is surjective on every
original stable group. -/
theorem sourceModTwoMooreHeartCoverMap_homotopy_surjective
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) (d : ℤ) :
    Function.Surjective ((sourceStableHomotopyAddFunctor d).map
      (sourceModTwoMooreHeartCoverMap Y (fun k hk => hY k (by omega)) h₂)) := by
  by_cases hd : d = 0
  · subst d
    exact sourceModTwoMooreHeartCoverMap_surjective Y _ h₂
  · letI := hY d hd
    exact fun x => ⟨0,Subsingleton.elim _ _⟩

/-- The actual signed relation inclusion is injective on every original stable group. -/
theorem sourceModTwoMooreHeartRelationsInclusion_homotopy_injective
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) (d : ℤ) :
    Function.Injective ((sourceStableHomotopyAddFunctor d).map
      (sourceModTwoMooreHeartRelationsInclusion Y hY h₂)) :=
  sourceChosenFiberInclusion_homotopy_injective _ d
    (sourceModTwoMooreHeartCoverMap_homotopy_surjective Y hY h₂ (d+1))

/-- The actual relation object remains concentrated in degree zero. -/
theorem sourceModTwoMooreHeartRelations_homotopy_subsingleton
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) (d : ℤ) (hd : d ≠ 0) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj
      (sourceModTwoMooreHeartRelations Y hY h₂)) := by
  letI := sourceModTwoMooreHeartCover_homotopy_subsingleton Y d hd
  exact (sourceModTwoMooreHeartRelationsInclusion_homotopy_injective Y hY h₂ d).subsingleton

/-- The actual relation object also has characteristic two; no coefficient
identification of the original Moore heart is used. -/
theorem sourceModTwoMooreHeartRelations_two_id
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) :
    2 • 𝟙 (sourceModTwoMooreHeartRelations Y hY h₂) = 0 := by
  apply source_nsmul_id_eq_zero_of_homotopy_nsmul_eq_zero _ 0 2
    (sourceModTwoMooreHeartRelations_homotopy_subsingleton Y hY h₂)
  intro x
  let F := sourceStableHomotopyAddFunctor 0
  let i := sourceModTwoMooreHeartRelationsInclusion Y hY h₂
  apply sourceModTwoMooreHeartRelationsInclusion_homotopy_injective Y hY h₂ 0
  have hz := congrArg (fun a : sourceModTwoMooreHeartCover Y ⟶ sourceModTwoMooreHeartCover Y =>
    F.map a (F.map i x)) (sourceModTwoMooreHeartCover_two_id Y)
  rw [Functor.map_nsmul,CategoryTheory.Functor.map_id,Functor.map_zero] at hz
  change (F.map i) (2 • x) = (F.map i) 0
  rw [map_nsmul,map_zero]
  exact hz

/-- The original relation inclusion followed by the original cover map is zero. -/
@[reassoc (attr := simp)]
theorem sourceModTwoMooreHeartRelationsInclusion_coverMap
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) :
    sourceModTwoMooreHeartRelationsInclusion Y hY h₂ ≫
      sourceModTwoMooreHeartCoverMap Y (fun d hd => hY d (by omega)) h₂ = 0 :=
  comp_distTriang_mor_zero₁₂ _ (sourceChosenFiberTriangle_distinguished _)

end KIP126.StableHomotopy.Implementation

