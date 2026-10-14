module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Moore.Postnikov.Relations.Proofs
public import KIP126.Def.StableHomotopy.Implementation.HF2.Additive.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- Conditional on the original coefficient comparison being invertible,
the original Moore-heart stable group consists of zero and its specified unit.
The comparison's invertibility remains an explicit hypothesis. -/
theorem sourceModTwoMooreHeart_homotopy_eq_zero_or_unit
    [IsIso sourceModTwoMooreHeartToHF2]
    (x : (sourceStableHomotopyAddFunctor 0).obj sourceModTwoMooreHeart) :
    x = 0 ∨ x = (sourceStableHomotopyAddFunctor 0).map sourceModTwoMooreHeartUnit
      (Prespectrum.sourceSphereGenerator 0) := by
  let F := sourceStableHomotopyAddFunctor 0
  have hinj := (ConcreteCategory.bijective_of_isIso (F.map sourceModTwoMooreHeartToHF2)).injective
  let c := sourceHF2PiZeroAddEquiv (F.map sourceModTwoMooreHeartToHF2 x)
  have hc : c = 0 ∨ c = 1 := by
    have hv := ZMod.val_lt c
    have h : c.val = 0 ∨ c.val = 1 := by omega
    exact h.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
  rcases hc with hc | hc
  · left
    apply hinj
    apply sourceHF2PiZeroAddEquiv.injective
    simpa only [map_zero] using hc
  · right
    apply hinj
    apply sourceHF2PiZeroAddEquiv.injective
    exact hc.trans sourceModTwoMooreHeartToHF2_generator.symm

/-- Under the specified coefficient comparison, every additive map between
the original stable groups of exponent-two hearts is induced by an actual
stable-category map. The proof descends the actual Moore-heart cover through
its actual relation triangle. -/
theorem source_homotopy_map_surjective_of_exponent_two_heart
    [IsIso sourceModTwoMooreHeartToHF2]
    (X Y : SourceCategory.{0})
    (hX : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hY : ∀ d : ℤ, 1 ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (hX₂ : ∀ x : (sourceStableHomotopyAddFunctor 0).obj X, 2 • x = 0)
    (hY₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) :
    Function.Surjective (fun f : X ⟶ Y => (sourceStableHomotopyAddFunctor 0).map f) := by
  let F := sourceStableHomotopyAddFunctor 0
  intro α
  let A (_ : F.obj X) := sourceModTwoMooreHeart
  let p := sourceModTwoMooreHeartCoverMap X (fun d hd => hX d (by omega)) hX₂
  let a : sourceModTwoMooreHeartCover X ⟶ Y :=
    Sigma.desc (fun x => (sourceModTwoMooreHeartHomEquiv Y hY hY₂).symm (α x))
  have ha : F.map a = F.map p ≫ α := by
    let c : Cofan (fun x : F.obj X => F.obj (A x)) :=
      Cofan.mk (F.obj (∐ A)) (fun x => F.map (Sigma.ι A x))
    have hc : IsColimit c := isColimitOfHasCoproductOfPreservesColimit F A
    apply hc.hom_ext
    rintro ⟨x⟩
    change F.map (Sigma.ι A x) ≫ F.map a = F.map (Sigma.ι A x) ≫ (F.map p ≫ α)
    rw [← F.map_comp, ← Category.assoc, ← F.map_comp]
    rw [sourceModTwoMooreHeartCoverMap_ι]
    simp only [a,Sigma.ι_desc]
    apply AddCommGrpCat.ext
    intro z
    rcases sourceModTwoMooreHeart_homotopy_eq_zero_or_unit z with rfl | rfl
    · simp
    · have hx := (sourceModTwoMooreHeartHomEquiv X
        (fun d hd => hX d (by omega)) hX₂).apply_symm_apply x
      have hy := (sourceModTwoMooreHeartHomEquiv Y hY hY₂).apply_symm_apply (α x)
      change sourceModTwoMooreHeartEvaluation X _ = x at hx
      change sourceModTwoMooreHeartEvaluation Y _ = α x at hy
      rw [sourceModTwoMooreHeartEvaluation_apply] at hx hy
      exact hy.trans (congrArg α hx).symm
  let r := sourceModTwoMooreHeartRelationsInclusion X hX hX₂
  have hra : r ≫ a = 0 := by
    apply source_hom_eq_of_homotopy_map_eq 0
      (fun d hd => sourceModTwoMooreHeartRelations_homotopy_subsingleton X hX hX₂ d (by omega))
      (fun d hd => hY d (by omega))
    rw [F.map_comp,ha,← Category.assoc,← F.map_comp]
    change F.map (r ≫ p) ≫ α = F.map 0
    rw [sourceModTwoMooreHeartRelationsInclusion_coverMap, F.map_zero, zero_comp, F.map_zero]
  obtain ⟨f,hf⟩ := (sourceChosenFiberTriangle p).yoneda_exact₂
    (sourceChosenFiberTriangle_distinguished p) a hra
  change a = p ≫ f at hf
  refine ⟨f,?_⟩
  apply AddCommGrpCat.ext
  intro x
  obtain ⟨z,rfl⟩ := sourceModTwoMooreHeartCoverMap_surjective X
    (fun d hd => hX d (by omega)) hX₂ x
  change (F.map p ≫ F.map f) z = (F.map p ≫ α) z
  rw [← F.map_comp,← hf,ha]

/-- The original degree-zero stable group is fully faithful on actual
exponent-two hearts, conditional only on the original Moore-heart comparison. -/
theorem source_homotopy_map_bijective_of_exponent_two_heart
    [IsIso sourceModTwoMooreHeartToHF2]
    (X Y : SourceCategory.{0})
    (hX : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hY : ∀ d : ℤ, 1 ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (hX₂ : ∀ x : (sourceStableHomotopyAddFunctor 0).obj X, 2 • x = 0)
    (hY₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) :
    Function.Bijective (fun f : X ⟶ Y => (sourceStableHomotopyAddFunctor 0).map f) := by
  refine ⟨?_,source_homotopy_map_surjective_of_exponent_two_heart X Y hX hY hX₂ hY₂⟩
  intro f g hfg
  exact source_hom_eq_of_homotopy_map_eq 0 (fun d hd => hX d (by omega))
    (fun d hd => hY d (by omega)) f g hfg

end KIP126.StableHomotopy.Implementation
