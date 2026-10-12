module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Moore.Postnikov.Proofs
public import KIP126.Def.StableHomotopy.Implementation.HF2.Moore.Postnikov.Representation.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- The original Moore-heart unit detects every actual map into an upper-truncated target. -/
theorem sourceModTwoMooreHeartUnit_precomp_injective
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, 1 ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y)) :
    Function.Injective (fun a : sourceModTwoMooreHeart ⟶ Y => sourceModTwoMooreHeartUnit ≫ a) := by
  intro a b hab
  apply (sourcePostnikovUnit_precomp_bijective sourceModTwoMoore 1 Y hY).injective
  let f := moorePowerMap 2 (Prespectrum.sourceSphere 0) 1
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT := HasFunctorialCofiber.cofib_distinguished f
  have hshift : Subsingleton ((Prespectrum.sourceSphere 0)⟦(1 : ℤ)⟧ ⟶ Y) := by
    letI := hY 1 (by omega)
    let e : ((Prespectrum.sourceSphere 0)⟦(1 : ℤ)⟧ ⟶ Y) ≃
        ((sourceStableHomotopyAddFunctor 1).obj Y) :=
      (Iso.homCongr (Prespectrum.sourceSphere_addShiftIso 0 1) (Iso.refl Y)).trans
        (Prespectrum.sourceStableHomotopyEquiv Y.as.obj 1).symm
    exact e.injective.subsingleton
  apply sub_eq_zero.mp
  obtain ⟨z,hz⟩ := T.yoneda_exact₃ hT
    (sourcePostnikovUnit sourceModTwoMoore 1 ≫ a - sourcePostnikovUnit sourceModTwoMoore 1 ≫ b) (by
      change sourceModTwoMooreInclusion ≫ (_ - _) = 0
      rw [Preadditive.comp_sub,← Category.assoc,← Category.assoc]
      exact sub_eq_zero.mpr hab)
  rw [hshift.elim z 0,comp_zero] at hz
  exact hz

/-- The image of the actual Moore-heart unit consists exactly of the
original sphere classes killed by two. -/
theorem sourceModTwoMooreHeartUnit_exists_lift_iff
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, 1 ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (a : Prespectrum.sourceSphere 0 ⟶ Y) :
    (∃ b : sourceModTwoMooreHeart ⟶ Y, sourceModTwoMooreHeartUnit ≫ b = a) ↔ 2 • a = 0 := by
  let f := moorePowerMap 2 (Prespectrum.sourceSphere 0) 1
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT := HasFunctorialCofiber.cofib_distinguished f
  constructor
  · rintro ⟨b,rfl⟩
    have hz := comp_distTriang_mor_zero₁₂ T hT
    have hz' := congrArg (fun k => k ≫ sourcePostnikovUnit sourceModTwoMoore 1 ≫ b) hz
    change (f ≫ HasFunctorialCofiber.cofibι f) ≫ sourcePostnikovUnit sourceModTwoMoore 1 ≫ b = 0 ≫ _ at hz'
    simpa only [f,moorePowerMap,pow_one,sourceModTwoMooreHeartUnit,
      sourceModTwoMooreInclusion,Preadditive.nsmul_comp,Category.id_comp,
      Category.assoc,zero_comp] using hz'
  · intro ha
    have hz : f ≫ a = 0 := by
      simpa only [f,moorePowerMap,pow_one,Preadditive.nsmul_comp,Category.id_comp] using ha
    obtain ⟨b,hb⟩ := T.yoneda_exact₂ hT a hz
    obtain ⟨c,hc⟩ := (sourcePostnikovUnit_precomp_bijective sourceModTwoMoore 1 Y hY).surjective b
    refine ⟨c,?_⟩
    exact (Category.assoc sourceModTwoMooreInclusion (sourcePostnikovUnit sourceModTwoMoore 1) c).trans
      ((congrArg (fun k : sourceModTwoMoore ⟶ Y => sourceModTwoMooreInclusion ≫ k) hc).trans hb.symm)

/-- The original sphere unit of the actual Moore heart is killed by two. -/
theorem sourceModTwoMooreHeartUnit_two_nsmul : 2 • sourceModTwoMooreHeartUnit = 0 :=
  (sourceModTwoMooreHeartUnit_exists_lift_iff sourceModTwoMooreHeart
    (fun d hd => sourceModTwoMooreHeart_homotopy_subsingleton d (by omega))
    sourceModTwoMooreHeartUnit).mp ⟨𝟙 _,Category.comp_id _⟩

/-- The actual Moore heart itself has characteristic two, independently
of identifying its original degree-zero group with the coefficient field. -/
theorem sourceModTwoMooreHeart_two_id : 2 • 𝟙 sourceModTwoMooreHeart = 0 := by
  apply sourceModTwoMooreHeartUnit_precomp_injective sourceModTwoMooreHeart
    (fun d hd => sourceModTwoMooreHeart_homotopy_subsingleton d (by omega))
  change sourceModTwoMooreHeartUnit ≫ (2 • 𝟙 _) = sourceModTwoMooreHeartUnit ≫ 0
  rw [Preadditive.comp_nsmul,Category.comp_id,sourceModTwoMooreHeartUnit_two_nsmul,comp_zero]

/-- The actual additive evaluation detects maps into every upper-truncated target. -/
theorem sourceModTwoMooreHeartEvaluation_injective
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, 1 ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y)) :
    Function.Injective (sourceModTwoMooreHeartEvaluation Y) := by
  intro a b hab
  apply sourceModTwoMooreHeartUnit_precomp_injective Y hY
  exact (Prespectrum.sourceStableHomotopyAddEquiv Y.as.obj 0).symm.injective hab

/-- A stable class is represented by an actual map from the Moore heart
exactly when it is killed by two. -/
theorem sourceModTwoMooreHeartEvaluation_exists_lift_iff
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, 1 ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (y : (sourceStableHomotopyAddFunctor 0).obj Y) :
    (∃ b : sourceModTwoMooreHeart ⟶ Y, sourceModTwoMooreHeartEvaluation Y b = y) ↔ 2 • y = 0 := by
  let e := Prespectrum.sourceStableHomotopyAddEquiv Y.as.obj 0
  have h : (∃ b : sourceModTwoMooreHeart ⟶ Y, sourceModTwoMooreHeartEvaluation Y b = y) ↔
      (∃ b : sourceModTwoMooreHeart ⟶ Y, sourceModTwoMooreHeartUnit ≫ b = e y) := by
    constructor
    · rintro ⟨b,hb⟩
      refine ⟨b,?_⟩
      apply e.symm.injective
      exact hb.trans (e.symm_apply_apply y).symm
    · rintro ⟨b,hb⟩
      refine ⟨b,?_⟩
      change e.symm (sourceModTwoMooreHeartUnit ≫ b) = y
      rw [hb,e.symm_apply_apply]
  rw [h,sourceModTwoMooreHeartUnit_exists_lift_iff Y hY]
  have he₂ : e (2 • y) = 2 • e y := by
    simpa only [two_nsmul] using e.map_add y y
  constructor
  · intro hy
    apply e.injective
    exact he₂.trans (hy.trans e.map_zero.symm)
  · intro hy
    exact he₂.symm.trans ((congrArg e hy).trans e.map_zero)

/-- Every original stable class of an exponent-two upper-truncated target
has a unique actual Moore-heart representative. -/
theorem sourceModTwoMooreHeartEvaluation_bijective
    (Y : SourceCategory.{0})
    (hY : ∀ d : ℤ, 1 ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (h₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0) :
    Function.Bijective (sourceModTwoMooreHeartEvaluation Y) :=
  ⟨sourceModTwoMooreHeartEvaluation_injective Y hY,
    fun y => (sourceModTwoMooreHeartEvaluation_exists_lift_iff Y hY y).mpr (h₂ y)⟩

/-- Evaluation retains the original sphere generator and both original
stable-group maps, rather than a replacement group presentation. -/
theorem sourceModTwoMooreHeartEvaluation_apply (Y : SourceCategory.{0})
    (a : sourceModTwoMooreHeart ⟶ Y) :
    sourceModTwoMooreHeartEvaluation Y a =
      (sourceStableHomotopyAddFunctor 0).map a
        ((sourceStableHomotopyAddFunctor 0).map sourceModTwoMooreHeartUnit
          (Prespectrum.sourceSphereGenerator 0)) := by
  let F := sourceStableHomotopyAddFunctor 0
  change (Prespectrum.sourceStableHomotopyEquiv Y.as.obj 0).symm
    (sourceModTwoMooreHeartUnit ≫ a) =
      (F.map sourceModTwoMooreHeartUnit ≫ F.map a) (Prespectrum.sourceSphereGenerator 0)
  rw [← F.map_comp]
  change (Prespectrum.sourceStableHomotopyEquiv Y.as.obj 0).symm
    (sourceModTwoMooreHeartUnit ≫ a) =
      (forget AddCommGrpCat).map ((sourceStableHomotopyAddFunctor 0).map
        (sourceModTwoMooreHeartUnit ≫ a)) (Prespectrum.sourceSphereGenerator 0)
  rw [sourceStableHomotopyAddFunctor_forget_map]
  exact Prespectrum.sourceStableHomotopyEquiv_symm_apply Y.as.obj 0 _

end KIP126.StableHomotopy.Implementation

