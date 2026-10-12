module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Heart.Product.Proofs
public import KIP126.Def.Algebra.Module.Basis.Coproduct.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- The identity of an actual arbitrary coproduct of the fixed coefficient
object is killed by two. -/
theorem sourceHF2Coproduct_two_id (J : Type) :
    2 • 𝟙 (∐ fun _ : J => sourceLocalization.obj sourceHF2.spectrum) = 0 := by
  apply Sigma.hom_ext
  intro j
  rw [Preadditive.comp_nsmul,Category.comp_id,comp_zero]
  have h := congrArg (fun f => f ≫
    Sigma.ι (fun _ : J => sourceLocalization.obj sourceHF2.spectrum) j) sourceHF2_two_id
  simpa only [Preadditive.nsmul_comp,Category.id_comp,zero_comp] using h

/-- An additive isomorphism of original groups lifts to an actual stable
isomorphism between exponent-two hearts under the specified comparison. -/
theorem source_exponent_two_heart_exists_iso_of_homotopy_iso
    [IsIso sourceModTwoMooreHeartToHF2]
    (X Y : SourceCategory.{0})
    (hX : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hY : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (hX₂ : ∀ x : (sourceStableHomotopyAddFunctor 0).obj X, 2 • x = 0)
    (hY₂ : ∀ y : (sourceStableHomotopyAddFunctor 0).obj Y, 2 • y = 0)
    (e : (sourceStableHomotopyAddFunctor 0).obj X ≅ (sourceStableHomotopyAddFunctor 0).obj Y) :
    ∃ e' : X ≅ Y, (sourceStableHomotopyAddFunctor 0).map e'.hom = e.hom := by
  let F := sourceStableHomotopyAddFunctor 0
  obtain ⟨f,hf⟩ := source_homotopy_map_surjective_of_exponent_two_heart X Y hX
    (fun d hd => hY d (by omega)) hX₂ hY₂ e.hom
  obtain ⟨g,hg⟩ := source_homotopy_map_surjective_of_exponent_two_heart Y X hY
    (fun d hd => hX d (by omega)) hY₂ hX₂ e.inv
  change F.map f = e.hom at hf
  change F.map g = e.inv at hg
  have hfg : f ≫ g = 𝟙 X := by
    apply source_hom_eq_of_homotopy_map_eq 0
      (fun d hd => hX d (by omega)) (fun d hd => hX d (by omega))
    change F.map (f ≫ g) = F.map (𝟙 X)
    rw [F.map_comp,hf,hg,e.hom_inv_id,CategoryTheory.Functor.map_id]
  have hgf : g ≫ f = 𝟙 Y := by
    apply source_hom_eq_of_homotopy_map_eq 0
      (fun d hd => hY d (by omega)) (fun d hd => hY d (by omega))
    change F.map (g ≫ f) = F.map (𝟙 Y)
    rw [F.map_comp,hf,hg,e.inv_hom_id,CategoryTheory.Functor.map_id]
  exact ⟨⟨f,g,hfg,hgf⟩,hf⟩

/-- A basis of an exponent-two original stable group gives an actual
coproduct model by the fixed HF2 spectrum. The categorical group coproduct
is identified using the original basis cofan, then actual heart fullness
and faithfulness lift that identification. -/
theorem source_exponent_two_heart_exists_HF2_coproduct_iso
    [IsIso sourceModTwoMooreHeartToHF2]
    (X : SourceCategory.{0})
    (hX : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hX₂ : ∀ x : (sourceStableHomotopyAddFunctor 0).obj X, 2 • x = 0) :
    ∃ J : Type, Nonempty ((∐ fun _ : J => sourceLocalization.obj sourceHF2.spectrum) ≅ X) := by
  let F := sourceStableHomotopyAddFunctor 0
  letI : Module (ZMod 2) (F.obj X) := AddCommGroup.zmodModule hX₂
  let J := Module.Free.ChooseBasisIndex (ZMod 2) (F.obj X)
  let b : Module.Basis J (ZMod 2) (F.obj X) := Module.Free.chooseBasis (ZMod 2) (F.obj X)
  let H := sourceLocalization.obj sourceHF2.spectrum
  let A (_ : J) := H
  let B := KIP126.Foundation.basisAdditiveCofan b
  let e : F.obj H ≅ AddCommGrpCat.of (ZMod 2) := sourceHF2PiZeroAddEquiv.toAddCommGrpIso
  let α : Discrete.functor (fun _ : J => F.obj H) ≅
      Discrete.functor (fun _ : J => AddCommGrpCat.of (ZMod 2)) :=
    Discrete.natIso (fun _ => e)
  let C := (Cocone.precompose α.hom).obj B
  have hC : IsColimit C :=
    (IsColimit.precomposeHomEquiv α B).symm (KIP126.Foundation.basisAdditiveCofan_isColimit b)
  let D : Cofan (fun j : J => F.obj (A j)) :=
    Cofan.mk (F.obj (∐ A)) (fun j => F.map (Sigma.ι A j))
  have hD : IsColimit D := isColimitOfHasCoproductOfPreservesColimit F A
  let g : F.obj (∐ A) ≅ F.obj X := hD.coconePointUniqueUpToIso hC
  have hA : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj (∐ A)) :=
    fun d hd => sourceCoproduct_homotopy_subsingleton A d (fun _ => sourceHF2.vanishes d hd)
  have hA₂ : ∀ x : F.obj (∐ A), 2 • x = 0 := by
    intro x
    have h := congrArg (fun f : (∐ A) ⟶ (∐ A) => F.map f x) (sourceHF2Coproduct_two_id J)
    rw [Functor.map_nsmul,CategoryTheory.Functor.map_id,Functor.map_zero] at h
    exact h
  obtain ⟨e',_⟩ := source_exponent_two_heart_exists_iso_of_homotopy_iso (∐ A) X hA hX hA₂ hX₂ g
  exact ⟨J,⟨e'⟩⟩

/-- Every actual HF2 coproduct is an actual retract of an actual HF2
product under the specified comparison. No finiteness of the coproduct
index is assumed. -/
theorem sourceHF2Coproduct_exists_product_retract
    [IsIso sourceModTwoMooreHeartToHF2] (J : Type) :
    ∃ (K : Type)
      (i : (∐ fun _ : J => sourceLocalization.obj sourceHF2.spectrum) ⟶
        ∏ᶜ fun _ : K => sourceLocalization.obj sourceHF2.spectrum)
      (r : (∏ᶜ fun _ : K => sourceLocalization.obj sourceHF2.spectrum) ⟶
        ∐ fun _ : J => sourceLocalization.obj sourceHF2.spectrum), i ≫ r = 𝟙 _ := by
  let A (_ : J) := sourceLocalization.obj sourceHF2.spectrum
  apply source_exponent_two_heart_exists_HF2_product_retract (∐ A)
    (fun d hd => sourceCoproduct_homotopy_subsingleton A d (fun _ => sourceHF2.vanishes d hd))
  intro x
  have h := congrArg (fun f : (∐ A) ⟶ (∐ A) => (sourceStableHomotopyAddFunctor 0).map f x)
    (sourceHF2Coproduct_two_id J)
  rw [Functor.map_nsmul,CategoryTheory.Functor.map_id,Functor.map_zero] at h
  exact h

end KIP126.StableHomotopy.Implementation
