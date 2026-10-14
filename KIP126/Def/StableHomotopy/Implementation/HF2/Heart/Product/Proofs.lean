module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Moore.Postnikov.Fullness.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Product.Vanishing.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Scalar.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Milnor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Homotopy.Proofs
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- An actual exponent-two heart is an actual retract of a product of the
fixed HF2 object, conditional on the original Moore-heart comparison. All
linear functionals are realized by stable maps; extending an inverse from
the image of their joint evaluation supplies the actual retraction. -/
theorem source_exponent_two_heart_exists_HF2_product_retract
    [IsIso sourceModTwoMooreHeartToHF2]
    (X : SourceCategory.{0})
    (hX : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hX₂ : ∀ x : (sourceStableHomotopyAddFunctor 0).obj X, 2 • x = 0) :
    ∃ (J : Type) (i : X ⟶ ∏ᶜ fun _ : J => sourceLocalization.obj sourceHF2.spectrum)
      (r : (∏ᶜ fun _ : J => sourceLocalization.obj sourceHF2.spectrum) ⟶ X), i ≫ r = 𝟙 X := by
  let F := sourceStableHomotopyAddFunctor 0
  let H := sourceLocalization.obj sourceHF2.spectrum
  letI : Module (ZMod 2) (F.obj X) := AddCommGroup.zmodModule hX₂
  let J := Module.Dual (ZMod 2) (F.obj X)
  have hH : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj H) :=
    fun d hd => sourceHF2.vanishes d hd
  have hH₂ : ∀ y : F.obj H, 2 • y = 0 := by
    intro y
    have h := congrArg (fun f : H ⟶ H => F.map f y) sourceHF2_two_id
    rw [Functor.map_nsmul,CategoryTheory.Functor.map_id,Functor.map_zero] at h
    exact h
  let α (φ : J) : F.obj X ⟶ F.obj H :=
    AddCommGrpCat.ofHom (sourceHF2PiZeroAddEquiv.symm.toAddMonoidHom.comp φ.toAddMonoidHom)
  have hex (φ : J) : ∃ a : X ⟶ H, F.map a = α φ :=
    source_homotopy_map_surjective_of_exponent_two_heart X H hX
      (fun d hd => hH d (by omega)) hX₂ hH₂ (α φ)
  choose a ha using hex
  let Z := ∏ᶜ fun _ : J => H
  let i : X ⟶ Z := Pi.lift a
  have hi : Function.Injective (F.map i) := by
    intro x y hxy
    apply Module.eval_apply_injective (ZMod 2)
    ext φ
    have hφ := congrArg (fun z => F.map (Pi.π (fun _ : J => H) φ) z) hxy
    change (F.map i ≫ F.map (Pi.π (fun _ : J => H) φ)) x =
      (F.map i ≫ F.map (Pi.π (fun _ : J => H) φ)) y at hφ
    rw [← F.map_comp,Pi.lift_π,ha] at hφ
    exact sourceHF2PiZeroAddEquiv.symm.injective hφ
  have hZ : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Z) :=
    fun d hd => sourceProduct_homotopy_subsingleton (fun _ : J => H) d (fun _ => hH d hd)
  have hZ₂ : ∀ z : F.obj Z, 2 • z = 0 := by
    intro z
    have h := congrArg (fun f : Z ⟶ Z => F.map f z)
      (sourceProduct_nsmul_id_eq_zero (fun _ : J => H) 2 (fun _ => sourceHF2_two_id))
    rw [Functor.map_nsmul,CategoryTheory.Functor.map_id,Functor.map_zero] at h
    exact h
  letI : Module (ZMod 2) (F.obj Z) := AddCommGroup.zmodModule hZ₂
  let l : F.obj X →ₗ[ZMod 2] F.obj Z := AddMonoidHom.toZModLinearMap 2 (F.map i).hom
  obtain ⟨s,hs⟩ := l.exists_leftInverse_of_injective (LinearMap.ker_eq_bot_of_injective hi)
  obtain ⟨r,hr⟩ := source_homotopy_map_surjective_of_exponent_two_heart Z X hZ
    (fun d hd => hX d (by omega)) hZ₂ hX₂ (AddCommGrpCat.ofHom s.toAddMonoidHom)
  change F.map r = AddCommGrpCat.ofHom s.toAddMonoidHom at hr
  refine ⟨J,i,r,?_⟩
  apply source_hom_eq_of_homotopy_map_eq 0
    (fun d hd => hX d (by omega)) (fun d hd => hX d (by omega))
  change F.map (i ≫ r) = F.map (𝟙 X)
  rw [F.map_comp,hr,CategoryTheory.Functor.map_id]
  apply AddCommGrpCat.ext
  intro x
  exact congrArg (fun f : F.obj X →ₗ[ZMod 2] F.obj X => f x) hs

/-- Under the original Moore-heart comparison, every actual exponent-two
heart is HF2-local by its constructed retract into an actual product. -/
theorem sourceIsHF2Local_of_exponent_two_heart
    [IsIso sourceModTwoMooreHeartToHF2]
    (X : SourceCategory.{0})
    (hX : ∀ d : ℤ, d ≠ 0 → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hX₂ : ∀ x : (sourceStableHomotopyAddFunctor 0).obj X, 2 • x = 0) :
    SourceIsHF2Local X := by
  obtain ⟨J,i,r,hir⟩ := source_exponent_two_heart_exists_HF2_product_retract X hX hX₂
  have hP : SourceIsHF2Local (∏ᶜ fun _ : J => sourceLocalization.obj sourceHF2.spectrum) :=
    SourceIsHF2Local.product _ (fun _ => @sourceHF2_isLocal)
  exact @SourceIsHF2Local.of_retract _ _ i r hir @hP

end KIP126.StableHomotopy.Implementation
