module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Orthogonality.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Connectivity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- The cofiber of the actual degree-n sphere cover is one degree more
connected than its n-connective target. -/
theorem sourceSphereCover_cofiber_homotopy_subsingleton (X : SourceCategory.{0}) (n d : ℤ)
    (hX : ∀ k, k < n → Subsingleton ((sourceStableHomotopyAddFunctor k).obj X))
    (hd : d < n + 1) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj
      (HasFunctorialCofiber.cofib (sourceSphereCoverMap X n))) := by
  let F := sourceStableHomotopyAddFunctor d
  let A := sourceSphereCover X n
  let f := sourceSphereCoverMap X n
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT : T ∈ distTriang SourceCategory := HasFunctorialCofiber.cofib_distinguished f
  letI := sourceSphereCover_homotopy_subsingleton X n (d - 1) (by omega)
  letI : Subsingleton (Prespectrum.sourceSphere d ⟶
      sourceLocalization.obj (A⟦(1 : ℤ)⟧).as.obj) := by
    change Subsingleton (Prespectrum.sourceSphere d ⟶ A⟦(1 : ℤ)⟧)
    exact sourceSphere_hom_shift_subsingleton A d
  letI : Subsingleton (F.obj (A⟦(1 : ℤ)⟧)) :=
    (Prespectrum.sourceStableHomotopyEquiv (A⟦(1 : ℤ)⟧).as.obj d).injective.subsingleton
  have hz₃ : F.map T.mor₃ = 0 :=
    (AddCommGrpCat.isZero_of_subsingleton (F.obj (A⟦(1 : ℤ)⟧))).eq_of_tgt _ _
  haveI : Epi (F.map T.mor₂) :=
    (F.map_distinguished_exact T.rotate (rot_of_distTriang T hT)).epi_f hz₃
  have hsurj := (AddCommGrpCat.epi_iff_surjective (F.map T.mor₂)).mp inferInstance
  have hcover : Function.Surjective (F.map f) := by
    by_cases heq : d = n
    · subst d
      exact sourceSphereCoverMap_surjective X n
    · letI := hX d (by omega)
      exact fun x => ⟨0, Subsingleton.elim _ _⟩
  have hz₂ : F.map T.mor₂ = 0 := by
    apply AddCommGrpCat.ext
    intro x
    obtain ⟨a, rfl⟩ := hcover x
    change (F.map T.mor₁ ≫ F.map T.mor₂) a = 0
    rw [← F.map_comp, comp_distTriang_mor_zero₁₂ T hT, F.map_zero]
    rfl
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  rw [hz₂]
  rfl

private theorem sphere_cover_comp_eq_of_homotopy_map_eq {X Y : SourceCategory.{0}}
    (n : ℤ) (f g : X ⟶ Y)
    (hfg : (sourceStableHomotopyAddFunctor n).map f =
      (sourceStableHomotopyAddFunctor n).map g) :
    sourceSphereCoverMap X n ≫ f = sourceSphereCoverMap X n ≫ g := by
  apply Sigma.hom_ext
  intro x
  simp only [sourceSphereCoverMap, Sigma.ι_desc_assoc]
  have hx := congrArg (fun a : (sourceStableHomotopyAddFunctor n).obj X ⟶
      (sourceStableHomotopyAddFunctor n).obj Y => a x) hfg
  have hf := Prespectrum.sourceStableHomotopyEquiv_natural f n x
  have hg := Prespectrum.sourceStableHomotopyEquiv_natural g n x
  change (forget AddCommGrpCat).map ((sourceStableHomotopyAddFunctor n).map f) x =
    (forget AddCommGrpCat).map ((sourceStableHomotopyAddFunctor n).map g) x at hx
  rw [sourceStableHomotopyAddFunctor_forget_map,
    sourceStableHomotopyAddFunctor_forget_map] at hx
  exact hf.symm.trans ((congrArg (Prespectrum.sourceStableHomotopyEquiv Y.as.obj n) hx).trans hg)

/-- Maps from an n-connective actual spectrum to an n-truncated one are
detected by their induced map on the original degree-n stable group. -/
theorem source_hom_eq_of_homotopy_map_eq {X Y : SourceCategory.{0}} (n : ℤ)
    (hX : ∀ d, d < n → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hY : ∀ d, n < d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y))
    (f g : X ⟶ Y)
    (hfg : (sourceStableHomotopyAddFunctor n).map f =
      (sourceStableHomotopyAddFunctor n).map g) : f = g := by
  let a := sourceSphereCoverMap X n
  let T := Triangle.mk a (HasFunctorialCofiber.cofibι a) (HasFunctorialCofiber.cofibδ a)
  have hT : T ∈ distTriang SourceCategory := HasFunctorialCofiber.cofib_distinguished a
  have hC : Subsingleton (T.obj₃ ⟶ Y) :=
    source_hom_subsingleton_of_degree_bounds T.obj₃ Y (n + 1)
      (fun d hd => sourceSphereCover_cofiber_homotopy_subsingleton X n d hX hd)
      (fun d hd => hY d (by omega))
  apply sub_eq_zero.mp
  obtain ⟨b, hb⟩ := T.yoneda_exact₂ hT (f - g) (by
    change a ≫ (f - g) = 0
    rw [Preadditive.comp_sub, sphere_cover_comp_eq_of_homotopy_map_eq n f g hfg, sub_self])
  rw [hC.elim b 0, comp_zero] at hb
  exact hb

/-- On an actual spectrum concentrated in degree n, scalar annihilation
of that stable group implies scalar annihilation of the identity map. -/
theorem source_nsmul_id_eq_zero_of_homotopy_nsmul_eq_zero (X : SourceCategory.{0})
    (n : ℤ) (p : ℕ)
    (hX : ∀ d, d ≠ n → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (hp : ∀ x : (sourceStableHomotopyAddFunctor n).obj X, p • x = 0) :
    p • 𝟙 X = 0 := by
  apply source_hom_eq_of_homotopy_map_eq n
    (fun d hd => hX d (by omega)) (fun d hd => hX d (by omega))
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  apply AddCommGrpCat.ext
  intro x
  exact hp x

end KIP126.StableHomotopy.Implementation
