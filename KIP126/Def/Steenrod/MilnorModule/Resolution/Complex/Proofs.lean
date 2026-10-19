module

public import KIP126.Def.Steenrod.MilnorModule.Resolution.Complex.Data
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

/-! Exactness of this actual augmented dual complex remains a proof
obligation. It is not deduced from an unrestricted categorical duality. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory

theorem dualCobarAugmentation_quasiIso (R : Ext.CobarResolution) :
    QuasiIso (dualCobarAugmentation R) := by
  exact (open CategoryTheory.Limits KIP126.Algebra KIP126.Core.Algebra
    KIP126.Algebra.GradedVectorSpace in by
    set_option backward.isDefEq.respectTransparency false in
      let E (n : ℤ) : GrVect F2 ⥤ ModuleCat F2 :=
        (discreteEquivalence F2).functor ⋙ (evaluation (Discrete ℤ) (ModuleCat F2)).obj ⟨n⟩
      letI (n : ℤ) : (E n).Additive := by constructor; intro X Y f g; rfl
      letI (n : ℤ) : PreservesFiniteLimits (E n) := by dsimp [E]; infer_instance
      letI (n : ℤ) : PreservesFiniteColimits (E n) := by dsimp [E]; infer_instance
      let F := Monad.forget (GradedModule.leftTensorMonad steenrod)
      let G := Comonad.forget (GradedComodule.rightTensorComonad Coalgebra.dualSteenrod)
      letI : PreservesFiniteColimits F := ⟨fun _ _ _ => inferInstance⟩
      letI : PreservesFiniteLimits G := ⟨fun _ _ _ => inferInstance⟩
      have graded_exact (S : ShortComplex (GrVect F2))
          (hS : ∀ n : ℤ, (S.map (E n)).Exact) : S.Exact := by
        rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
        funext n
        have hz := (ShortComplex.exact_iff_isZero_homology _).mp (hS n)
        have hh : IsZero ((E n).obj S.homology) :=
          ((S.mapHomologyIso (E n)).isZero_iff).mp hz
        exact hh.eq_of_src _ _
      have dual_zero {A B D : SourceComodule} (f : A ⟶ B) (g : B ⟶ D)
          (w : f ≫ g = 0) : dualLeftMap g ≫ dualLeftMap f = 0 := by
        apply Monad.Algebra.Hom.ext
        funext n
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        change Module.Dual F2 (D.A n) at φ
        apply LinearMap.ext
        intro x
        have hw := congrArg (fun k => (k.f n).hom x) w
        change φ ((g.f n).hom ((f.f n).hom x)) = 0
        change (g.f n).hom ((f.f n).hom x) = 0 at hw
        rw [hw, map_zero]
      have dual_exact {A B D : SourceComodule} (f : A ⟶ B) (g : B ⟶ D)
          (w : f ≫ g = 0) (h : (ShortComplex.mk f g w).Exact) :
          (ShortComplex.mk (dualLeftMap g) (dualLeftMap f) (dual_zero f g w)).Exact := by
        apply (ShortComplex.exact_map_iff_of_faithful _ F).mp
        apply graded_exact
        intro n
        have hn := (h.map G).map (E n)
        apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
        change LinearMap.range (g.f n).hom.dualMap = LinearMap.ker (f.f n).hom.dualMap
        rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
          LinearMap.ker_dualMap_eq_dualAnnihilator_range]
        exact congrArg Submodule.dualAnnihilator hn.moduleCat_range_eq_ker.symm
      have dual_epi {A B : SourceComodule} (f : A ⟶ B) [Mono f] : Epi (dualLeftMap f) := by
        apply F.epi_of_epi_map
        constructor
        intro Z u v huv
        funext n
        have hinj : Function.Injective (f.f n).hom := by
          haveI : Mono ((G ⋙ E n).map f) := inferInstance
          exact (ModuleCat.mono_iff_injective ((G ⋙ E n).map f)).mp inferInstance
        haveI : Epi ((F.map (dualLeftMap f)) n) :=
          (ModuleCat.epi_iff_surjective _).mpr
            (LinearMap.dualMap_surjective_of_injective hinj)
        exact (cancel_epi ((F.map (dualLeftMap f)) n)).mp (congrFun huv n)
      have hzero : (ShortComplex.mk (dualCobarDifferential R 1 0)
          (dualCobarAugmentationZero R) (dualCobarDifferential_augmentation R)).Exact := by
        let S := ShortComplex.mk (dualLeftMap (R.resolution.cocomplex.d 0 1))
          (dualLeftMap (R.resolution.ι.f 0))
          (dual_zero _ _ R.resolution.ι_f_zero_comp_complex_d)
        have hx : (ShortComplex.mk _ _ R.resolution.ι_f_zero_comp_complex_d).Exact :=
          ShortComplex.exact_of_f_is_kernel _ R.resolution.isLimitKernelFork
        have hs : S.Exact := dual_exact _ _ _ hx
        apply ShortComplex.exact_of_iso (S₁ := S) ?_ hs
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (trivialDualIso 0)
          (by simp [S, dualCobarDifferential]) (by simp [S, dualCobarAugmentationZero])
      haveI : Epi (dualCobarAugmentationZero R) := by
        haveI := dual_epi (R.resolution.ι.f 0)
        dsimp only [dualCobarAugmentationZero]
        infer_instance
      constructor
      intro n
      cases n with
      | zero =>
          rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
          · refine ⟨hzero, ?_⟩
            change Epi (dualCobarAugmentationZero R)
            infer_instance
          · exact (dualCobarComplex R).shape 0 0 (by simp)
          · rfl
          · rfl
      | succ n =>
          rw [quasiIsoAt_iff_exactAt' _ _
            (ChainComplex.exactAt_succ_single_obj _ _)]
          rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
          exact dual_exact _ _ _ (R.resolution.exact_succ n))

end KIP126.Steenrod.Milnor.Module
