module

public import KIP126.Def.Comparison.ClassicalSynthetic.RealizationWeights.Data
public import KIP126.Def.Synthetic.Localization.Proofs

@[expose] public section

/-! Weight comparisons for the SAME lambda-inversion realization.
Their zero value and every successive weight map are fixed, so this is
not a family of unrelated isomorphisms of objects of the same dimension.
The coefficient comparison is the already specified nu-recovery map.
-/
namespace KIP126.Comparison.ClassicalSynthetic
open CategoryTheory CategoryTheory.Functor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  (N : NuFunctorData C Syn) (L : LambdaRecovery N)

/-- Lambda inversion and the zero normalization determine every weight.
This uniqueness is a model comparison property, independent of Adams
labels, of the Lin output, and of any high-stem theorem. -/
theorem RealizationWeightComparison.unique
    (A B : RealizationWeightComparison N L) : A = B := by
  have he (X : C) (a : ℤ) : A.iso X a = B.iso X a := by
    have hi (a : ℤ) : IsIso (L.realization.map (weightLambdaArrow N X a)) := by
      have h : L.realization.map (weightLambdaArrow N X a) =
          (A.iso X (a-1)).hom ≫ (A.iso X a).inv := by
        rw [← A.lambda X a, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [h]
      infer_instance
    induction a using Int.induction_on with
    | zero => exact Iso.ext ((A.zero X).trans (B.zero X).symm)
    | succ n ih =>
      apply Iso.ext
      letI := hi (n+1)
      apply (cancel_epi (L.realization.map (weightLambdaArrow N X (n+1)))).mp
      rw [A.lambda, B.lambda]
      have hn : (n : ℤ) + 1 - 1 = n := by omega
      rw [hn]
      exact congrArg Iso.hom ih
    | pred n ih =>
      apply Iso.ext
      rw [← A.lambda, ← B.lambda, ih]
  cases A with
  | mk a az al an =>
    cases B with
    | mk b bz bl bn =>
      have h : a = b := funext fun X => funext fun n => he X n
      cases h
      rfl

/-- Existence follows from inversion of the actual lambda maps and the
specified recovery at weight zero. It requires coherent index transports. -/
theorem realizationWeightComparison_exists (coherent : BiShiftCoherence Syn) :
    Nonempty (RealizationWeightComparison N L) := by
  set_option backward.isDefEq.respectTransparency false in
    have hi (X : C) (a : ℤ) : IsIso (L.realization.map (weightLambdaArrow N X a)) := by
      letI := L.localization.map_lambda_isIso (weightObject N X a)
      change IsIso (L.equivalence.functor.map (L.localization.reflector.map _))
      unfold weightLambdaArrow
      simp only [Functor.map_comp]
      infer_instance
    have hn {X Y : C} (f : X ⟶ Y) (a : ℤ) :
        (SyntheticCategory.biShift (0,a-1)).map (N.functor.map f) ≫ weightLambdaArrow N Y a =
          weightLambdaArrow N X a ≫ (SyntheticCategory.biShift (0,a)).map (N.functor.map f) := by
      unfold weightLambdaArrow
      have h (a b : ℤ) (hab : (0,a)+(0,-1)=(0,b)) :
          (SyntheticCategory.biShift (0,b)).map (N.functor.map f) ≫
            eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj (N.functor.obj Y)) hab.symm) =
          eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj (N.functor.obj X)) hab.symm) ≫
            (SyntheticCategory.biShift ((0,a)+(0,-1))).map (N.functor.map f) := by
        cases hab
        simp
      simp only [Category.assoc]
      rw [← Category.assoc _ (eqToHom _) _, h a (a-1) (by ext <;> simp [sub_eq_add_neg])]
      simp only [Category.assoc]
      rw [NatTrans.naturality_assoc]
      change _ ≫ _ ≫ (SyntheticCategory.biShift (0,-1)).map
        ((SyntheticCategory.biShift (0,a)).map (N.functor.map f)) ≫ _ = _
      erw [SyntheticCategory.lam.naturality]
      rfl
    let F (a : ℤ) : C ⥤ C := (N.functor ⋙ SyntheticCategory.biShift (0,a)) ⋙ L.realization
    let τ (a : ℤ) : F (a-1) ⟶ F a :=
      { app := fun X => L.realization.map (weightLambdaArrow N X a)
        naturality := fun X Y f => by
          change L.realization.map _ ≫ L.realization.map _ = L.realization.map _ ≫ L.realization.map _
          rw [← L.realization.map_comp, ← L.realization.map_comp]
          exact congrArg L.realization.map (hn f a) }
    letI (a : ℤ) : IsIso (τ a) := by
      haveI (X : C) : IsIso ((τ a).app X) := hi X a
      exact NatIso.isIso_of_isIso_app (τ a)
    let e (a : ℤ) : F (a-1) ≅ F a := asIso (τ a)
    let z : F 0 ≅ 𝟭 C :=
      isoWhiskerRight (isoWhiskerLeft N.functor SyntheticCategory.biShift_zero ≪≫
        Functor.rightUnitor N.functor) L.realization ≪≫ L.nuRealizationIso
    let succ (a : ℤ) (_ : 0 ≤ a) (q : F a ≅ 𝟭 C) : F (a+1) ≅ 𝟭 C :=
      (e (a+1)).symm ≪≫ eqToIso (congrArg F (by omega : a+1-1=a)) ≪≫ q
    let pred (a : ℤ) (_ : a ≤ 0) (q : F a ≅ 𝟭 C) : F (a-1) ≅ 𝟭 C := e a ≪≫ q
    let q (a : ℤ) : F a ≅ 𝟭 C := a.inductionOn' 0 z succ pred
    have hq0 : q 0 = z := Int.inductionOn'_self
    have hq (a : ℤ) : τ a ≫ (q a).hom = (q (a-1)).hom := by
      by_cases ha : a ≤ 0
      · have h := Int.inductionOn'_sub_one (z := a) (zero := z) (succ := succ) (pred := pred) ha
        change q (a-1) = e a ≪≫ q a at h
        rw [h]
        rfl
      · have h := Int.inductionOn'_add_one (z := a-1) (zero := z) (succ := succ) (pred := pred) (by omega : 0 ≤ a-1)
        have hs : a-1+1=a := by omega
        change q (a-1+1) = (e (a-1+1)).symm ≪≫ eqToIso (congrArg F (by omega : a-1+1-1=a-1)) ≪≫ q (a-1) at h
        have hn (b : ℤ) (hb : b=a) (hd : b-1=a-1)
            (h : q b = (e b).symm ≪≫ eqToIso (congrArg F hd) ≪≫ q (a-1)) :
            q a = (e a).symm ≪≫ q (a-1) := by
          subst b
          simpa only [eqToIso_refl, Iso.refl_trans] using h
        rw [hn _ hs (by omega) h]
        simp [e]
    refine ⟨{ iso := fun X a => (q a).app X, zero := ?_, lambda := ?_, naturality := ?_ }⟩
    · intro X
      rw [hq0]
      simp [z]
      erw [L.realization.map_id]
      erw [Category.id_comp]
    · intro X a
      exact congrArg (fun t => t.app X) (hq a)
    · intro X Y f a
      exact (q a).hom.naturality f

end
end KIP126.Comparison.ClassicalSynthetic
