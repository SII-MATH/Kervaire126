import KIP126.Def.Algebra.GradedComodule.Shift.TensorLine.Raw.Data

/-! Inverse and coaction identities for the prescribed degree-line maps. -/

namespace KIP126.Algebra.GradedComodule.TensorLine

open CategoryTheory MonoidalCategory GradedVectorSpace
open scoped TensorProduct

universe u

variable (K : Type u) [Field K]

/-- The prescribed splitting is inverse to multiplication on the tensor lines. -/
theorem hom_inv_id (t u : ℤ) :
    hom K t u ≫ inv K t u = 𝟙 (degreeLine K t ⊗ degreeLine K u) := by
  classical
  let e : degreeLine K t t ⊗ degreeLine K u u ≅ degreeLine K (t + u) (t + u) :=
    tensorIso (GradedObject.singleObjApplyIso t (ModuleCat.of K K))
      (GradedObject.singleObjApplyIso u (ModuleCat.of K K)) ≪≫
      (TensorProduct.lid K K).toModuleIso ≪≫
      (GradedObject.singleObjApplyIso (t + u) (ModuleCat.of K K)).symm
  funext n
  change hom K t u n ≫ inv K t u n = 𝟙 _
  apply GradedObject.Monoidal.tensorObj_ext
  intro i j hij
  by_cases hi : i = t
  · subst i
    by_cases hj : j = u
    · subst j
      subst n
      simp only [hom, inv, dite_true, GradedVectorSpace.tensorInclusion,
        GradedObject.Monoidal.ι_tensorObjDesc_assoc, Category.assoc]
      change e.hom ≫ e.inv ≫
        GradedObject.Monoidal.ιTensorObj (degreeLine K t) (degreeLine K u) t u (t + u) rfl = _
      exact (e.hom_inv_id_assoc _).trans (Category.comp_id _).symm
    · exact ((GradedObject.isInitialSingleObjApply u (ModuleCat.of K K) j hj).isInitialObj
        (tensorLeft (degreeLine K t t))).hom_ext _ _
  · exact ((GradedObject.isInitialSingleObjApply t (ModuleCat.of K K) i hi).isInitialObj
      (tensorRight (degreeLine K u j))).hom_ext _ _

/-- Multiplying the prescribed splitting returns the original degree line. -/
theorem inv_hom_id (t u : ℤ) :
    inv K t u ≫ hom K t u = 𝟙 (degreeLine K (t + u)) := by
  classical
  let e : degreeLine K t t ⊗ degreeLine K u u ≅ degreeLine K (t + u) (t + u) :=
    tensorIso (GradedObject.singleObjApplyIso t (ModuleCat.of K K))
      (GradedObject.singleObjApplyIso u (ModuleCat.of K K)) ≪≫
      (TensorProduct.lid K K).toModuleIso ≪≫
      (GradedObject.singleObjApplyIso (t + u) (ModuleCat.of K K)).symm
  funext n
  change inv K t u n ≫ hom K t u n = 𝟙 _
  by_cases hn : n = t + u
  · subst n
    simp only [hom, inv, dite_true, GradedVectorSpace.tensorInclusion, Category.assoc]
    erw [GradedObject.Monoidal.ι_tensorObjDesc]
    simp only [dite_true]
    change e.inv ≫ e.hom = _
    exact e.inv_hom_id
  · exact (GradedObject.isInitialSingleObjApply (t + u) (ModuleCat.of K K) n hn).hom_ext _ _

/-- On the nonzero summand the forward map is the actual scalar product. -/
theorem hom_tensor (t u : ℤ) (a b : K) :
    (hom K t u (t + u)).hom
        ((tensorInclusion K (degreeLine K t) (degreeLine K u) t u (t + u) rfl).hom
          ((GradedObject.singleObjApplyIso t (ModuleCat.of K K)).inv.hom a ⊗ₜ[K]
            (GradedObject.singleObjApplyIso u (ModuleCat.of K K)).inv.hom b)) =
      (GradedObject.singleObjApplyIso (t + u) (ModuleCat.of K K)).inv.hom (a * b) := by
  classical
  have hpair {M N : ModuleCat.{u} K} (eM : M ≅ ModuleCat.of K K)
      (eN : N ≅ ModuleCat.of K K) (a b : K) :
      (eM.hom ⊗ₘ eN.hom).hom (eM.inv.hom a ⊗ₜ[K] eN.inv.hom b) = a ⊗ₜ[K] b := by
    change (eM.hom ⊗ₘ eN.hom) (eM.inv a ⊗ₜ[K] eN.inv b) = a ⊗ₜ[K] b
    simp
  change ((GradedObject.Monoidal.ιTensorObj (degreeLine K t) (degreeLine K u)
    t u (t + u) rfl) ≫ hom K t u (t + u)).hom _ = _
  simp only [hom, dite_true, GradedObject.Monoidal.ι_tensorObjDesc]
  change (GradedObject.singleObjApplyIso (t + u) (ModuleCat.of K K)).inv.hom
    ((TensorProduct.lid K K)
      (((GradedObject.singleObjApplyIso t (ModuleCat.of K K)).hom ⊗ₘ
        (GradedObject.singleObjApplyIso u (ModuleCat.of K K)).hom).hom _)) = _
  exact congrArg (fun z => (GradedObject.singleObjApplyIso (t + u) (ModuleCat.of K K)).inv.hom
    ((TensorProduct.lid K K) z))
    (hpair (GradedObject.singleObjApplyIso t (ModuleCat.of K K))
      (GradedObject.singleObjApplyIso u (ModuleCat.of K K)) a b)

/-- The inverse takes the chosen generator to the two chosen generators. -/
theorem inv_generator (t u : ℤ) :
    (inv K t u (t + u)).hom (degreeLineGenerator K (t + u)) =
      (tensorInclusion K (degreeLine K t) (degreeLine K u) t u (t + u) rfl).hom
        (degreeLineGenerator K t ⊗ₜ[K] degreeLineGenerator K u) := by
  classical
  simp only [inv, dite_true, degreeLineGenerator]
  change (tensorInclusion K (degreeLine K t) (degreeLine K u) t u (t + u) rfl).hom
    (((GradedObject.singleObjApplyIso t (ModuleCat.of K K)).inv ⊗ₘ
        (GradedObject.singleObjApplyIso u (ModuleCat.of K K)).inv).hom
      (1 ⊗ₜ[K] ((GradedObject.singleObjApplyIso (t + u) (ModuleCat.of K K)).hom
        ((GradedObject.singleObjApplyIso (t + u) (ModuleCat.of K K)).inv 1)))) = _
  rw [ModuleCat.hom_inv_apply]
  rfl

/-- The prescribed multiplication intertwines the actual shifted trivial
coaction with the trivial coaction in the sum degree. -/
theorem hom_coaction {C : Comon (GrVect K)} (η : Coaugmentation C) (t u : ℤ) :
    ((internalShift K C t).obj (trivialAt K η u)).a ≫
        (rightTensorComonad C).map (hom K t u) =
      hom K t u ≫ (trivialAt K η (t + u)).a := by
  change (degreeLine K t ◁ RightTensor.trivialCoaction η (degreeLine K u) ≫
      (α_ (degreeLine K t) (degreeLine K u) C.X).inv) ≫ (hom K t u ▷ C.X) =
    hom K t u ≫ RightTensor.trivialCoaction η (degreeLine K (t + u))
  simp only [RightTensor.trivialCoaction, whiskerLeft_comp, Category.assoc]
  erw [associator_inv_naturality_right_assoc]
  erw [← rightUnitor_tensor_inv_assoc]
  exact RightTensor.trivial_naturality η (hom K t u)

end KIP126.Algebra.GradedComodule.TensorLine
