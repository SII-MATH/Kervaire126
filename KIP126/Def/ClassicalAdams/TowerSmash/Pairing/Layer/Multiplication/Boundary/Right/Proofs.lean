import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Boundary.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Boundary.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory BraidedCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]
  [∀ Y : C, (tensorLeft Y).CommShift ℤ]

/-- The other one-unit boundary of the same specified layer product.
Its successor map is the explicitly constructed braided lift, not an
unproved identification with the ordered right successor of the tower. -/
theorem adamsSphereLayerProduct_ι_left_δ_comparison
    (h : RightTensorSuspensionCompatibility (C := C))
    (hb : TensorSuspensionBraidingCompatibility (C := C)) (s t : ℕ) :
    (((adamsLayerTriangle H.unit (𝟙_ C) s).mor₂ ⊗ₘ
        (adamsLayerIso H.unit (𝟙_ C) t).inv) ≫ adamsSphereLayerProduct H R s t) ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃ =
      -((adamsTower H.unit (𝟙_ C) s ◁
          (adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) t))).mor₃) ≫
        (Functor.commShiftIso (tensorLeft (adamsTower H.unit (𝟙_ C) s)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (t + 1)) ≫
        (adamsTowerSpherePairingBoundaryRight H.unit s t)⟦(1 : ℤ)⟧') := by
  have hd := adamsLayerIso_δ H.unit (𝟙_ C) (t + s)
  have hp := adamsSphereLayerProduct_ι_left_comparison H R s t
  have hk := adamsTowerSpherePairingBoundaryRight_δ H.unit h hb s t
  exact (congrArg (fun f => (((adamsLayerTriangle H.unit (𝟙_ C) s).mor₂ ⊗ₘ
    (adamsLayerIso H.unit (𝟙_ C) t).inv) ≫ adamsSphereLayerProduct H R s t) ≫ f) hd).trans
    ((Preadditive.comp_neg _ _).trans (congrArg (fun f => -f)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫
          (adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) (t + s)))).mor₃)
            hp).trans hk))))

variable [MonoidalPreadditive C]

/-- On the original layer objects, the second-input boundary retains the
braided successor map forced by the coefficient product. -/
theorem adamsSphereLayerProduct_ι_left_δ
    (h : RightTensorSuspensionCompatibility (C := C))
    (hb : TensorSuspensionBraidingCompatibility (C := C)) (s t : ℕ) :
    ((adamsLayerTriangle H.unit (𝟙_ C) s).mor₂ ▷ adamsLayerAt H.unit (𝟙_ C) t) ≫
        adamsSphereLayerProduct H R s t ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃ =
      (adamsTower H.unit (𝟙_ C) s ◁ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃) ≫
        (Functor.commShiftIso (tensorLeft (adamsTower H.unit (𝟙_ C) s)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (t + 1)) ≫
        (adamsTowerSpherePairingBoundaryRight H.unit s t)⟦(1 : ℤ)⟧' := by
  have hd : (adamsLayerIso H.unit (𝟙_ C) t).inv ≫
      (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃ =
      -(adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) t))).mor₃ := by
    exact (congrArg (fun f => (adamsLayerIso H.unit (𝟙_ C) t).inv ≫ f)
      (adamsLayerIso_δ H.unit (𝟙_ C) t)).trans
      ((Preadditive.comp_neg _ _).trans
        (congrArg (fun f => -f) (Iso.inv_hom_id_assoc _ _)))
  have ht : (adamsTower H.unit (𝟙_ C) s ◁ (adamsLayerIso H.unit (𝟙_ C) t).inv) ≫
      (adamsTower H.unit (𝟙_ C) s ◁ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃) =
      -(adamsTower H.unit (𝟙_ C) s ◁
        (adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) t))).mor₃) :=
    (whiskerLeft_comp _ _ _).symm.trans
      ((congrArg (fun f => adamsTower H.unit (𝟙_ C) s ◁ f) hd).trans
        ((tensorLeft (adamsTower H.unit (𝟙_ C) s)).map_neg))
  have hr : (adamsTower H.unit (𝟙_ C) s ◁ (adamsLayerIso H.unit (𝟙_ C) t).inv) ≫
      ((adamsTower H.unit (𝟙_ C) s ◁ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃) ≫
        (Functor.commShiftIso (tensorLeft (adamsTower H.unit (𝟙_ C) s)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (t + 1)) ≫
        (adamsTowerSpherePairingBoundaryRight H.unit s t)⟦(1 : ℤ)⟧') =
      -((adamsTower H.unit (𝟙_ C) s ◁
          (adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) t))).mor₃) ≫
        (Functor.commShiftIso (tensorLeft (adamsTower H.unit (𝟙_ C) s)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (t + 1)) ≫
        (adamsTowerSpherePairingBoundaryRight H.unit s t)⟦(1 : ℤ)⟧') :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫
        (Functor.commShiftIso (tensorLeft (adamsTower H.unit (𝟙_ C) s)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (t + 1)) ≫
        (adamsTowerSpherePairingBoundaryRight H.unit s t)⟦(1 : ℤ)⟧') ht).trans
        (Preadditive.neg_comp _ _))
  apply (cancel_epi
    (adamsTower H.unit (𝟙_ C) s ◁ (adamsLayerIso H.unit (𝟙_ C) t).inv)).mp
  have hl : (adamsTower H.unit (𝟙_ C) s ◁ (adamsLayerIso H.unit (𝟙_ C) t).inv) ≫
      (((adamsLayerTriangle H.unit (𝟙_ C) s).mor₂ ▷ adamsLayerAt H.unit (𝟙_ C) t) ≫
        adamsSphereLayerProduct H R s t ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃) =
      (((adamsLayerTriangle H.unit (𝟙_ C) s).mor₂ ⊗ₘ
        (adamsLayerIso H.unit (𝟙_ C) t).inv) ≫ adamsSphereLayerProduct H R s t) ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃ := by
    simp only [tensorHom_def', Category.assoc]
    rfl
  exact hl.trans ((adamsSphereLayerProduct_ι_left_δ_comparison H R h hb s t).trans hr.symm)

/-- An exact criterion for replacing the braided lift by the ordered
successor in the actual layer boundary formula. The obstruction is a
concrete composite on existing objects; its vanishing remains unproved. -/
theorem adamsSphereLayerProduct_ι_left_δ_ordered_iff
    (h : RightTensorSuspensionCompatibility (C := C))
    (hb : TensorSuspensionBraidingCompatibility (C := C)) (s t : ℕ) :
    (((adamsLayerTriangle H.unit (𝟙_ C) s).mor₂ ▷ adamsLayerAt H.unit (𝟙_ C) t) ≫
        adamsSphereLayerProduct H R s t ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃ =
      (adamsTower H.unit (𝟙_ C) s ◁ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃) ≫
        (Functor.commShiftIso (tensorLeft (adamsTower H.unit (𝟙_ C) s)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (t + 1)) ≫
        (adamsTowerSpherePairingNextRight H.unit s t)⟦(1 : ℤ)⟧') ↔
      (adamsTower H.unit (𝟙_ C) s ◁ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃) ≫
        (Functor.commShiftIso (tensorLeft (adamsTower H.unit (𝟙_ C) s)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (t + 1)) ≫
        (adamsTowerSpherePairingBoundaryRight H.unit s t -
          adamsTowerSpherePairingNextRight H.unit s t)⟦(1 : ℤ)⟧' = 0 := by
  have hsub {A B U V : C} (a : A ⟶ B) (b : B ⟶ U⟦(1 : ℤ)⟧)
      (f g : U ⟶ V) :
      (a ≫ b ≫ f⟦(1 : ℤ)⟧' = a ≫ b ≫ g⟦(1 : ℤ)⟧') ↔
        a ≫ b ≫ (f - g)⟦(1 : ℤ)⟧' = 0 := by
    simp only [Functor.map_sub, Preadditive.comp_sub, sub_eq_zero]
  have hp := adamsSphereLayerProduct_ι_left_δ H R h hb s t
  constructor
  · intro he
    exact (hsub _ _ _ _).mp (hp.symm.trans he)
  · intro hz
    exact hp.trans ((hsub _ _ _ _).mpr hz)

end
end KIP126.Classical.Adams
