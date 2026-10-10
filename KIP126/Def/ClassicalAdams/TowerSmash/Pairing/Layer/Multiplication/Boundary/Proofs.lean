import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Restrictions.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Boundary.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- Boundary of the one-unit restriction of the actual coefficient-induced
layer product, in the existing coefficient coordinates. The minus sign is
the one already present in the positive-fiber layer comparison. -/
theorem adamsSphereLayerProduct_ι_right_δ_comparison
    (h : RightTensorSuspensionCompatibility (C := C)) (s t : ℕ) :
    (((adamsLayerIso H.unit (𝟙_ C) s).inv ⊗ₘ
        (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂) ≫ adamsSphereLayerProduct H R s t) ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃ =
      -(((adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) s))).mor₃ ▷
          adamsTower H.unit (𝟙_ C) t) ≫
        (Functor.commShiftIso (tensorRight (adamsTower H.unit (𝟙_ C) t)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (s + 1)) ≫
        (adamsTowerSpherePairingIso H.unit (s + 1) t).hom⟦(1 : ℤ)⟧') := by
  have hd := adamsLayerIso_δ H.unit (𝟙_ C) (t + s)
  have hp := adamsSphereLayerProduct_ι_right_comparison H R s t
  have hb := adamsTowerSpherePairingIso_δ_left H.unit h s t
  calc
    _ = (((adamsLayerIso H.unit (𝟙_ C) s).inv ⊗ₘ
          (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂) ≫ adamsSphereLayerProduct H R s t) ≫
        (-((adamsLayerIso H.unit (𝟙_ C) (t + s)).hom ≫
          (adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) (t + s)))).mor₃)) :=
      congrArg (fun f => (((adamsLayerIso H.unit (𝟙_ C) s).inv ⊗ₘ
        (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂) ≫ adamsSphereLayerProduct H R s t) ≫ f) hd
    _ = -(((((adamsLayerIso H.unit (𝟙_ C) s).inv ⊗ₘ
          (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂) ≫ adamsSphereLayerProduct H R s t) ≫
          (adamsLayerIso H.unit (𝟙_ C) (t + s)).hom) ≫
          (adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) (t + s)))).mor₃) := by
      exact (Preadditive.comp_neg _ _).trans
        (congrArg (fun f => -f) (Category.assoc _ _ _).symm)
    _ = -(((α_ H.HF2 (adamsTower H.unit (𝟙_ C) s)
          (adamsTower H.unit (𝟙_ C) t)).hom ≫
          H.HF2 ◁ (adamsTowerSpherePairingIso H.unit s t).hom) ≫
          (adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) (t + s)))).mor₃) :=
      congrArg (fun f => -(f ≫
        (adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) (t + s)))).mor₃)) hp
    _ = _ := congrArg (fun f => -f) ((Category.assoc _ _ _).trans hb)

variable [MonoidalPreadditive C]

/-- One-sided boundary formula for the specified layer multiplication
itself. The other input is restricted along the actual tower-to-layer map.
This is not a two-term boundary or pagewise Leibniz theorem. -/
theorem adamsSphereLayerProduct_ι_right_δ
    (h : RightTensorSuspensionCompatibility (C := C)) (s t : ℕ) :
    (adamsLayerAt H.unit (𝟙_ C) s ◁ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂) ≫
        adamsSphereLayerProduct H R s t ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃ =
      ((adamsLayerTriangle H.unit (𝟙_ C) s).mor₃ ▷ adamsTower H.unit (𝟙_ C) t) ≫
        (Functor.commShiftIso (tensorRight (adamsTower H.unit (𝟙_ C) t)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (s + 1)) ≫
        (adamsTowerSpherePairingIso H.unit (s + 1) t).hom⟦(1 : ℤ)⟧' := by
  have hd : (adamsLayerIso H.unit (𝟙_ C) s).inv ≫
      (adamsLayerTriangle H.unit (𝟙_ C) s).mor₃ =
      -(adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) s))).mor₃ := by
    calc
      _ = (adamsLayerIso H.unit (𝟙_ C) s).inv ≫
          (-((adamsLayerIso H.unit (𝟙_ C) s).hom ≫
            (adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) s))).mor₃)) :=
        congrArg (fun f => (adamsLayerIso H.unit (𝟙_ C) s).inv ≫ f)
          (adamsLayerIso_δ H.unit (𝟙_ C) s)
      _ = _ := by
        rw [Preadditive.comp_neg, Iso.inv_hom_id_assoc]
        rfl
  have ht : ((adamsLayerIso H.unit (𝟙_ C) s).inv ▷ adamsTower H.unit (𝟙_ C) t) ≫
      ((adamsLayerTriangle H.unit (𝟙_ C) s).mor₃ ▷ adamsTower H.unit (𝟙_ C) t) =
      -((adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) s))).mor₃ ▷
        adamsTower H.unit (𝟙_ C) t) :=
    (comp_whiskerRight _ _ _).symm.trans
      ((congrArg (fun f => f ▷ adamsTower H.unit (𝟙_ C) t) hd).trans
        ((tensorRight (adamsTower H.unit (𝟙_ C) t)).map_neg))
  have hr : ((adamsLayerIso H.unit (𝟙_ C) s).inv ▷ adamsTower H.unit (𝟙_ C) t) ≫
      (((adamsLayerTriangle H.unit (𝟙_ C) s).mor₃ ▷ adamsTower H.unit (𝟙_ C) t) ≫
        (Functor.commShiftIso (tensorRight (adamsTower H.unit (𝟙_ C) t)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (s + 1)) ≫
        (adamsTowerSpherePairingIso H.unit (s + 1) t).hom⟦(1 : ℤ)⟧') =
      -(((adamsFiberTriangle (adamsUnit H.unit (adamsTower H.unit (𝟙_ C) s))).mor₃ ▷
          adamsTower H.unit (𝟙_ C) t) ≫
        (Functor.commShiftIso (tensorRight (adamsTower H.unit (𝟙_ C) t)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (s + 1)) ≫
        (adamsTowerSpherePairingIso H.unit (s + 1) t).hom⟦(1 : ℤ)⟧') :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫
        (Functor.commShiftIso (tensorRight (adamsTower H.unit (𝟙_ C) t)) (1 : ℤ)).hom.app
          (adamsTower H.unit (𝟙_ C) (s + 1)) ≫
        (adamsTowerSpherePairingIso H.unit (s + 1) t).hom⟦(1 : ℤ)⟧') ht).trans
        (Preadditive.neg_comp _ _))
  apply (cancel_epi
    ((adamsLayerIso H.unit (𝟙_ C) s).inv ▷ adamsTower H.unit (𝟙_ C) t)).mp
  have hl : ((adamsLayerIso H.unit (𝟙_ C) s).inv ▷ adamsTower H.unit (𝟙_ C) t) ≫
      ((adamsLayerAt H.unit (𝟙_ C) s ◁ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂) ≫
        adamsSphereLayerProduct H R s t ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃) =
      (((adamsLayerIso H.unit (𝟙_ C) s).inv ⊗ₘ
        (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂) ≫ adamsSphereLayerProduct H R s t) ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃ := by
    simp only [tensorHom_def, Category.assoc]
    rfl
  exact hl.trans ((adamsSphereLayerProduct_ι_right_δ_comparison H R h s t).trans hr.symm)

end
end KIP126.Classical.Adams
