import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Successor.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Step.Suspension.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The actual tower pairing, not an independent triangle completion,
intertwines the coefficient-side connecting maps under explicit ambient
tensor-suspension compatibility. -/
theorem adamsTowerSpherePairingIso_δ_left
    (h : RightTensorSuspensionCompatibility (C := C)) (s t : ℕ) :
    (α_ H (adamsTower unit (𝟙_ C) s) (adamsTower unit (𝟙_ C) t)).hom ≫
      H ◁ (adamsTowerSpherePairingIso unit s t).hom ≫
      (adamsFiberTriangle (adamsUnit unit (adamsTower unit (𝟙_ C) (t + s)))).mor₃ =
    ((adamsFiberTriangle (adamsUnit unit (adamsTower unit (𝟙_ C) s))).mor₃ ▷
        adamsTower unit (𝟙_ C) t) ≫
      (Functor.commShiftIso (tensorRight (adamsTower unit (𝟙_ C) t)) (1 : ℤ)).hom.app
        (adamsTower unit (𝟙_ C) (s + 1)) ≫
      (adamsTowerSpherePairingIso unit (s + 1) t).hom⟦(1 : ℤ)⟧' := by
  have hm :
      (((adamsFiberTensorIso unit (adamsTower unit (𝟙_ C) s)).hom ▷
          adamsTower unit (𝟙_ C) t) ≫
        (α_ (fiber unit) (adamsTower unit (𝟙_ C) s)
          (adamsTower unit (𝟙_ C) t)).hom ≫
        fiber unit ◁ (adamsTowerSpherePairingIso unit s t).hom) ≫
        (adamsFiberTensorIso unit (adamsTower unit (𝟙_ C) (t + s))).inv =
      (adamsTowerSpherePairingIso unit (s + 1) t).hom := by
    have hm := congrArg
      (fun f => f ≫ (adamsFiberTensorIso unit (adamsTower unit (𝟙_ C) (t + s))).inv)
      (adamsTowerSpherePairingIso_succ_comparison unit s t)
    exact hm.symm.trans ((Category.assoc _ _ _).trans
      ((congrArg (fun f => (adamsTowerSpherePairingIso unit (s + 1) t).hom ≫ f)
        (Iso.hom_inv_id _)).trans (Category.comp_id _)))
  have hm' :
      ((adamsFiberTensorIso unit (adamsTower unit (𝟙_ C) s)).hom ▷
          adamsTower unit (𝟙_ C) t) ≫
        (α_ (fiber unit) (adamsTower unit (𝟙_ C) s)
          (adamsTower unit (𝟙_ C) t)).hom ≫
        fiber unit ◁ (adamsTowerSpherePairingIso unit s t).hom ≫
        (adamsFiberTensorIso unit (adamsTower unit (𝟙_ C) (t + s))).inv =
      (adamsTowerSpherePairingIso unit (s + 1) t).hom := by
    simpa only [Category.assoc] using hm
  exact (adamsFiberTensorIso_pairing_δ unit h
    (adamsTowerSpherePairingIso unit s t).hom).trans
    (congrArg (fun f =>
      ((adamsFiberTriangle (adamsUnit unit (adamsTower unit (𝟙_ C) s))).mor₃ ▷
          adamsTower unit (𝟙_ C) t) ≫
        (Functor.commShiftIso (tensorRight (adamsTower unit (𝟙_ C) t)) (1 : ℤ)).hom.app
          (adamsTower unit (𝟙_ C) (s + 1)) ≫ f⟦(1 : ℤ)⟧') hm')

end
end KIP126.Classical.Adams
