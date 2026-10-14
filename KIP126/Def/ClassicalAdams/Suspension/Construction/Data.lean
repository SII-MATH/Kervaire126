module

public import KIP126.Def.ClassicalAdams.Suspension.Data
public import KIP126.Def.ClassicalAdams.TowerLayer.Basic.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Unit.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Coaction.Unit.Proofs
public import KIP126.Def.StableHomotopy.Context.CofiberExtension.Proofs

@[expose] public section


/-! Actual suspension comparisons from the specified tensor and unit shift
structures. Triangle completion uses the selected cofibers. It does not assert
independence of the completion choices or identify any native coordinates. -/

namespace KIP126.Classical.Adams.Suspension.Construction

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- Complete the two given isomorphisms to the normalized shifted cofiber triangle. -/
def cofiberTriangleIso {A B A' B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B')
    (eA : A' ≅ A⟦(1 : ℤ)⟧) (eB : B' ≅ B⟦(1 : ℤ)⟧)
    (hcomm : f' ≫ eB.hom = eA.hom ≫ f⟦(1 : ℤ)⟧') :
    Triangle.mk f' (HasFunctorialCofiber.cofibι f') (HasFunctorialCofiber.cofibδ f') ≅
      CofiberExtension.shiftedCofiberTriangle f 1 :=
  isoTriangleOfIso₁₂ _ _ (HasFunctorialCofiber.cofib_distinguished f')
    (CofiberExtension.shiftedCofiberTriangle_distinguished f 1) eA eB hcomm

/-- The third component uses the already chosen cofibers. -/
def cofiberIso {A B A' B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B')
    (eA : A' ≅ A⟦(1 : ℤ)⟧) (eB : B' ≅ B⟦(1 : ℤ)⟧)
    (hcomm : f' ≫ eB.hom = eA.hom ≫ f⟦(1 : ℤ)⟧') :
    HasFunctorialCofiber.cofib f' ≅ (HasFunctorialCofiber.cofib f)⟦(1 : ℤ)⟧ :=
  Triangle.π₃.mapIso (cofiberTriangleIso f f' eA eB hcomm)

variable (H : Mod2EilenbergMacLane (C := C))
  [(tensorLeft H.HF2).CommShift ℤ] [(mod2UnitNatTrans H).CommShift ℤ]

set_option backward.isDefEq.respectTransparency false in
/-- A full triangle isomorphism, with the second component negative to
compensate for the two signs of the shifted inverse-rotated triangle. -/
def fiberTriangleIso {Y Z : C} (e : Y ≅ Z⟦(1 : ℤ)⟧) :
    adamsFiberTriangle (adamsUnit H.unit Y) ≅
      (Triangle.shiftFunctor C (1 : ℤ)).obj (adamsFiberTriangle (adamsUnit H.unit Z)) :=
  (rotCompInvRot.app _ : _ ≅ _) ≪≫
    (invRotate C).mapIso
      (isoTriangleOfIso₁₂ _ _
        (rot_of_distTriang _ (adamsFiberTriangle_distinguished (adamsUnit H.unit Y)))
        (rot_of_distTriang _ (Triangle.shift_distinguished _
          (adamsFiberTriangle_distinguished (adamsUnit H.unit Z)) (1 : ℤ)))
        (-e)
        ((tensorLeft H.HF2).mapIso e ≪≫
          ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).app Z)
        (by
          change adamsUnit H.unit Y ≫ _ = (-e.hom) ≫ ((1 : ℤ).negOnePow • (adamsUnit H.unit Z)⟦(1 : ℤ)⟧')
          simp only [Int.negOnePow_one, Units.neg_smul, one_smul,
            Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
          change adamsUnit H.unit Y ≫ (H.HF2 ◁ e.hom) ≫ _ = _
          rw [← Category.assoc, ← adamsUnit_naturality H.unit e.hom,
            Category.assoc]
          exact congrArg (fun k => e.hom ≫ k) (mod2Unit_shift H Z (1 : ℤ)))) ≪≫
    (rotCompInvRot.app _).symm

/-- The single recursive fiber step for an arbitrary given previous-stage
suspension comparison. The output uses the already selected fibers. -/
def fiberIso {Y Z : C} (e : Y ≅ Z⟦(1 : ℤ)⟧) :
    fiber (adamsUnit H.unit Y) ≅ (fiber (adamsUnit H.unit Z))⟦(1 : ℤ)⟧ :=
  Triangle.π₁.mapIso (fiberTriangleIso H e)

/-- Recursively compare every actual tower term, starting with the identity. -/
def towerIso (X : C) : ∀ s : ℕ,
    adamsTower H.unit (X⟦(1 : ℤ)⟧) s ≅ (adamsTower H.unit X s)⟦(1 : ℤ)⟧
  | 0 => Iso.refl _
  | s + 1 => fiberIso H (towerIso X s)

end
end KIP126.Classical.Adams.Suspension.Construction
