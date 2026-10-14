module

public import KIP126.Def.Algebra.GradedModule.Shift.Raw.Data

@[expose] public section

/-! Laws of the actual action on the shifted left module. -/

namespace KIP126.Algebra.GradedModule

open CategoryTheory MonoidalCategory GradedVectorSpace
open scoped MonObj

universe u

variable (K : Type u) [Field K]

theorem internalShiftAction_unit (A : Mon (GrVect K)) (t : ℤ) (M : LeftModule A) :
    (η[A.X] ▷ (M.A ⊗ GradedComodule.degreeLine K t)) ≫
        internalShiftAction K A t M =
      (λ_ (M.A ⊗ GradedComodule.degreeLine K t)).hom := by
  set_option backward.isDefEq.respectTransparency false in
    have hu : (η[A.X] ▷ M.A) ≫ M.a = (λ_ M.A).hom := by
      have h := M.unit
      change (λ_ M.A).inv ≫ (η[A.X] ▷ M.A) ≫ M.a = 𝟙 M.A at h
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id] using congrArg ((λ_ M.A).hom ≫ ·) h
    dsimp only [internalShiftAction]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, hu,
      ← leftUnitor_tensor_hom]

theorem internalShiftAction_assoc (A : Mon (GrVect K)) (t : ℤ) (M : LeftModule A) :
    (μ[A.X] ▷ (M.A ⊗ GradedComodule.degreeLine K t)) ≫
        internalShiftAction K A t M =
      (α_ A.X A.X (M.A ⊗ GradedComodule.degreeLine K t)).hom ≫
        (A.X ◁ internalShiftAction K A t M) ≫ internalShiftAction K A t M := by
  set_option backward.isDefEq.respectTransparency false in
    have ha : (μ[A.X] ▷ M.A) ≫ M.a =
        (α_ A.X A.X M.A).hom ≫ (A.X ◁ M.a) ≫ M.a := by
      have h := M.assoc
      change (α_ A.X A.X M.A).inv ≫ (μ[A.X] ▷ M.A) ≫ M.a =
        (A.X ◁ M.a) ≫ M.a at h
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        congrArg ((α_ A.X A.X M.A).hom ≫ ·) h
    dsimp only [internalShiftAction]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, ha]
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    rw [associator_inv_naturality_middle_assoc]
    simp only [← Category.assoc]
    congr 2
    monoidal_coherence

/-- Whiskering an actual left-module map by the degree line intertwines the
two prescribed shifted actions. -/
theorem internalShiftAction_map (A : Mon (GrVect K)) (t : ℤ)
    {M N : LeftModule A} (f : M ⟶ N) :
    (leftTensorMonad A).map (f.f ▷ GradedComodule.degreeLine K t) ≫
        internalShiftAction K A t N =
      internalShiftAction K A t M ≫ (f.f ▷ GradedComodule.degreeLine K t) := by
  set_option backward.isDefEq.respectTransparency false in
    have hf : (A.X ◁ f.f) ≫ N.a = M.a ≫ f.f := f.h
    change (A.X ◁ f.f ▷ _) ≫ (α_ _ _ _).inv ≫ (N.a ▷ _) =
      ((α_ _ _ _).inv ≫ (M.a ▷ _)) ≫ (f.f ▷ _)
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight,
      hf, comp_whiskerRight, Category.assoc]

end KIP126.Algebra.GradedModule
