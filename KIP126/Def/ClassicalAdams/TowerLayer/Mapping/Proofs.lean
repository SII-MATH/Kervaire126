import KIP126.Def.ClassicalAdams.TowerLayer.Basic.Proofs
import KIP126.Def.StableHomotopy.Context.Proofs

namespace KIP126.Classical.Adams

open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- A vanishing group of maps into the desuspended target makes the actual
fiber inclusion injective on maps out of Z. This is not a categorical
monomorphism assertion for the fiber inclusion. -/
theorem fiberι_postcomp_injective_of_vanishing {X Y Z : C} (f : X ⟶ Y)
    (hvan : ∀ a : Z ⟶ Y⟦(-1 : ℤ)⟧, a = 0) :
    Function.Injective (fun g : Z ⟶ fiber f => g ≫ fiberι f) := by
  intro g₁ g₂ hcomp
  change g₁ ≫ fiberι f = g₂ ≫ fiberι f at hcomp
  have hz : (g₁ - g₂) ≫ (adamsFiberTriangle f).invRotate.mor₂ = 0 := by
    change (g₁ - g₂) ≫ (-fiberι f) = 0
    rw [Preadditive.comp_neg, Preadditive.sub_comp,
      hcomp, sub_self, neg_zero]
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ (adamsFiberTriangle f).invRotate
    (inv_rot_of_distTriang _ (adamsFiberTriangle_distinguished f)) (g₁ - g₂) hz
  have ha0 : a = 0 := hvan a
  rw [ha0, Limits.zero_comp] at ha
  exact sub_eq_zero.mp ha

/-- Surjectivity in degree n kills the connecting map and makes the actual
fiber inclusion injective in degree n-1. This does not require vanishing of
the entire group of maps to the desuspended target. -/
theorem fiberι_homotopy_injective_of_surjective {X Y : C} (f : X ⟶ Y) (n : ℤ)
    (hsurj : Function.Surjective (inducedMap f n)) :
    Function.Injective (inducedMap (fiberι f) (n - 1)) := by
  let T : HoCofiberSequence (C := C) :=
    { X := fiber f
      Y := X
      Z := Y
      f := (adamsFiberTriangle f).mor₁
      g := f
      h := (adamsFiberTriangle f).mor₃
      distinguished := adamsFiberTriangle_distinguished f }
  intro x y hxy
  change x ≫ fiberι f = y ≫ fiberι f at hxy
  have hzero : inducedMap T.f (n - 1) (x - y) = 0 := by
    change (x - y) ≫ (-fiberι f) = 0
    rw [Preadditive.comp_neg, Preadditive.sub_comp, hxy, sub_self, neg_zero]
  obtain ⟨z, hz⟩ := (lesHomotopyExactH T n (x - y)).mp hzero
  obtain ⟨a, ha⟩ := hsurj z
  have hz0 : connectingHomomorphism T n z = 0 :=
    (les_homotopy_exact_g T n z).mpr ⟨a, ha⟩
  exact sub_eq_zero.mp (hz.symm.trans hz0)

end KIP126.Classical.Adams
