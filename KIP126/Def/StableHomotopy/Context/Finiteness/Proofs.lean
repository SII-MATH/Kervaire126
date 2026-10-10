import KIP126.Def.StableHomotopy.Context.Data
import Mathlib.GroupTheory.QuotientGroup.Finite

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Exactness of a distinguished triangle makes the middle representable
Hom group finite whenever both end Hom groups are finite. -/
theorem finite_hom_middle_of_distinguished (T : Triangle C)
    (hT : T ∈ distTriang C) (W : C)
    [Finite (W ⟶ T.obj₁)] [Finite (W ⟶ T.obj₃)] : Finite (W ⟶ T.obj₂) := by
  let f : (W ⟶ T.obj₁) →+ (W ⟶ T.obj₂) :=
    { toFun := fun a => a ≫ T.mor₁
      map_zero' := by simp
      map_add' := by intros; simp }
  let g : (W ⟶ T.obj₂) →+ (W ⟶ T.obj₃) :=
    { toFun := fun b => b ≫ T.mor₂
      map_zero' := by simp
      map_add' := by intros; simp }
  letI := Fintype.ofFinite (W ⟶ T.obj₁)
  letI := Fintype.ofFinite (W ⟶ T.obj₃)
  letI := AddGroup.fintypeOfKerLeRange f g (by
    intro b hb
    obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT b hb
    exact ⟨a, ha.symm⟩)
  infer_instance

end KIP126.StableHomotopy
