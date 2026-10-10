import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.ULift

namespace KIP126.Core.ModuleCat

open CategoryTheory
universe v

/-- A homomorphism from the lifted rank-one free module is determined at one. -/
theorem freeRankOne_eval_one_injective (A : ModuleCat.{v} ℤ) :
    Function.Injective (fun f : ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ A =>
      f (ULift.up 1)) := by
  intro f g h
  change f.hom (ULift.up 1) = g.hom (ULift.up 1) at h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hz : z = z.down • (ULift.up 1 : ULift.{v} ℤ) := by
    apply ULift.ext
    simp
  rw [hz, f.hom.map_smul, g.hom.map_smul, h]

theorem finite_freeRankOne_hom (A : ModuleCat.{v} ℤ) [Finite A] :
    Finite (ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ A) :=
  Finite.of_injective _ (freeRankOne_eval_one_injective A)

end KIP126.Core.ModuleCat
