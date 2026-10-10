import KIP126.Def.SpectralSequence.Convergence.Category.Data
import KIP126.Def.SpectralSequence.ModuleSubobject.Proofs

/-! API regression checks for the migrated nested-subobject convergence layer. -/

namespace KIP126.Checks.SpectralSequence.ConvergenceSSData

open KIP126.Core.SpectralSequence

#check Filtration
#check Filtration.F
#check Filtration.mono
#check Filtration.associatedGraded
#check Filtration.toAssociatedGraded
#check Filtration.transportGraded
#check Filtration.IsBounded
#check Filtration.IsBoundedBelow
#check Filtration.IsBoundedAbove
#check Filtration.IsExhaustive
#check Filtration.IsHausdorff
#check Convergence
#check Convergence.filtrationDegree
#check Convergence.stemDegree
#check ConvergenceMorphismData
#check ConvergenceMorphism
#check Detects
#check detect_zero
#check detect_difference
#check FilteredMorphism
#check FilteredMorphism.inducedGrMap
#check ConvergingSS

end KIP126.Checks.SpectralSequence.ConvergenceSSData

/-! Separation does not require a finite zero layer. The filtration of
integer-valued functions vanishing below `s` has zero intersection, while
its `s`th layer contains the nonzero function supported at `s`. -/
namespace KIP126.Checks.SpectralSequence.Separation

open CategoryTheory KIP126.Core.SpectralSequence

private def tailSubmodule (s : ℤ) : Submodule ℤ (ℤ → ℤ) where
  carrier := {f | ∀ n : ℤ, n < s → f n = 0}
  zero_mem' := by intro n _; rfl
  add_mem' := by intro f g hf hg n hn; change f n + g n = 0; rw [hf n hn, hg n hn, add_zero]
  smul_mem' := by intro c f hf n hn; change c * f n = 0; rw [hf n hn, mul_zero]

private noncomputable def tailFiltration :
    Filtration (fun _ : Unit => ModuleCat.of ℤ (ℤ → ℤ)) where
  F s _ := (ModuleCat.subobjectModule _).symm (tailSubmodule s)
  mono s _ := (ModuleCat.subobjectModule _).symm.monotone (by
    intro f hf n hn
    exact hf n (by omega))

private theorem tailFiltration_level (s : ℤ) (k : Unit) :
    (ModuleCat.subobjectModule (ModuleCat.of ℤ (ℤ → ℤ)))
      (tailFiltration.F s k) = tailSubmodule s :=
  OrderIso.apply_symm_apply _ _

private theorem mem_tailSubmodule (s : ℤ) (f : ℤ → ℤ) :
    f ∈ tailSubmodule s ↔ ∀ n : ℤ, n < s → f n = 0 := Iff.rfl

attribute [local irreducible] tailFiltration tailSubmodule

example : tailFiltration.IsHausdorff := by
  intro k S hS
  apply (ModuleCat.subobjectModule (ModuleCat.of ℤ (ℤ → ℤ))).injective
  rw [OrderIso.map_bot]
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  funext n
  have hle := (ModuleCat.subobjectModule _).monotone (hS (n + 1))
  rw [tailFiltration_level] at hle
  have hm := hle hf
  exact (mem_tailSubmodule _ _).mp hm n (by omega)

example : ¬ tailFiltration.toAlgebra.IsEventuallyZero := by
  intro h
  obtain ⟨s, hs⟩ := h ()
  change tailFiltration.F s () = ⊥ at hs
  have heq := congrArg (ModuleCat.subobjectModule (ModuleCat.of ℤ (ℤ → ℤ))) hs
  rw [tailFiltration_level, OrderIso.map_bot] at heq
  let f : ℤ → ℤ := fun n => if n = s then 1 else 0
  have hf : f ∈ tailSubmodule s := by
    rw [mem_tailSubmodule]
    intro n hn
    simp [f, ne_of_lt hn]
  rw [heq] at hf
  have hz : f = 0 := hf
  have hc := congrFun hz s
  norm_num [f] at hc

end KIP126.Checks.SpectralSequence.Separation
