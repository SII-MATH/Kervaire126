import KIP126.Def.ClassicalAdams.Moss.Detection.Predicates
import KIP126.Def.ClassicalAdams.Moss.Convergence.Proofs

namespace KIP126.Classical.Adams.Moss

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  {H : C} {unit : 𝟙_ C ⟶ H} {X Y : C}

/-- Detection implies a permanent cycle, without silently asserting nonzero survival. -/
theorem permanent_of_detects {c : MappingAdamsConvergence unit X Y}
    {r : ℤ} {k : ℤ × ℤ} {x : (mappingSequence unit X Y).Page r k}
    {α : mappingAbutment X Y (k.2 - k.1)}
    (h : DetectsAbutment unit X Y c r k x α) : PermanentCycle unit X Y r k x := by
  obtain ⟨e, he, _⟩ := h
  exact ⟨e, he⟩

theorem permanent_of_detectsMap [(tensorLeft X).CommShift ℤ]
    {c : MappingAdamsConvergence unit X Y}
    {r : ℤ} {k : ℤ × ℤ} {x : (mappingSequence unit X Y).Page r k}
    {f : X⟦k.2 - k.1⟧ ⟶ Y} (h : DetectsMap unit X Y c r k x f) :
    PermanentCycle unit X Y r k x := permanent_of_detects h

/-- Detection gives an actual lift to the specified Adams filtration stage. -/
theorem towerLift_of_detects {c : MappingAdamsConvergence unit X Y}
    {r : ℤ} {k : ℤ × ℤ} {x : (mappingSequence unit X Y).Page r k}
    {α : mappingAbutment X Y (k.2 - k.1)}
    (h : DetectsAbutment unit X Y c r k x α) :
    ∃ g : HomotopyGroup (k.2 - k.1) (mappingStage unit X Y k.1.toNat),
      g ≫ mappingToTarget unit X Y k.1.toNat = α := by
  obtain ⟨e, _, a, ha, _⟩ := h
  exact (mappingFiltration_image unit X Y k.1 (k.2 - k.1) α).mp ⟨a, ha⟩

end KIP126.Classical.Adams.Moss
