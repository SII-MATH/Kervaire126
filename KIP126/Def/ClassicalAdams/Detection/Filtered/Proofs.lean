module

public import KIP126.Def.ClassicalAdams.Detection.Predicates

@[expose] public section


namespace KIP126.Classical.Adams.TowerDetection

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
open KIP126.Core.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}

/-- Detection in the actual tower filtration supplies an actual filtered
homotopy lift. This extracts the range witness from the already constructed
filtration; it does not assert that an arbitrary lift has the given E₂ label. -/
theorem Detects.exists_towerLift {c : Convergence unit X} {p : ℤ × ℤ}
    {x : (adamsTowerInternalSpectralSequence unit X).Page 2 p}
    {α : HomotopyGroup (p.2 - p.1) X} (h : Detects c p x α) :
    ∃ a : HomotopyGroup (p.2 - p.1) (adamsTowerAt unit X p.1),
      a ≫ adamsTowerMap unit X 0 p.1.toNat (Nat.zero_le _) = α := by
  obtain ⟨z, hz, b, hb, he⟩ := h
  have hf : ModuleCat.subobjectModule (homotopy X (p.2 - p.1))
      ((filtration unit X).F p.1 (p.2 - p.1)) =
        filtrationSubmodule unit X p.1 (p.2 - p.1) :=
    (ModuleCat.subobjectModule _).apply_symm_apply _
  have ha : α ∈ filtrationSubmodule unit X p.1 (p.2 - p.1) := by
    rw [← hf]
    change α ∈ LinearMap.range (((filtration unit X).F p.1 (p.2 - p.1)).arrow.hom)
    exact ⟨b, hb⟩
  exact ha

end KIP126.Classical.Adams.TowerDetection
