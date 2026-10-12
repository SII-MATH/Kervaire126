module

public import KIP126.Def.ClassicalAdams.Completion.Proofs
public import KIP126.Def.ClassicalAdams.Suspension.Data
public import KIP126.Def.ClassicalAdams.TowerLayer.Basic.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.StableHomotopy.Cohomology

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
  {H : Mod2EilenbergMacLane (C := C)} {X : C}

/-- The specified actual suspension comparison identifies completeness of
the suspended object with completeness of the original object. -/
theorem Suspension.TowerComparison.isENilpotentComplete_iff
    (S : Suspension.TowerComparison H X) :
    IsENilpotentComplete H.unit (X⟦(1 : ℤ)⟧) ↔
      IsENilpotentComplete H.unit X := by
  have h : (adamsResidualSequence H.unit (X⟦(1 : ℤ)⟧)).IsAcyclic ↔
      ((adamsResidualSequence H.unit X).map (shiftFunctor C (1 : ℤ))).IsAcyclic := by
    apply InverseSequence.isAcyclic_iff_of_iso (fun n => S.tower (n : ℤ))
    intro n
    have hn := S.tower_comm (n : ℤ) ((n : ℤ) + 1) (by omega)
    rw [adamsTowerMapAt_nat_succ, adamsTowerMapAt_nat_succ] at hn
    simpa [adamsResidualSequence, InverseSequence.map, adamsTowerAt] using hn
  exact h.trans ((adamsResidualSequence H.unit X).shift_isAcyclic_iff 1)

end KIP126.Classical.Adams
