module

public import KIP126.Def.ClassicalAdams.Completion.Predicates
public import KIP126.Def.ClassicalAdams.TowerNaturality.Isomorphism.Proofs
public import KIP126.Def.StableHomotopy.InverseSequence.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
  {H : C} (unit : 𝟙_ C ⟶ H)

/-- Actual object isomorphisms preserve and reflect Adams nilpotent completeness.
This uses the commuting maps on the specified residual towers, without requiring
identity or composition laws for the chosen cofiber maps. -/
theorem isENilpotentComplete_iff_of_iso {X Y : C} (e : X ≅ Y) :
    IsENilpotentComplete unit X ↔ IsENilpotentComplete unit Y := by
  exact InverseSequence.isAcyclic_iff_of_iso
    (D := adamsResidualSequence unit X) (E := adamsResidualSequence unit Y)
    (fun n => by
      letI := adamsTowerInduced_isIso unit e.hom n
      exact asIso (adamsTowerInduced unit e.hom n))
    (adamsTowerInduced_step unit e.hom)

/-- Transport an established completeness proof along a spectrum isomorphism. -/
theorem IsENilpotentComplete.of_iso {X Y : C}
    (hX : IsENilpotentComplete unit X) (e : X ≅ Y) :
    IsENilpotentComplete unit Y :=
  (isENilpotentComplete_iff_of_iso unit e).mp hX

end KIP126.Classical.Adams
