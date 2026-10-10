import KIP126.Def.StableHomotopy.InverseSequence.Data

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasProductsOfShape ℕ C]

/-- Vanishing of the sequential homotopy limit, expressed without
choosing its fiber object: the Milnor `1 - shift` map is an isomorphism. -/
def InverseSequence.IsAcyclic (D : InverseSequence C) : Prop :=
  IsIso D.oneSubShift

end KIP126.StableHomotopy
