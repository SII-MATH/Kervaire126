module

public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Data

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- The constant sequence with its actual identity transition morphisms. -/
abbrev InverseSequence.constant (X : C) : InverseSequence C where
  obj _ := X
  step _ := 𝟙 X

end KIP126.StableHomotopy
