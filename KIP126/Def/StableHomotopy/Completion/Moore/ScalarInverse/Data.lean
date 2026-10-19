module

public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Data

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- The residual sequence for scalar completion: each stage is the original
object, and each adjacent map multiplies by the scalar. -/
noncomputable def scalarResidualSequence (p : ℕ) (X : C) : InverseSequence C where
  obj _ := X
  step _ := p • 𝟙 X

end KIP126.StableHomotopy
