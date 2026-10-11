module

public import KIP126.LinProgram.Model.E2.Data
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs

@[expose] public section


/-! The complete archived module presentation over the existing sphere E2.
No extra relation is inferred from a native degree bound. -/
namespace KIP126.LinModule.Presentation

abbrev Free (n : Nat) := Fin n →₀ LinE2.E2

noncomputable def ofPowers (n : Nat) : List Nat → Free n
  | [j] => if h : j < n then Finsupp.single ⟨j, h⟩ 1 else 0
  | i :: a :: rest =>
    if h : i < LinE2.RawData.generatorCount then
      LinE2.generator ⟨i, h⟩ ^ a • ofPowers n rest
    else 0
  | [] => 0

noncomputable def monomialVector (n : Nat) (code : String) : Free n :=
  ofPowers n ((code.splitOn ",").map (fun a => a.toNat?.getD 0))

noncomputable def relationVector (n : Nat) (code : String) : Free n :=
  ((code.splitOn ";").map (monomialVector n)).sum

noncomputable def definingSubmodule (n : Nat) (relations : List String) :
    Submodule LinE2.E2 (Free n) :=
  Submodule.span LinE2.E2 {v | ∃ code ∈ relations, v = relationVector n code}

abbrev Model (n : Nat) (relations : List String) :=
  Free n ⧸ definingSubmodule n relations

noncomputable def projection (n : Nat) (relations : List String) :
    Free n →ₗ[LinE2.E2] Model n relations := (definingSubmodule n relations).mkQ

noncomputable def generator (n : Nat) (relations : List String) (i : Fin n) :
    Model n relations := projection n relations (Finsupp.single i 1)

noncomputable def evaluatePowers {M : Type*} [AddCommGroup M] [Module LinE2.E2 M]
    {n : Nat} (g : Fin n → M) : List Nat → M
  | [j] => if h : j < n then g ⟨j, h⟩ else 0
  | i :: a :: rest =>
    if h : i < LinE2.RawData.generatorCount then
      LinE2.generator ⟨i, h⟩ ^ a • evaluatePowers g rest
    else 0
  | [] => 0

end KIP126.LinModule.Presentation
