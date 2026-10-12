module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Equivalence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Group.Structure.Data
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Group.MinimalAxioms

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- Transport the actual loop-concatenation group along the fully faithful
ordinary loop functor, on each original stable hom set. -/
@[implicit_reducible]
noncomputable def sourceHomGroup (A B : SourceCategory.{u}) : AddGroup (A ⟶ B) := by
  letI : AddGroup (sourceLoopFunctor.obj A ⟶ sourceLoopFunctor.obj B) :=
    sourceLoopHomGroup B.as.obj (sourceLoopFunctor.obj A)
  let e := (Functor.FullyFaithful.ofFullyFaithful sourceLoopFunctor).homEquiv (X := A) (Y := B)
  letI : Add (A ⟶ B) := e.add
  letI : Neg (A ⟶ B) := e.Neg
  have hz : e (0 : A ⟶ B) = 0 := sourceLoopFunctor.map_zero A B
  exact AddGroup.ofLeftAxioms
    (fun f g h => e.injective (by simp only [Equiv.add_def, Equiv.apply_symm_apply, add_assoc]))
    (fun f => e.injective (by simp only [Equiv.add_def, Equiv.apply_symm_apply, hz, zero_add]))
    (fun f => e.injective (by
      simp only [Equiv.add_def, Equiv.neg_def, Equiv.apply_symm_apply, neg_add_cancel, hz]))

end KIP126.StableHomotopy.Implementation.Prespectrum
