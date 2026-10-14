module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Equivalence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Group.Structure.Data
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Group.MinimalAxioms
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Group.Naturality.Proofs

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

attribute [local instance] sourceHomGroup

/-- The transported addition is exactly actual loop concatenation after
applying the fully faithful source loop functor. -/
theorem sourceHomGroup_map_add {A B : SourceCategory.{u}} (f g : A ⟶ B) :
    sourceLoopFunctor.map (f + g) = sourceLoopAdd B.as.obj
      (sourceLoopFunctor.map f) (sourceLoopFunctor.map g) := by
  change (Functor.FullyFaithful.ofFullyFaithful sourceLoopFunctor).homEquiv
    ((Functor.FullyFaithful.ofFullyFaithful sourceLoopFunctor).homEquiv.symm
      (sourceLoopAdd B.as.obj (sourceLoopFunctor.map f) (sourceLoopFunctor.map g))) = _
  exact Equiv.apply_symm_apply _ _

theorem sourceHomGroup_add_comp {A B C : SourceCategory.{u}}
    (f g : A ⟶ B) (h : B ⟶ C) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  apply sourceLoopFunctor.map_injective
  rw [Functor.map_comp, sourceHomGroup_map_add, sourceHomGroup_map_add,
    Functor.map_comp, Functor.map_comp]
  exact sourceLoopAdd_postcomp _ _ h

theorem sourceHomGroup_comp_add {A B C : SourceCategory.{u}}
    (f : A ⟶ B) (g h : B ⟶ C) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  apply sourceLoopFunctor.map_injective
  rw [Functor.map_comp, sourceHomGroup_map_add, sourceHomGroup_map_add,
    Functor.map_comp, Functor.map_comp]
  exact comp_sourceLoopAdd _ _ _ _

end KIP126.StableHomotopy.Implementation.Prespectrum

end
