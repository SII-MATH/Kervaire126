module

public import KIP126.Def.CategoryTheory.Shift.Integer.Chain.Evaluation.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Foundation

universe u

instance sourceSuspensionFunctor_faithful : sourceSuspensionFunctor.{u}.Faithful :=
  sourceSuspensionEquivalence.fullyFaithfulFunctor.faithful

instance sourceSuspensionFunctor_full : sourceSuspensionFunctor.{u}.Full :=
  sourceSuspensionEquivalence.fullyFaithfulFunctor.full

/-- The chain of actual signed suspension iterates of a source object. -/
noncomputable def sourceIntegerChainFunctor :
    SourceCategory.{u} ⥤ IntegerChain sourceSuspensionFunctor where
  obj X := {
    obj n := (sourceIntegerShiftFunctor n).obj X
    step n := (sourceIntegerSuccessorIso n).symm.app X }
  map f := ⟨fun n => (sourceIntegerShiftFunctor n).map f, by
    intro n
    exact (sourceIntegerSuccessorIso n).inv.naturality f⟩

/-- A chain map between canonical source chains is determined by, and exists
for, its actual degree-zero map. -/
noncomputable def sourceIntegerChainFullyFaithful : sourceIntegerChainFunctor.{u}.FullyFaithful where
  preimage f := f.app 0
  map_preimage f := IntegerChain.hom_ext_zero _ _ rfl
  preimage_map f := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
