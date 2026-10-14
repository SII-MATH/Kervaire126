module

public import KIP126.Def.CategoryTheory.Shift.Integer.Chain.Coherence.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Chain.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Foundation

universe u

/-- The specified integer source iterate agrees with translation of its
canonical chain. The comparison is the unique lift of the identity at zero. -/
noncomputable def sourceIntegerChainShiftIso (d : ℤ) :
    sourceIntegerShiftFunctor.{u} d ⋙ sourceIntegerChainFunctor ≅
      sourceIntegerChainFunctor ⋙ shiftFunctor (IntegerChain sourceSuspensionFunctor) d :=
  ((Functor.FullyFaithful.ofFullyFaithful (IntegerChain.eval sourceSuspensionFunctor 0)).whiskeringRight
    SourceCategory).preimageIso (eqToIso (by
      change sourceIntegerShiftFunctor d = sourceIntegerShiftFunctor (d + 0)
      rw [add_zero]))

/-- Coherent integer shifts on the actual stable source category, with the
specified signed iterate functors and addition inherited from actual chains. -/
noncomputable instance sourceHasShift : HasShift SourceCategory.{u} ℤ :=
  sourceIntegerChainFullyFaithful.hasShift sourceIntegerShiftFunctor sourceIntegerChainShiftIso

end KIP126.StableHomotopy.Implementation.Prespectrum
