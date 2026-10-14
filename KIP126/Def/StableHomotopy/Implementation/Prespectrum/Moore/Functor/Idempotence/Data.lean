module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Functor.Idempotence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual Moore completion is idempotent, through the original
unit at its completed objects. -/
noncomputable def sourceMooreCompletionIdempotentIso (p : ℕ) :
    sourceMooreCompletionFunctor.{u} p ⋙ sourceMooreCompletionFunctor p ≅
      sourceMooreCompletionFunctor p :=
  (NatIso.ofComponents
    (fun (X : SourceCategory.{u}) =>
      asIso (sourceMooreCompletionUnit p (sourceMooreCompletion p X)))
    (fun f => (sourceMooreCompletionMap_unit p (sourceMooreCompletionMap p f)).symm)).symm

end KIP126.StableHomotopy.Implementation
