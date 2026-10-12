module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Functor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The same constructed unit is an isomorphism after one actual Moore
completion, by its proved orthogonality universal property. -/
instance sourceMooreCompletionUnit_completed_isIso (p : ℕ) (X : SourceCategory.{u}) :
    IsIso (sourceMooreCompletionUnit p (sourceMooreCompletion p X)) :=
  sourceMooreCompletionUnit_isIso_of_orthogonal p (sourceMooreCompletion p X)
    (fun U hU => by
      letI := hU
      exact sourceMooreCompletion_hom_subsingleton p X U)

/-- Completing the unit gives exactly the unit of the completed object,
not merely some other isomorphism of the same two objects. -/
theorem sourceMooreCompletionMap_unit_eq (p : ℕ) (X : SourceCategory.{u}) :
    sourceMooreCompletionMap p (sourceMooreCompletionUnit p X) =
      sourceMooreCompletionUnit p (sourceMooreCompletion p X) := by
  apply sourceMooreCompletion_hom_ext p
  exact sourceMooreCompletionMap_unit p (sourceMooreCompletionUnit p X)

end KIP126.StableHomotopy.Implementation
