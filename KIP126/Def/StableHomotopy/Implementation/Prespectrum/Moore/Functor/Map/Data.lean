module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Universal.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The actual Moore map is the unique extension across the same
constructed unit into the already constructed Moore target. -/
noncomputable def sourceMooreCompletionMap (p : ℕ) {X Y : SourceCategory.{u}} (f : X ⟶ Y) :
    sourceMooreCompletion p X ⟶ sourceMooreCompletion p Y :=
  ((sourceMooreCompletionUnit_precomp_bijective p X (sourceMooreCompletion p Y)
    (fun U hU => by
      letI := hU
      exact sourceMooreCompletion_hom_subsingleton p Y U)).surjective
    (f ≫ sourceMooreCompletionUnit p Y)).choose

end KIP126.StableHomotopy.Implementation
