module

public import KIP126.Def.StableHomotopy.Implementation.Completion.TwoComplete.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

/-- The fixed HF₂-local sphere is 2-complete. The actual locality-to-
completeness proof is independent of the still unfinished construction
of the fixed reflection used in this closed application. -/
theorem completedSphere_twoComplete :
    (completionModel.replacement.obj Prespectrum.sphere).IsTwoComplete :=
  completionModel.replacement_isTwoComplete Prespectrum.sphere

end KIP126.StableHomotopy.Implementation
