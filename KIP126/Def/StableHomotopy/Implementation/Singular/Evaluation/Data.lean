module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The actual counit as a based map, using its proved basepoint normalization. -/
noncomputable def singularEvaluationBased (A : BasedSpace.{u}) :
    singularRealization A ⟶ A :=
  ⟨singularEvaluation A,singularEvaluation_point A⟩

end KIP126.StableHomotopy.Implementation
