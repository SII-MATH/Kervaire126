module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open Topology
open scoped Topology.Homotopy

universe u

/-- Postcompose an actual based cubical loop with the singular evaluation. -/
noncomputable def singularEvaluationLoop (A : BasedSpace.{u}) (n : ℕ)
    (p : GenLoop (Fin n) (singularRealization A) (singularRealization A).point) :
    GenLoop (Fin n) A A.point :=
  ⟨(singularEvaluation A).comp p.val, fun t ht =>
    (congrArg (singularEvaluation A) (p.property t ht)).trans (singularEvaluation_point A)⟩

/-- The induced map on the original based cubical homotopy quotient. -/
noncomputable def singularEvaluationHomotopy (A : BasedSpace.{u}) (n : ℕ) :
    _root_.HomotopyGroup (Fin n) (singularRealization A) (singularRealization A).point →
      _root_.HomotopyGroup (Fin n) A A.point :=
  Quotient.map (singularEvaluationLoop A n)
    (fun _ _ h => h.comp_continuousMap (singularEvaluation A))

end KIP126.StableHomotopy.Implementation
