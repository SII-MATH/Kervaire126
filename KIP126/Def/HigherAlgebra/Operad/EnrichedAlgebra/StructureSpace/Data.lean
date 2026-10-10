import KIP126.Def.HigherAlgebra.Operad.EnrichedAlgebra.Data
import KIP126.Def.HigherAlgebra.Operad.StructureSpace.Data

/-! Strict operadic actions with a path to the specified actual unit arrow.
This is a point-set mapping-space construction, not an assertion that strict
operad maps compute a derived space of algebra structures. -/

namespace KIP126.HigherAlgebra.Operad.EnrichedAlgebra

open CategoryTheory MonoidalCategory EnrichedTensor

universe u v w

variable {M : Type u} [Category.{v} M] [MonoidalCategory M]
  [EnrichedOrdinaryCategory TopCat.{v} M]
  (P : Presentation M) (hP : TensorLaws P) (O : TopologicalOperad.{w})

/-- Nullary action, transported continuously to the model's actual mapping
space from the unit. The transport is the fixed empty tensor comparison. -/
def unitEvaluation (X : M) (o : O.Op empty) :
    C(AlgebraOn P hP O X, MappingSpace (𝟙_ M) X) :=
  (⟨Endomorphism.nullaryHomeomorph P X,
    (Endomorphism.nullaryHomeomorph P X).continuous_toFun⟩ :
      C(P.Op X empty, MappingSpace (𝟙_ M) X)).comp
    (TopologicalOperad.nullaryEvaluation O (Endomorphism.operad P hP X) o)

/-- The path homotopy fiber over the given ordinary arrow, regarded as its
corresponding point in the actual enriched mapping space. -/
def strictUnitFiber (X : M) (o : O.Op empty) (q : 𝟙_ M ⟶ X) :
    TopCat.{max 1 (max v w)} :=
  KIP126.Topology.PathHomotopyFiber.space (unitEvaluation P hP O X o) (point q)

end KIP126.HigherAlgebra.Operad.EnrichedAlgebra
