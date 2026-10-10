import KIP126.Def.HigherAlgebra.Operad.Topological.Data
import KIP126.Def.Topology.HomotopyFiber.Data

/-!
The space of strict maps between two fixed topological operads. Its topology
is induced by the component maps into the product, over all finite input
sets, of compact-open continuous-map spaces. The operadic equations select
the subspace of compatible components.

Evaluation at a fixed nullary operation is a continuous map. Its path
homotopy fiber at a fixed target operation records both a strict operad map
and a path from its nullary value to that operation. This is a point-set
construction for arbitrary target operads; it does not assert that this
strict map space or its fiber computes a derived operadic structure space.
-/

namespace KIP126.HigherAlgebra.Operad.TopologicalOperad

universe v w

instance Hom.instTopologicalSpace (O : TopologicalOperad.{v})
    (P : TopologicalOperad.{w}) : TopologicalSpace (Hom O P) :=
  TopologicalSpace.induced (fun f : Hom O P => f.app) inferInstance

/-- Strict operad maps with the topology induced by the product of their
compact-open component mapping spaces. -/
def homSpace (O : TopologicalOperad.{v}) (P : TopologicalOperad.{w}) :
    TopCat.{max 1 (max v w)} :=
  TopCat.of (Hom O P)

/-- Evaluation at one fixed operation in one fixed arity. No local compactness
of the operation space is needed for evaluation at a fixed point. -/
def evaluation (O : TopologicalOperad.{v}) (P : TopologicalOperad.{w})
    (I : FintypeCat.{0}) (x : O.Op I) : C(Hom O P, P.Op I) where
  toFun f := f.app I x
  continuous_toFun := (continuous_eval_const x).comp
    ((continuous_apply I).comp continuous_induced_dom)

/-- Evaluate a strict operad map on the specified nullary operation. -/
def nullaryEvaluation (O : TopologicalOperad.{v}) (P : TopologicalOperad.{w})
    (o : O.Op (FintypeCat.of PEmpty)) :
    C(Hom O P, P.Op (FintypeCat.of PEmpty)) :=
  evaluation O P (FintypeCat.of PEmpty) o

/-- The actual path homotopy fiber of nullary evaluation. By unfolding, its
points are pairs in `Hom O P × C(unitInterval, P.Op empty)` satisfying the
two endpoint equations, with the product-subspace topology. It is not a
strict equality fiber or a disjoint union with discrete operad-map index. -/
abbrev NullaryStructureFiber (O : TopologicalOperad.{v})
    (P : TopologicalOperad.{w}) (o : O.Op (FintypeCat.of PEmpty))
    (q : P.Op (FintypeCat.of PEmpty)) :=
  KIP126.Topology.PathHomotopyFiber (nullaryEvaluation O P o) q

/-- The path fiber of nullary evaluation, bundled with its actual topology. -/
def nullaryStructureFiberSpace (O : TopologicalOperad.{v})
    (P : TopologicalOperad.{w}) (o : O.Op (FintypeCat.of PEmpty))
    (q : P.Op (FintypeCat.of PEmpty)) : TopCat.{max 1 (max v w)} :=
  KIP126.Topology.PathHomotopyFiber.space (nullaryEvaluation O P o) q

end KIP126.HigherAlgebra.Operad.TopologicalOperad
