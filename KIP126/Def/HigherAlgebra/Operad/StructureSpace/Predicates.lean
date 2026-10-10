import KIP126.Def.HigherAlgebra.Operad.StructureSpace.Data
import Mathlib.Topology.Homotopy.Contractible

namespace KIP126.HigherAlgebra.Operad.TopologicalOperad

universe v w

/-- Contractibility of the explicitly defined strict nullary path fiber.
This is a condition, not a theorem. Interpreting it as uniqueness of derived
algebra structures requires a separate model and mapping-space comparison. -/
def HasContractibleNullaryStructureFiber (O : TopologicalOperad.{v})
    (P : TopologicalOperad.{w}) (o : O.Op (FintypeCat.of PEmpty))
    (q : P.Op (FintypeCat.of PEmpty)) : Prop :=
  ContractibleSpace (NullaryStructureFiber O P o q)

end KIP126.HigherAlgebra.Operad.TopologicalOperad
