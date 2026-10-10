import KIP126.Def.HigherAlgebra.Operad.StructureSpace.Predicates
import KIP126.Def.Topology.HomotopyFiber.Proofs

namespace KIP126.HigherAlgebra.Operad.TopologicalOperad

universe v w

variable {O : TopologicalOperad.{v}} {P : TopologicalOperad.{w}}

/-- The topology is induced along an injection: proof fields introduce no
extra choices beyond the actual family of component maps. -/
theorem Hom.app_injective : Function.Injective (fun f : Hom O P => f.app) := by
  intro f g h
  cases f
  cases g
  cases h
  rfl

/-- Evaluation is the actual component map, not an independently chosen map
from a putative space of structures. -/
@[simp] theorem evaluation_apply (I : FintypeCat.{0}) (x : O.Op I) (f : Hom O P) :
    evaluation O P I x f = f.app I x :=
  rfl

@[simp] theorem nullaryEvaluation_apply (o : O.Op (FintypeCat.of PEmpty))
    (f : Hom O P) : nullaryEvaluation O P o f = f.app (FintypeCat.of PEmpty) o :=
  rfl

end KIP126.HigherAlgebra.Operad.TopologicalOperad
