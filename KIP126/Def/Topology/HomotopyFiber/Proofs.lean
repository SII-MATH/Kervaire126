import KIP126.Def.Topology.HomotopyFiber.Data

namespace KIP126.Topology.PathHomotopyFiber

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The path starts at the image of the point in the source. -/
@[simp] theorem path_zero (f : C(X, Y)) (y : Y) (z : PathHomotopyFiber f y) :
    path f y z 0 = f (projection f y z) :=
  z.property.1

/-- The path ends at the chosen target point. -/
@[simp] theorem path_one (f : C(X, Y)) (y : Y) (z : PathHomotopyFiber f y) :
    path f y z 1 = y :=
  z.property.2

end KIP126.Topology.PathHomotopyFiber
