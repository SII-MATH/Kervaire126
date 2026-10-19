module

public import KIP126.Def.Topology.Path.Translation.Data

@[expose] public section

namespace KIP126.Topology
universe u v

/-- Apply a continuous map to actual based loops with an explicitly
specified target basepoint and its proved preservation equation. -/
def continuousBasedLoopMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (a : X) (b : Y) (h : f a = b) : C(Path a a,Path b b) where
  toFun p := {
    toFun t := f (p t)
    continuous_toFun := f.continuous.comp p.continuous
    source' := (congrArg f p.source).trans h
    target' := (congrArg f p.target).trans h }
  continuous_toFun := Path.continuous_uncurry_iff.mp (f.continuous.comp continuous_eval)

end KIP126.Topology
