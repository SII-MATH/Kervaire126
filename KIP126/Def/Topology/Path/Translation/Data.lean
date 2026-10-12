module

public import Mathlib.Topology.Homotopy.HSpaces
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

@[expose] public section

namespace KIP126.Topology
open scoped unitInterval
universe u v

/-- Left translation on the actual compact-open based loop space. -/
noncomputable def loopLeftTranslate {X : Type u} [TopologicalSpace X] {a : X}
    (p : Path a a) : C(Path a a,Path a a) :=
  ⟨fun q => p.trans q,Path.continuous_trans.comp (continuous_const.prodMk continuous_id)⟩

/-- The actual loop-space map induced by an arbitrary continuous map. -/
def continuousLoopMap {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (a : X) : C(Path a a,Path (f a) (f a)) :=
  ⟨fun p => p.map f.continuous,Path.continuous_uncurry_iff.mp (f.continuous.comp continuous_eval)⟩

end KIP126.Topology
