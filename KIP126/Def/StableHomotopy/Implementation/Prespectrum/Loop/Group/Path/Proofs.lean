module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open Topology
open scoped unitInterval
universe u v

/-- The usual associating homotopy is jointly continuous in all three paths. -/
theorem continuous_loopAssocFamily {T : Type u} [TopologicalSpace T]
    {X : Type v} [TopologicalSpace X] {a : X} (f g h : C(T, Path a a)) :
    Continuous (fun z : T × I => (Path.Homotopy.transAssoc (f z.1) (g z.1) (h z.1)).eval z.2) := by
  apply Path.continuous_uncurry_iff.mp
  change Continuous (fun z : (T × I) × I =>
    ((f z.1.1).trans ((g z.1.1).trans (h z.1.1))) _)
  fun_prop

/-- Contracting a path followed by its reverse is continuous in the path. -/
theorem continuous_loopCancelFamily {T : Type u} [TopologicalSpace T]
    {X : Type v} [TopologicalSpace X] {a : X} (f : C(T, Path a a)) :
    Continuous (fun z : T × I => (Path.Homotopy.reflTransSymm (f z.1)).eval z.2) := by
  apply Path.continuous_uncurry_iff.mp
  change Continuous (fun z : (T × I) × I => (f z.1.1) _)
  fun_prop

end KIP126.StableHomotopy.Implementation.Prespectrum
