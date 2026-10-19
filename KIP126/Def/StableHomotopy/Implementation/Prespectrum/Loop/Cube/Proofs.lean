module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open Topology
open scoped unitInterval

/-- Insert the last coordinate continuously into an actual cube. -/
theorem continuous_cube_snoc (r : ℕ) :
    Continuous (fun z : (Fin r → I) × I => (Fin.snoc z.1 z.2 : Fin (r+1) → I)) := by
  apply continuous_pi
  intro i
  induction i using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; fun_prop
  | cast j => simp only [Fin.snoc_castSucc]; fun_prop

end KIP126.StableHomotopy.Implementation.Prespectrum
