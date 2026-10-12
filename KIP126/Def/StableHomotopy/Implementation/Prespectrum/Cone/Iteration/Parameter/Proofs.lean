module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Parameter.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open scoped unitInterval

theorem continuous_coneIterationParameter :
    Continuous (fun z : I × I => coneIterationParameter z.1 z.2) := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] theorem coneIterationParameter_one (s : I) : coneIterationParameter s 1 = s := by
  apply Subtype.ext
  dsimp [coneIterationParameter]
  ring

@[simp] theorem coneIterationParameter_one_left (t : I) : coneIterationParameter 1 t = 1 := by
  apply Subtype.ext
  dsimp [coneIterationParameter]
  ring

end KIP126.StableHomotopy.Implementation.Prespectrum
