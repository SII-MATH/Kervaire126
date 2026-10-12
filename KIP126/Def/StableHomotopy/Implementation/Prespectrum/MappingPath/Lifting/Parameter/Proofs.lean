module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Lifting.Parameter.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open scoped unitInterval

@[simp] theorem mappingPathLiftFirst_zero (t : I) : mappingPathLiftFirst (0,t) = t := by
  apply Subtype.ext
  simp [mappingPathLiftFirst,min_eq_left t.property.2]

@[simp] theorem mappingPathLiftFirst_start (s : I) : mappingPathLiftFirst (s,0) = 0 := by
  apply Subtype.ext
  simp [mappingPathLiftFirst]

@[simp] theorem mappingPathLiftSecond_end (s : I) : mappingPathLiftSecond (s,1) = s := by
  apply Subtype.ext
  simp [mappingPathLiftSecond,max_eq_left s.property.1]

theorem mappingPathLiftFirst_join (s t : I) (h : (1+(s : ℝ))*(t : ℝ) = 1) :
    mappingPathLiftFirst (s,t) = 1 := by
  apply Subtype.ext
  simp [mappingPathLiftFirst,h]

theorem mappingPathLiftSecond_join (s t : I) (h : (1+(s : ℝ))*(t : ℝ) = 1) :
    mappingPathLiftSecond (s,t) = 0 := by
  apply Subtype.ext
  simp [mappingPathLiftSecond,h]

end KIP126.StableHomotopy.Implementation.Prespectrum
