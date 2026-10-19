module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open Topology
open scoped unitInterval

/-- The initial-path parameter in the variable-length concatenation. -/
def mappingPathLiftFirst : C(I × I,I) where
  toFun z := ⟨min ((1+(z.1 : ℝ))*(z.2 : ℝ)) 1, by
    constructor
    · exact le_min (mul_nonneg (by linarith [z.1.property.1]) z.2.property.1) zero_le_one
    · exact min_le_right _ _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.add continuous_fst.subtype_val).mul
      continuous_snd.subtype_val).min continuous_const

/-- The newly traversed base-homotopy parameter. -/
def mappingPathLiftSecond : C(I × I,I) where
  toFun z := ⟨max (((1+(z.1 : ℝ))*(z.2 : ℝ))-1) 0, by
    constructor
    · exact le_max_right _ _
    · apply max_le
      · nlinarith [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]
      · exact zero_le_one⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_const.add continuous_fst.subtype_val).mul
      continuous_snd.subtype_val).sub continuous_const).max continuous_const

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

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

end
