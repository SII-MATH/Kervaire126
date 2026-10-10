import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Int.Defs

/-! Adams grading conventions, independent of either spectral-sequence implementation. -/
namespace KIP126.Classical.Adams

abbrev Bidegree := ℤ × ℤ

/-- Classical Adams differentials increase the bidegree by `(r,r-1)`. -/
def classicalAdamsShape (r : ℤ) : ComplexShape Bidegree :=
  ComplexShape.up' (r, r - 1)

end KIP126.Classical.Adams
