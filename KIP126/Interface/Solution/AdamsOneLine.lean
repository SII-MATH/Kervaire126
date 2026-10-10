import KIP126.Def.StageInput.StandardSphere.Classes.Family
import KIP126.Def.ClassicalAdams.SphereClasses.Products.Data
import KIP126.Def.SpectralSequence.Computation.Predicates
import KIP126.Def.StageInput.Milnor
import KIP126.Def.StageInput.StandardSphere.Sequence.Data

/-! Classical Hopf differentials on the fixed internal Adams tower.
The j=6 instance is used in MainPaper Lemma 7.16 (classical Massey/Toda
argument); j=4,5 also occur in the body’s tool examples. Introductory one-line
classification, full Hopf-survival classification and May’s low-dimensional
survival families are outside the current formalization scope.
This remaining declaration is an explicit literature-production obligation.
-/

namespace KIP126.Interface.Solution

open KIP126.Classical.Adams KIP126.Core.SpectralSequence

/-- For every j ≥ 4, the actual internal d₂ on hⱼ equals the specified
nonzero cobar product h₀ hⱼ₋₁². The target degree is retained explicitly. -/
theorem adamsOneLine_d2 (j : ℕ) (hj : 4 ≤ j) :
    HasNonzeroDifferential sphereAdamsData 2
      (1, ((2 ^ j : ℕ) : ℤ)) (3, ((1 + 2 ^ (j - 1 + 1) : ℕ) : ℤ))
      (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations j)
      (Sphere.Internal.h0HiSquare standardFoundation.hf2 standardMilnorCooperations (j - 1)) := by
  sorry

end KIP126.Interface.Solution
