module

public import KIP126.Def.ClassicalAdams.SphereClasses.Products.Data
public import KIP126.Def.StageInput.Milnor
public import KIP126.Def.StageInput.StandardSphere.Sequence.Data
public import KIP126.Def.SpectralSequence.Computation.API.Predicates

@[expose] public section


/-! Human-facing names for standard sphere differentials.  The definitions
expand to the actual spectral-sequence predicates, so they preserve page
representatives and degree transport.  The nonzero-target strengthening is
kept as a separate proposition. -/

namespace KIP126.Classical.Adams.StandardSphere

noncomputable section
open KIP126.Core.SpectralSequence

/-- The standard hᵢ class, with its bidegree computed from `i`. -/
noncomputable def standardHi (i : ℕ) :
    sphereAdamsData.Page 2 (1, ((2 ^ i : ℕ) : ℤ)) :=
  Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations i

/-- A list of indices denotes the corresponding product of standard `hᵢ` classes.
For example, `[0, 0, 3, 5]` denotes `h₀ h₀ h₃ h₅` in bidegree `(4, 42)`. -/
noncomputable def standardHProduct (indices : List ℕ)
    (hne : indices ≠ [] := by decide) :
    sphereAdamsData.Page 2
      (indices.length, ((Sphere.Internal.hWordDegree indices : ℕ) : ℤ)) :=
  Sphere.Internal.hMonomial standardFoundation.hf2 standardMilnorCooperations indices hne

/-- The standard h₀ hᵢ² class, with its bidegree computed from `i`. -/
noncomputable def standardH0HiSquare (i : ℕ) :
    sphereAdamsData.Page 2 (3, ((1 + 2 ^ (i + 1) : ℕ) : ℤ)) :=
  Sphere.Internal.h0HiSquare standardFoundation.hf2 standardMilnorCooperations i

/-- Readable alias for `standardHi 4`; no new class is introduced. -/
abbrev h4 : sphereAdamsData.Page 2 (1, 16) := standardHi 4

/-- Readable alias for `standardH0HiSquare 3`; no new class is introduced. -/
abbrev h0H3Sq : sphereAdamsData.Page 2 (3, 17) := standardH0HiSquare 3

/-- The standard one-line d₂ equation `d₂(h₄) = h₀ h₃²`. -/
def h4D2H0H3Sq : Prop :=
  Differential sphereAdamsData 2 h4 h0H3Sq

/-- The same equation together with the fact that its target is nonzero. -/
def h4D2H0H3SqNonzero : Prop :=
  NonzeroDifferential sphereAdamsData 2 h4 h0H3Sq

/-- The one-line d₂ equation using the uniform list-product notation. -/
def h4D2H033 : Prop :=
  Differential sphereAdamsData 2 (standardHProduct [4]) (standardHProduct [0, 3, 3])

end
end KIP126.Classical.Adams.StandardSphere
