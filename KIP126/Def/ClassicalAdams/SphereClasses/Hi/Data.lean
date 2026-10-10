import KIP126.Def.ClassicalAdams.SphereClasses.Data
import KIP126.Def.Steenrod.MilnorCobar.Hi.Proofs

/-! The standard `hᵢ` family on the actual sphere Adams second page. -/

namespace KIP126.Classical.Adams.Sphere

noncomputable section

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- The class of `[ξ₁^(2^i)]`, using the specified Milnor coordinates and the
actual first-page homology quotient of the sphere's Adams tower. -/
def hi (i : ℕ) :
    adamsPage H.unit SphereSpectrum 2 (by decide) 1 ((2 ^ i : ℕ) : ℤ) :=
  classOfMilnorCocycle H M 1 (2 ^ i) (KIP126.Steenrod.Milnor.hiCochain i)
    (KIP126.Steenrod.Milnor.hiCochain_isCycle i)

/-- The class of the concatenation square `[ξ₁^(2^i) | ξ₁^(2^i)]`, with
the same Milnor coordinates as `hi` and internal degree `2^(i+1)`. -/
def hiSquare (i : ℕ) :
    adamsPage H.unit SphereSpectrum 2 (by decide) 2 ((2 ^ (i + 1) : ℕ) : ℤ) :=
  classOfMilnorCocycle H M 2 (2 ^ (i + 1)) (KIP126.Steenrod.Milnor.hiSquareCochain i)
    (KIP126.Steenrod.Milnor.hiSquareCochain_isCycle i)

end

end KIP126.Classical.Adams.Sphere
