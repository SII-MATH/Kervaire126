import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.Data
import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Data

/-! The standard product on the *existing* internal sphere E₂ page.
It is cobar concatenation transported through the fixed Milnor coordinates.
No CSV multiplication operation or computation certificate is an input here.
Comparison with the tower pairing is a separate mathematical obligation. -/
namespace KIP126.Classical.Adams.Sphere.Internal
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- Multiplication of specified classes, not a free operation in a model. -/
def product {s t s' t' : ℕ}
    (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s, t))
    (y : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (s', t')) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2
      ((s + s' : ℕ), (t + t' : ℕ)) :=
  MilnorCohomology.comparison H M (s + s') (t + t')
    (MilnorCohomology.cup H M
      ((MilnorCohomology.comparison H M s t).symm x)
      ((MilnorCohomology.comparison H M s' t').symm y))
end
end KIP126.Classical.Adams.Sphere.Internal
