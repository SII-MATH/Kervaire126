import KIP126.Def.ClassicalAdams.Tmf.CsvE2.Classes.Data
import KIP126.Def.StableHomotopy.Cohomology.Data
import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Data
import KIP126.Def.Synthetic.Sphere.Data
import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# A parameterized realization of the tmf coordinate input

The carrier is an explicitly supplied algebra object T, with its actual
multiplication and unit; the Hurewicz maps below are induced by that unit.
The comparison realizes the one fixed CSV algebra in the actual HF₂-Adams
tower of T. This file neither constructs topological modular forms nor
asserts that an arbitrary algebra object is tmf. A producer must supply the
chosen tmf realization and prove its coordinate comparison. The bounded
comparison does not assert a global Ext calculation. Compatibility with the
actual first-layer product and unit is stated separately in
`Model/Predicates.lean`; neither file asserts compatibility with higher pages.
-/

namespace KIP126.Classical.Adams.Tmf

noncomputable section
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The one unit used by every classical and synthetic comparison. -/
def unit (T : Mon C) : SphereSpectrum ⟶ T.X := MonObj.one

/-- Classical Hurewicz is postcomposition by that same algebra-object unit. -/
def hurewicz (T : Mon C) (n : ℤ) :
    HomotopyGroup n (SphereSpectrum : C) →+ HomotopyGroup n T.X :=
  inducedMap (unit T) n

/-- The actual E₂ map induced by the same unit on the HF₂-Adams towers. -/
def e2Hurewicz (H : Mod2EilenbergMacLane (C := C)) (T : Mon C) (p : ℤ × ℤ) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 p →ₗ[ℤ]
      (adamsTowerInternalSpectralSequence H.unit T.X).Page 2 p :=
  adamsInternalE2Induced H.unit (unit T) p

/-- Synthetic Hurewicz is induced by ν of that exact unit, on every bidegree. -/
def syntheticHurewicz {Syn : Type w} [SyntheticCategory.{w, v} Syn]
    (N : NuFunctorData C Syn) (T : Mon C) (p : ℤ × ℤ) :
    BiHom p.1 p.2 (N.functor.obj SphereSpectrum) →+
      BiHom p.1 p.2 (N.functor.obj T.X) :=
  Preadditive.rightComp (Smn p.1 p.2) (N.functor.map (unit T))

/-- A bounded coordinate comparison for an explicit tmf realization.
No named class is independently chosen: all are transported from the fixed
polynomial quotient. The comparison itself remains a model input. -/
structure E2Presentation (H : Mod2EilenbergMacLane (C := C)) (T : Mon C) where
  comparison : ∀ (s t : ℕ), t ≤ 261 →
    CsvE2.E2At s t ≃ₗ[ℤ]
      (adamsTowerInternalSpectralSequence H.unit T.X).Page 2 ((s : ℤ), (t : ℤ))

variable {H : Mod2EilenbergMacLane (C := C)} {T : Mon C}

/-- The fixed w₂² class, on this realization's actual internal E₂. -/
def E2Presentation.v2Sixteen (P : E2Presentation H T) :
    (adamsTowerInternalSpectralSequence H.unit T.X).Page 2 (16, 112) :=
  P.comparison 16 112 (by decide) CsvE2.v2Sixteen

/-- The fixed β⁵g class on the same actual internal E₂. -/
def E2Presentation.betaFiveG (P : E2Presentation H T) :
    (adamsTowerInternalSpectralSequence H.unit T.X).Page 2 (19, 114) :=
  P.comparison 19 114 (by decide) CsvE2.betaFiveG

/-- BR21's target transported through the very same E₂ comparison. -/
def E2Presentation.betaGFour (P : E2Presentation H T) :
    (adamsTowerInternalSpectralSequence H.unit T.X).Page 2 (19, 114) :=
  P.comparison 19 114 (by decide) CsvE2.betaGFour

/-- Coordinate transport respects the proved quotient identity; no new choice. -/
theorem E2Presentation.betaGFour_eq_betaFiveG (P : E2Presentation H T) :
    P.betaGFour = P.betaFiveG :=
  congrArg (P.comparison 19 114 (by decide)) CsvE2.betaGFour_eq_betaFiveG

end
end KIP126.Classical.Adams.Tmf
