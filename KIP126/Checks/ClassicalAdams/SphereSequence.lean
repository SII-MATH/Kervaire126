import KIP126.Def.ClassicalAdams.Convergence.Proofs
import KIP126.Def.SpectralSequence.PageLevel.Proofs
import KIP126.Def.ClassicalAdams.SphereSequence.Data

/-!
# Regression checks for classical Adams pages and sphere multiplication

The checks cover page numbering, Mathlib page passage, spectrum-bound
convergence, and the algebraic laws of a chosen sphere presentation.
-/

namespace KIP126.Classical.Adams.Regression

open CategoryTheory
open KIP126.Core.SpectralSequence

example : classicalAdamsPageLevel.firstPage = 2 := rfl
example : classicalAdamsPageLevel.admissibleFrom = 2 := rfl
example (r : ℕ) : classicalAdamsPageLevel.page r = r := rfl
example (r : ℕ) : classicalAdamsPageLevel.cycleLevel r = (r : ℤ) - 1 := rfl
example (r : ℕ) :
    classicalAdamsPageLevel.cycleLevel r =
      classicalAdamsPageLevel.quotientExponent r :=
  classicalAdamsPageLevel.cycleLevel_eq_quotientExponent r
example (r : ℕ) (h : 2 ≤ r) :
    classicalAdamsPageLevel.admissibleFrom ≤ classicalAdamsPageLevel.page r :=
  classicalAdamsPageLevel.page_ge h

example {G : CategoryTheory.GradedObject ℤ AddCommGrpCat}
    (F : KIP126.Core.Algebra.Filtration G)
    (hF : F.IsEventuallyZero) :
    IsAdamsFiltrationSeparated F :=
  isAdamsFiltrationSeparated_of_eventuallyZero F hF

variable {stable : StableHomotopyContext}
  {A : ClassicalAdamsSS stable stable.sphere}

example (b : Bidegree) :
    classicalAdamsTarget AdamsPage.two b = (b.1 + 2, b.2 + 1) := by
  simpa using classicalAdamsTarget_two b

example (b : Bidegree) :
    (classicalAdamsShape 2).Rel b (classicalAdamsTarget AdamsPage.two b) :=
  classicalAdamsShape_two_rel b

example (b : Bidegree) :
    (A.E₂).homology b ≅ (A.E₃).X b :=
  A.e₂ToE₃ b

/-! ### Spectrum-bound strong convergence -/

variable {π₂ : TwoCompleteStableHomotopy stable} {X : stable.Spectrum}
  (system : SpectrumBoundClassicalAdamsSS π₂ X)

example : KIP126.Core.Algebra.Filtration (π₂.groups X) :=
  system.strongConvergence.filtration

example : system.strongConvergence.filtration.IsExhaustive :=
  system.strongConvergence.exhaustive

example : IsAdamsFiltrationSeparated system.strongConvergence.filtration :=
  system.strongConvergence.separated

example (b : Bidegree) (r : ℤ)
    (hr : system.strongConvergence.stablePage b ≤ r) :
    UnderlyingAdamsPage system.pageSlice.sequence r
        ((system.strongConvergence.stablePage_ge_two b).trans hr) b ≅
      system.strongConvergence.filtration.associatedGraded b.1 (adamsStem b) :=
  system.strongConvergence.pageComparison b r hr

/-! ### Lawful sphere multiplication -/

variable {sphereSystem : SpectrumBoundClassicalAdamsSS π₂ stable.sphere}

example (P : SphereAdamsPresentation sphereSystem.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P)
    (a b : Bidegree) (x x' : (sphereSystem.pageSlice.E₂).X a)
    (y : (sphereSystem.pageSlice.E₂).X b) :
    algebra.productMap a b (x + x') y =
      algebra.productMap a b x y + algebra.productMap a b x' y := by
  simp

example {smashSphere : ClassicalAdamsSS stable
      (stable.smash stable.sphere stable.sphere)}
    (P : SphereAdamsPresentation sphereSystem.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P)
    (pairing : ExternalAdamsPairing sphereSystem.pageSlice
      sphereSystem.pageSlice smashSphere)
    (pairingLaws : ExternalAdamsPairingLaws pairing)
    (compatibility : SphereAdamsExternalCompatibility algebra pairing pairingLaws)
    (a b : Bidegree) (x : (sphereSystem.pageSlice.E₂).X a)
    (y : (sphereSystem.pageSlice.E₂).X b) :
    algebra.productMap a b x y =
      (compatibility.smashToSphere (a + b)).hom
        (pairingLaws.pairMap a b x y) :=
  compatibility.product_eq_external a b x y

end KIP126.Classical.Adams.Regression
