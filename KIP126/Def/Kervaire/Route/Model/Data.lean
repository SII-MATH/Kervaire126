import KIP126.Def.Kervaire.Route.Labels.Data
import KIP126.Def.Kervaire.Route.Objects.Data
import KIP126.Def.ClassicalAdams.Detection.Convergence.Data
import KIP126.Def.Synthetic.Detection.Predicates
import KIP126.Def.Synthetic.AdamsSequence.Maps.Data
import KIP126.Def.Synthetic.Sphere.Actions.Data
import KIP126.Def.Synthetic.Context.Coherence.Predicates
import KIP126.Def.Synthetic.Localization.Recovery.Data
import KIP126.Def.Comparison.ClassicalSynthetic.FirstQuotient.Data
import KIP126.Def.Comparison.ClassicalSynthetic.FirstQuotient.Restricted.Data
import KIP126.Def.Synthetic.QuotientTower.Predicates
import KIP126.Def.Synthetic.NormalizedMap.Data
import KIP126.Def.ClassicalAdams.Suspension.Predicates
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-! Shared objects for the Section 7 proof route. This is data, not a claim
that the literature/computation inputs hold. In particular it has no C₃/C₄/C₅,
specified differential, permanent-cycle, or Proposition 7.8/7.9 field.
Model compatibility is recorded separately in `Model/Predicates`; data alone
must not be advertised as the completed frozen M interface. -/
namespace KIP126.Kervaire.Route
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Comparison.ClassicalSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- One choice of objects and comparison data for the entire route.
Convergence is requested on the selected object closure, including Cν and the detector.
The E₂ comparison is a graded comparison, NOT a map of classical sequences:
such a map would lose the synthetic λ-torsion information. -/
structure ModelData (H : Mod2EilenbergMacLane (C := C)) (Syn : Type w)
    [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)] where
  nu : NuFunctorData C Syn
  family : SyntheticAdamsFamily Syn
  recovery : LambdaRecovery nu
  /-- Exact structure used by Toda brackets, rotations and the octahedron. -/
  classicalTriangulated : CategoryTheory.IsTriangulated C
  syntheticTriangulated : CategoryTheory.IsTriangulated Syn
  shiftAdditive : ∀ p, (SyntheticCategory.biShift (Syn := Syn) p).Additive
  shiftCommShift : ∀ p, (SyntheticCategory.biShift (Syn := Syn) p).CommShift ℤ
  shiftExact : ∀ p, letI := shiftCommShift p;
    (SyntheticCategory.biShift (Syn := Syn) p).IsTriangulated
  realizationShift : recovery.realization.CommShift ℤ
  realizationExact : letI := realizationShift; recovery.realization.IsTriangulated
  shiftCoherence : BiShiftCoherence Syn
  quotientFunctoriality : LambdaQuotientFunctoriality (Syn := Syn)
  firstQuotient : ∀ X : C, FirstQuotientHomotopyComparison H nu X
  quotientTower : ∀ X : Syn, FiniteLambdaQuotientTower X
  auxiliary : AuxiliaryData C
  /-- One convergence choice throughout the selected object closure. -/
  convergence : ∀ X : SyntheticObject,
    TowerConvergence (nuCoefficientUnit H.unit nu) family (X.obj nu auxiliary)
  classicalConvergence : ∀ X : ClassicalObject,
    KIP126.Classical.Adams.TowerDetection.Convergence H.unit (X.obj auxiliary)
  classicalSuspension : ∀ X : ClassicalObject,
    KIP126.Classical.Adams.Suspension.TowerComparison H (X.obj auxiliary)
  /-- Comparisons needed by the normalized maps and the Cν calculation.
  The same comparison is fixed for all quotients and all extension lengths. -/
  nuE2 : ∀ (X : ClassicalObject) (a s t : ℤ) (k : ℕ),
    E2 H (X.obj auxiliary) s t ≃ₗ[ℤ]
      (family.obj ((SyntheticCategory.biShift (0, a)).obj
        (nu.functor.obj (X.obj auxiliary)))).E₂ (s, t, t + a - k)
  /-- One normalized lift per actual map; later pages use its actual λ
  quotients. These lifts carry their factorization through νf. -/
  normalizedMap : ∀ (X Y : ClassicalObject) (f : X.obj auxiliary ⟶ Y.obj auxiliary),
    NormalizedSyntheticMap H nu f
  /-- λᵏ x lives in degree (s,t,t-k). Agreement with the first quotient,
  tower realization and λ action is a separate structural obligation. -/
  sphereE2 : ∀ (s t : ℤ) (k : ℕ),
    E2 H SphereSpectrum s t ≃ₗ[ℤ] (family.sphere).E₂ (s, t, t - k)

namespace ModelData
variable {H : Mod2EilenbergMacLane (C := C)} (D : ModelData H Syn)

abbrev sphereConvergence := D.convergence .sphere

abbrev quotientConvergence (n : ℕ) (_hn : 0 < n) :=
  D.convergence (.quotient n .sphere)

def sphereFirstQuotient : SphereFirstQuotientComparison H Syn :=
  sphereFirstQuotientOfLambdaFunctor H D.nu D.quotientFunctoriality
    (D.firstQuotient SphereSpectrum)

/-- The quotient label is induced by the actual quotient projection in the
same functor. It is never selected independently of the sphere label. -/
def quotientLabel (n : ℕ) (s t : ℤ) (k : ℕ) (x : E2 H SphereSpectrum s t) :
    (D.family.obj (XModLambdaN (S_0_0 : Syn) n)).E₂ (s, t, t - k) :=
  familyPageMap D.family (XModLambdaN.incl S_0_0 n) 2 (s, t, t - k)
    (D.sphereE2 s t k x)
end ModelData
end
end KIP126.Kervaire.Route
