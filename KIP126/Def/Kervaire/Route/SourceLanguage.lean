import KIP126.Def.Comparison.Interfaces
import KIP126.Def.ClassicalAdams.Convergence.BHS.Predicates
import KIP126.Def.ClassicalAdams.SphereVanishing.Predicates
import KIP126.Def.Synthetic.EInfty.Presentation.Predicates
import KIP126.Def.SpectralSequence.Computation.State.Predicates
import KIP126.Def.SpectralSequence.Computation.Predicates
import KIP126.Def.Comparison.ClassicalSynthetic.Data
import KIP126.Def.Comparison.ClassicalSynthetic.FirstQuotient.Data
import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Internal.Data
import KIP126.Def.ClassicalAdams.SphereClasses.Products.Data
import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.CycleMap.Data
import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Data
import KIP126.Def.Kervaire.Theta5.Predicates
import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates
import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Window.Data
import KIP126.Def.Synthetic.EInfty.Shift.Predicates
import KIP126.Def.Synthetic.PageExtension.Ambiguity.Predicates
import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Top.Data
import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Top.Equivalence.Data
import KIP126.Def.ClassicalAdams.Suspension.Predicates
import KIP126.Def.Synthetic.PageExtension.Crossing.Predicates
import KIP126.Def.Synthetic.PageExtension.Solutions.Data
import KIP126.Def.Synthetic.PageExtension.Solutions.Permanent.Data
import KIP126.Def.Synthetic.ExtensionSS.Square.Construction.Data
import KIP126.Def.ClassicalAdams.Moss.Statement.Predicates
import KIP126.Def.ClassicalAdams.Tmf.Model.Data
import KIP126.Def.ClassicalAdams.Tmf.Model.Predicates
import KIP126.Def.ClassicalAdams.SphereMultiplication.Data
import KIP126.Def.Steenrod.MilnorExt.Resolution.Data
import KIP126.Def.Synthetic.Bockstein.Hom.Data
import KIP126.Def.Synthetic.QuotientFunctor.Data
import KIP126.Def.ClassicalAdams.Convergence.Tower.Predicates
import KIP126.Def.ClassicalAdams.Completion.Predicates
import KIP126.Def.Kervaire.Route.Extensions.Data
import KIP126.Def.Kervaire.Route.Hopf.Data
import KIP126.Def.Kervaire.Route.Conditions.Predicates
import KIP126.Def.Kervaire.Route.Massey.Predicates
import KIP126.Def.Kervaire.Route.Toda.Predicates
import KIP126.Def.Synthetic.Computation.Predicates
import KIP126.Def.Kervaire.Route.Labels.Tmf.Data
import Mathlib.CategoryTheory.Adjunction.Additive
import KIP126.Def.Kervaire.Route.Multiplication.Comparison
import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Data
import KIP126.Def.StableHomotopy.FiniteType.Predicates
import Mathlib.CategoryTheory.Monoidal.Mon
import KIP126.Def.Kervaire.Route.Triangles.Predicates
import KIP126.Def.Comparison.ClassicalSynthetic.RealizationWeights.Data
import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.Route.Data
import KIP126.Def.StableHomotopy.Implementation.Data

/-! Mathematical language for source comparisons on one actual route model.

The operations below use the chosen functors, towers, coordinate maps and
products. Predicate declarations describe exact properties; they assert none
of those properties. Accepted source-result packages and the A(M)/C(M) delivery
contracts remain in Interface/Challenge/Challenge2. The historical namespace
is retained to keep existing consumers definitionally unchanged.
-/

namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- Pstrągowski/BHS lifting and triangle conditions use this very ν.
This is the existing precise source interface, not a new assumed theorem. -/
abbrev SyntheticLiftInput := KIP126.Synthetic.SyntheticInterface H D.nu

/-- BHS A.9/A.11 formula data, with actual classical cycle/boundary quotients.
Their λ/ρ compatibility must accompany any supplied presentation. -/
abbrev EInftyFormulaInput := KIP126.Synthetic.SpectralSequence.SyntheticEInftyPresentation H D.nu D.family
abbrev EInftyCompatibilityInput (P : EInftyFormulaInput D)
    (S : EInftyWeightShift D.family) :=
  KIP126.Synthetic.SpectralSequence.SyntheticEInftyMapCompatibility H D.nu D.family P S
    (fun X => D.quotientTower (D.nu.functor.obj X))

/-- An E∞ formula must preserve the actual E₂ labels, in addition to
commuting with λ/ρ. This prevents supplying unrelated quotient isomorphisms.
Both finite and infinite formulas retain all classical boundary ambiguity. -/
def EInftyLabelAgreement (P : EInftyFormulaInput D) : Prop :=
  (∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ)
      (k : ℕ) (hk : k < q)
      (x : PageRepresentatives.cycles H (X.obj D.auxiliary)
        ((q : ℤ) - p.2 + (p.2 - k)) p)
      (e : ((D.family.nuQuotient D.nu (X.obj D.auxiliary) q).sequence.ssData
        (p.1,p.2,p.2-k)).eInfty),
    HasInfinityRepresentative _ 2 _ (finiteTargetLabel D X q p.1 p.2 k x.val) e ↔
      P.finiteWindow (X.obj D.auxiliary) q hq p (p.2-k) (by constructor <;> omega) e =
        KIP126.Algebra.NestedQuotient.projection _ _ x) ∧
  (∀ (X : ClassicalObject) (p : ℤ × ℤ) (k : ℕ)
      (x : PageRepresentatives.permanentCycles H (X.obj D.auxiliary) p)
      (e : ((D.family.nu D.nu (X.obj D.auxiliary)).sequence.ssData
        (p.1,p.2,p.2-k)).eInfty),
    HasInfinityRepresentative _ 2 _ (targetNuLabel D X p.1 p.2 k x.val) e ↔
      P.nuWindow (X.obj D.auxiliary) p (p.2-k) (by omega) e =
        KIP126.Algebra.NestedQuotient.projection _ _ x)

/-- BHS A.8 / LWX Theorem 3.6: the source λᵏx and target
λ^(k+r-1)y have the same weight. This is a law to supply from A(M), not a
map from the entire classical sequence to every synthetic weight. -/
def DifferentialLiftInput : Prop :=
  ∀ (X : ClassicalObject) (a s t : ℤ) (r k : ℕ), 2 ≤ r →
    ∀ (x : E2 H (X.obj D.auxiliary) s t)
      (y : E2 H (X.obj D.auxiliary) (s + r) (t + r - 1)),
    KIP126.Core.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence H.unit (X.obj D.auxiliary)) r
      (s,t) (s+r,t+r-1) x y →
    KIP126.Synthetic.SpectralSequence.HasDifferential
      (D.family.obj ((SyntheticCategory.biShift (0,a)).obj
        (D.nu.functor.obj (X.obj D.auxiliary)))) r
      (s,t,t+a-k) (s+r,t+r-1,(t+r-1)+a-(k+(r-1) : ℕ))
      (D.nuE2 X a s t k x) (D.nuE2 X a (s+r) (t+r-1) (k+(r-1)) y)

/-- Bind the geometric Hopf maps used by the tools to standard classes
and to the actual synthetic η used in C₅. These are explicit literature
identifications, not consequences inferred merely from the maps' names. -/
def HopfBindings (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  TowerDetection.Detects (D.classicalConvergence .sphere) (1,2)
    (Sphere.Internal.hi H M 1) D.auxiliary.etaMap ∧
  TowerDetection.Detects (D.classicalConvergence .sphere) (1,4)
    (Sphere.Internal.hi H M 2) D.auxiliary.nuMap ∧
  ∃ he : normalizedExponent H D.auxiliary.etaMap = 1,
    η = (etaSourceIso D he).hom ≫
      (D.normalizedMap (.shift 1 .sphere) .sphere D.auxiliary.etaMap).map ≫ D.nu.unitIso.hom

/-- The original distinguished-choice BX condition, before the LWX
normalization and arbitrary-choice deductions. BX Proposition 7.19. -/
abbrev BXInput (η : BiHom 1 2 (S_0_0 : Syn)) (θ : BiHom 62 64 (S_0_0 : Syn)) :=
  BJMOriginalCriterion H M D.sphereFirstQuotient η θ

/-- The actual Hurewicz map for the selected detector. In the chosen route
A(M) identifies its object/unit with tmf and supplies the required results. -/
noncomputable def detectorMap : (S_0_0 : Syn) ⟶ D.nu.functor.obj D.auxiliary.detector :=
  D.nu.unitIso.inv ≫ D.nu.functor.map D.auxiliary.detectorUnit

/-- Actual order-two statement used before Moss; no presentation of π₆₂
as an unrelated abstract group is substituted. Xu/IWX, cited by LWX 7.16. -/
def OrderTwo62 : Prop :=
  ∀ α : HomotopyGroup (C := C) 62 SphereSpectrum, α + α = 0

/-- The local sphere form of the Moss implication needed in LWX Lemma 7.16.
Source: Moss Theorem 1.2; crossing convention also IWX Definition 2.15 and
Theorem 2.16. No claim of zero indeterminacy is hidden in the conclusion:
there exists a permanent defining-system value detecting a bracket member.
The three detection and two null-composition hypotheses are explicit. -/
def ThetaBMossInput : Prop :=
  ∀ (B : E2 H SphereSpectrum 8 70)
    (θ β : HomotopyGroup (C := C) 62 SphereSpectrum)
    (two : HomotopyGroup (C := C) 0 SphereSpectrum),
    two = (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ (2 • 𝟙 _) →
    TowerDetection.Detects (D.classicalConvergence .sphere) (2,64)
      (Sphere.Internal.hiSquare H M 5) θ →
    TowerDetection.Detects (D.classicalConvergence .sphere) (1,1)
      (Sphere.Internal.hi H M 0) two →
    TowerDetection.Detects (D.classicalConvergence .sphere) (8,70) B β →
    θ + θ = 0 → β + β = 0 →
    (ThetaBMassey M B).Nonempty →
    ¬ SphereMossCrossing (H := H) 3 (3,65) →
    ¬ SphereMossCrossing (H := H) 3 (9,71) →
    TowerDetection.ResidualInjectivity H.unit (SphereSpectrum (C := C)) →
    ∃ (z : E2 H SphereSpectrum 9 134)
      (ξ : HomotopyGroup (C := C) 125 SphereSpectrum),
      ThetaBMasseyDefiningSystem M B z ∧
      TowerDetection.Detects (D.classicalConvergence .sphere) (9,134) z ξ ∧
      ThetaBToda θ β ξ
end KIP126.Literature.Route


/-! Classical literature inputs on the frozen route's actual Adams tower.
These are explicit hypotheses, not instances or proved theorems. See
`docs/STAGE0_INTERFACES.md` for source locators and the scope of this package. -/
namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- A classical θ₅ means detection by the standard Milnor square, on D's
classical convergence. It is not identified with a CSV coordinate. -/
def ClassicalTheta (θ : HomotopyGroup (C := C) 62 SphereSpectrum) : Prop :=
  TowerDetection.Detects (D.classicalConvergence .sphere) (2,64)
    (Sphere.Internal.hiSquare H M 5) θ

/-- BJM (1984), or Xu Corollary 1.3: an order-two θ₅ exists.
The nonzero-survival clause prevents a zero representative from fulfilling
existence merely because `Detects` permits a zero associated-graded class. -/
def Theta5Existence : Prop :=
  NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
    (2,64) (Sphere.Internal.hiSquare H M 5) ∧
  ∃ θ, ClassicalTheta D θ ∧ θ + θ = 0

/-- IWX's classical 62-stem computation: every element has exponent two.
Xu's existence of ONE order-two θ₅ alone does not imply this assertion. -/
abbrev Stem62ExponentTwo := KIP126.Literature.Route.OrderTwo62 (C := C)

/-- The exact part of IWX's Adams filtration calculation used in LWX
Lemma 7.10: two classical h₅²-detected choices differ in filtration ≥ 6.
This is a consequence of the PREVIOUSLY published 62-stem computation,
not the synthetic choice-independence lemma proved in the present paper. -/
def Theta5FiltrationGap : Prop :=
  ∀ θ θ' : HomotopyGroup (C := C) 62 SphereSpectrum,
    ClassicalTheta D θ → ClassicalTheta D θ' →
    θ - θ' ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 6 62

/-- Detection of the actual degree-zero multiplication-by-two map. Source:
the classical Adams 0-stem, with h₀ the standard Milnor generator. -/
def TwoDetection : Prop :=
  TowerDetection.Detects (D.classicalConvergence .sphere) (1,1)
    (Sphere.Internal.hi H M 0)
    ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ (2 • 𝟙 _))

/-- Adams' Hopf classes, including identification of the selected synthetic
η with the SAME normalized geometric η map. The equality is a model/source
comparison obligation; the name of `etaMap` alone proves nothing. -/
def HopfInput (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  EtaChoice M D.toModelData η ∧ KIP126.Literature.Route.HopfBindings D η ∧
  NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
    (1,2) (Sphere.Internal.hi H M 1) ∧
  NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
    (1,4) (Sphere.Internal.hi H M 2)

end KIP126.Literature.Route


namespace KIP126.Literature.Route
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.Kervaire KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- BX Proposition 7.19 and its proof, at ONE common source choice.
All three clauses use that same θ₅ and the η fixed in `ClassicalInputs`.
The original finite formula uses ηθ₅² modulo λ^r. The total-boundary formula
and the untruncated iff are explicitly in the proof of BX Proposition 7.19.
The LWX normalization to ληθ₅² modulo λ^(r+1), and extension to arbitrary
choices, remain paper deductions; they are deliberately absent here. -/
def BXDistinguishedInput (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  ∃ θ : BiHom 62 64 (S_0_0 : Syn),
    BJMOriginalCriterion H M D.sphereFirstQuotient η θ ∧
    BJMSourceTotalBoundaryIdentity H M D.sphereFirstQuotient η θ ∧
    BJMUntruncatedCriterion H M η θ
end KIP126.Literature.Route


/-! BHS/Pstrągowski source statements on the frozen ν and sequence family.
Finite quotient assertions retain their more general scope. Untruncated BHS
results retain the source object's completeness and convergence hypotheses;
actual completion maps and internal image/divisibility reflection transport
them to the selected ordinary objects. -/
namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

abbrev nuZero (X : ClassicalObject) :=
  (SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj (X.obj D.auxiliary))

/-- The fixed first-quotient label, only rewriting t+0=t. -/
def firstLabel (X : ClassicalObject) (s t : ℤ) (x : E2 H (X.obj D.auxiliary) s t) :
    BiHom (t-s) t (XModLambdaN (nuZero D X) 1) := by
  simpa using (D.firstQuotient (X.obj D.auxiliary) 0 s t).symm x

/-- Reindex the ACTUAL δ_(q,q+1) from D's quotient tower. -/
def bocksteinArrow (X : ClassicalObject) (q : ℕ) (hq : 0 < q) :
    XModLambdaN (nuZero D X) q ⟶
      (SyntheticCategory.biShift (1,-(q : ℤ))).obj (XModLambdaN (nuZero D X) 1) :=
  ((D.quotientTower (nuZero D X)).triangle hq (Nat.lt_succ_self q)).delta ≫
    (SyntheticCategory.biShift_compat (Syn := Syn) 1).inv.app _ ≫
    (SyntheticCategory.biShift_comp (0,-(q : ℤ)) (1,0)).hom.app _ ≫
    eqToHom (by congr 1 <;> simp)

/-- Bockstein target in classical E₂. Its bidegree is (s+q+1,t+q),
so this represents d_(q+1), not an extension differential of stem zero. -/
def bocksteinLabel (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (nuZero D X) q)) :
    E2 H (X.obj D.auxiliary) (s+q+1) (t+q) := by
  let b : BiHom (t-s-1) (t+q) (XModLambdaN (nuZero D X) 1) :=
    (susp_invariance (t-s-1) (t+q) 1 (-(q : ℤ)) _).symm
      (homotopyRegrade (by omega) (by omega) (a ≫ bocksteinArrow D X q hq))
  exact D.firstQuotient (X.obj D.auxiliary) 0 (s+q+1) (t+q)
    (homotopyRegrade (by omega) (by omega) b)

/-- BHS Theorem A.1(1): vanishing through d_q iff a lift to νX/λ^q
exists. Membership in Z_q permits a boundary or zero label; `SurvivesTo`
would incorrectly demand nonzero. All restrictions are D's actual ρ. -/
def FiniteLiftCriterion : Prop :=
  ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t),
    (x ∈ PageRepresentatives.cycles H (X.obj D.auxiliary) q (s,t) ↔
      ∃ a : BiHom (t-s) t (XModLambdaN (nuZero D X) q),
        a ≫ (D.quotientTower (nuZero D X)).rho 1 q hq = firstLabel D X s t x)

/-- BHS A.1(1c): choose a lift whose boundary represents the differential.
The target is stated modulo the ACTUAL classical page boundaries by
`HasDifferential`; an arbitrary lift need not have this property. The sign
in BHS disappears in the mod-2 E₂ group, not in integral homotopy groups. -/
def BocksteinDifferential : Prop :=
  ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t),
    x ∈ PageRepresentatives.cycles H (X.obj D.auxiliary) q (s,t) →
    ∃ a : BiHom (t-s) t (XModLambdaN (nuZero D X) q),
      a ≫ (D.quotientTower (nuZero D X)).rho 1 q hq = firstLabel D X s t x ∧
      KIP126.Core.SpectralSequence.HasDifferential
        (adamsTowerInternalSpectralSequence H.unit (X.obj D.auxiliary))
        (q+1) (s,t) (s+q+1,t+q) x (bocksteinLabel D X q hq s t a)

/-- BHS A.1(2): lift a permanent cycle through the untruncated νX.
This is not an assertion that every E₂ label is a permanent cycle. -/
def PermanentLiftCriterion : Prop :=
  ∀ (X : ClassicalObject) (s t : ℤ) (x : E2 H (X.obj D.auxiliary) s t),
    (x ∈ PageRepresentatives.permanentCycles H (X.obj D.auxiliary) (s,t) ↔
      ∃ a : BiHom (t-s) t (nuZero D X),
        quotientClass 1 a = firstLabel D X s t x)

/-- BHS A.8, including the converse on labeled representatives.
These are the existing differentials on the same family, not a newly
postulated differential function. Multiplication by λ changes weight only. -/
def DifferentialRigidity : Prop :=
  ∀ (X : ClassicalObject) (a s t : ℤ) (r k : ℕ), 2 ≤ r →
    ∀ (x : E2 H (X.obj D.auxiliary) s t)
      (y : E2 H (X.obj D.auxiliary) (s+r) (t+r-1)),
    (KIP126.Core.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence H.unit (X.obj D.auxiliary)) r
      (s,t) (s+r,t+r-1) x y ↔
    KIP126.Synthetic.SpectralSequence.HasDifferential
      (D.family.obj ((SyntheticCategory.biShift (0,a)).obj
        (D.nu.functor.obj (X.obj D.auxiliary)))) r
      (s,t,t+a-k) (s+r,t+r-1,(t+r-1)+a-(k+(r-1) : ℕ))
      (D.nuE2 X a s t k x) (D.nuE2 X a (s+r) (t+r-1) (k+(r-1)) y))

/-- Selected-model consequence of λ-localization: only the objects in
`SyntheticObject` and their displayed bidegrees are quantified. Compactness
belongs to the FULL source category; no hypercomplete sphere is asserted
compact. The adjunction/λ/realization comparison is a separate Interface
obligation, specified in `RealizationKernel.lean`. -/
def RealizationKernel : Prop :=
  ∀ (X : SyntheticObject) (m w : ℤ) (a : BiHom m w (X.obj D.nu D.auxiliary)),
    (D.recovery.realization.map a = 0 ↔ ∃ k : ℕ, lambdaMultiply k a = 0)

/-- BHS `cor:tau-surj`: Adams filtration equals λ-Bockstein filtration.
The inequality makes the exponent nonnegative. It says nothing about
the filtration of a particular θ₅² or the value of a particular product. -/
def FiltrationLambda : Prop :=
  ∀ (X : ClassicalObject) (m w s : ℤ) (h : w - m ≤ s),
    ∀ a : BiHom m w (D.nu.functor.obj (X.obj D.auxiliary)),
    (FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a ↔
      ∃ b : BiHom m (m+s) (D.nu.functor.obj (X.obj D.auxiliary)),
        homotopyRegrade rfl (by rw [Int.toNat_of_nonneg (by omega)]; omega)
          (lambdaMultiply (m+s-w).toNat b) = a)

/-- The first quotient label for an actual classical source object, including
completion objects outside the selected route closure. -/
def bhsFirstLabel (X : C) (s t : ℤ) (x : E2 H X s t) :
    BiHom (t-s) t (XModLambdaN
      ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X)) 1) := by
  simpa using (D.firstQuotient X 0 s t).symm x

/-- Untruncated lifting at ONE source object. BHS A.1(2) is applied only
after its nilpotent-completeness and strong-convergence hypotheses are supplied. -/
def BHSPermanentLiftAt (X : C) : Prop :=
  ∀ (s t : ℤ) (x : E2 H X s t),
    (x ∈ PageRepresentatives.permanentCycles H X (s,t) ↔
      ∃ a : BiHom (t-s) t
        ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X)),
        quotientClass 1 a = bhsFirstLabel D X s t x)

/-- Finite λ-divisibility in the same actual νX. No inverse limit or
surjectivity of integral homotopy into its 2-adic completion is asserted. -/
def BHSLambdaDivisible (X : C) (m w s : ℤ) (h : w-m ≤ s)
    (a : BiHom m w (D.nu.functor.obj X)) : Prop :=
  ∃ b : BiHom m (m+s) (D.nu.functor.obj X),
    homotopyRegrade rfl (by rw [Int.toNat_of_nonneg (by omega)]; omega)
      (lambdaMultiply (m+s-w).toNat b) = a

/-- BHS cor:tau-surj on a specified source object. -/
def BHSFiltrationLambdaAt (X : C) : Prop :=
  ∀ (m w s : ℤ) (h : w-m ≤ s) (a : BiHom m w (D.nu.functor.obj X)),
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a ↔
      BHSLambdaDivisible D X m w s h a

/-- Actual completion maps from the selected ordinary objects. In particular,
the source of `map .nuCofiber` is the cofiber of D.auxiliary.nuMap, and the
source of `map .detector` is D's one detector. Their source completeness,
mod-two equivalence and comparison proofs are separately delivered below. -/
structure BHSCompletionData where
  products : CategoryTheory.Limits.HasProductsOfShape ℕ C
  completed : ClassicalObject → C
  map : ∀ X : ClassicalObject, X.obj D.auxiliary ⟶ completed X
  convergence : ∀ X : ClassicalObject,
    TowerDetection.Convergence H.unit (completed X)

/-- The completed objects, not the ordinary selected sphere, satisfy the
source hypotheses. The actual completion map is a mod-two homology equivalence.
These are Interface construction obligations, proved using bounded-below
completion and finite-type convergence for sphere, its actual ν cofiber,
the same tmf detector, and their shifts. -/
structure BHSCompletionApplicability (Q : BHSCompletionData D) : Prop where
  source : ∀ X : ClassicalObject,
    BHSObjectApplicability Q.products H.unit (Q.completed X)
  mod2_equivalence : ∀ (X : ClassicalObject) (n : ℤ),
    Function.Bijective (Mod2Homology.pushforward H (Q.map X) n)

/-- Source-to-selected comparison along q and νq. These are internal
completion comparisons, not additional BHS theorems. `first_quotient_image`
reflects only the image modulo λ; it does NOT assert π₀(S) → π₀(S₂∧) is
surjective. The finite divisibility reflection likewise retains the selected
integral class. No particular permanent class or differential is assumed. -/
structure BHSCompletionComparison (Q : BHSCompletionData D) : Prop where
  permanent_cycles : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t),
    (x ∈ PageRepresentatives.permanentCycles H (X.obj D.auxiliary) (s,t) ↔
      adamsInternalE2Induced H.unit (Q.map X) (s,t) x ∈
        PageRepresentatives.permanentCycles H (Q.completed X) (s,t))
  first_quotient_image : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t),
    (∃ a : BiHom (t-s) t
        ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj (Q.completed X))),
      quotientClass 1 a = bhsFirstLabel D (Q.completed X) s t
        (adamsInternalE2Induced H.unit (Q.map X) (s,t) x)) ↔
    (∃ a : BiHom (t-s) t (nuZero D X),
      quotientClass 1 a = firstLabel D X s t x)
  filtration : ∀ (X : ClassicalObject) (m w s : ℤ)
    (a : BiHom m w (D.nu.functor.obj (X.obj D.auxiliary))),
    (FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a ↔
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s
        (a ≫ D.nu.functor.map (Q.map X)))
  lambda_divisibility : ∀ (X : ClassicalObject) (m w s : ℤ) (h : w-m ≤ s)
    (a : BiHom m w (D.nu.functor.obj (X.obj D.auxiliary))),
    (BHSLambdaDivisible D (Q.completed X) m w s h
        (a ≫ D.nu.functor.map (Q.map X)) ↔
      BHSLambdaDivisible D (X.obj D.auxiliary) m w s h a)

/-- The remaining zero region in BHS A.8's E₂ formula. M already fixes
the nonzero-weight comparison D.nuE2; this rules out extra classes above
that region instead of silently ignoring them. -/
def E2WeightVanishing : Prop :=
  ∀ (X : ClassicalObject) (a s t w : ℤ), t+a < w →
    Subsingleton ((D.family.obj ((SyntheticCategory.biShift (0,a)).obj
      (D.nu.functor.obj (X.obj D.auxiliary)))).E₂ (s,t,w))

/-- BHS `SynRevAdams.tex`, `cor:synth-ctau-ASS` (1),(3), in the paper's
weight convention: for each positive quotient length q, every finite page
E_r (r >= 2) is zero outside 0 <= t-w < q. The E-infinity assertion is
separately part of `EInftyFormulaInput`. This is a statement about the actual
finite lambda quotient and its actual Adams pages, not about lambda^q acting
as zero on all of its homotopy groups. No completeness hypothesis on X is
needed for this finite-quotient source result. -/
def FiniteQuotientPageVanishing : Prop :=
  ∀ (X : ClassicalObject) (q : ℕ), 0 < q → ∀ (r s t w : ℤ), 2 ≤ r →
    (t < w ∨ (q : ℤ) ≤ t-w) →
      Subsingleton ((D.family.nuQuotient D.nu (X.obj D.auxiliary) q).Page r (s,t,w))

end
end KIP126.Literature.Route


/-! Exact classical source existence on one actual sphere background.
No arbitrary route, synthetic category, normalized lift or detector occurs
in the accepted source theorem. Identification with selected route maps is
an independently supplied model comparison. -/
namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

structure ClassicalSourceData (H : Mod2EilenbergMacLane (C := C)) where
  convergence : TowerDetection.Convergence H.unit SphereSpectrum
  eta : HomotopyGroup (C := C) 1 SphereSpectrum
  nu : HomotopyGroup (C := C) 3 SphereSpectrum
  theta5 : HomotopyGroup (C := C) 62 SphereSpectrum

variable {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]

/-- Identity with source classical objects and with the actual selected
normalized eta. These are construction/comparison obligations, not source
facts valid for arbitrary selections in D. -/
structure ClassicalSourceBinding (D : Model H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn)) (S : ClassicalSourceData H) : Prop where
  convergence : D.classicalConvergence .sphere = S.convergence
  eta : D.auxiliary.etaMap = S.eta
  nu : D.auxiliary.nuMap = S.nu
  normalized_eta : ∃ he : normalizedExponent H D.auxiliary.etaMap = 1,
    η = (etaSourceIso D he).hom ≫
      (D.normalizedMap (.shift 1 .sphere) .sphere D.auxiliary.etaMap).map ≫ D.nu.unitIso.hom
end KIP126.Literature.Route


namespace KIP126.Literature.Route
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.Synthetic.Context
universe u v
variable (Syn : Type u) [SyntheticCategory.{u, v} Syn]

/-- Tensor suspension conventions and exactness on the existing synthetic
category. To apply May's TC3, the source model must realize THESE choices;
independent exact tensor functors do not by themselves supply TC3. -/
structure MayContext where
  leftShift : ∀ X : Syn, (tensorLeft X).CommShift ℤ
  rightShift : ∀ X : Syn, (tensorRight X).CommShift ℤ
  leftExact : ∀ X : Syn, letI := leftShift X; (tensorLeft X).IsTriangulated
  rightExact : ∀ X : Syn, letI := rightShift X; (tensorRight X).IsTriangulated

/-- The source square and boundary relation selected from May (2001), TC3
(author PDF pp.12–13). The lifting field is the homotopy-group consequence
of the `(j₁,j₂)` pushpull square in Lemma 4.6 (p.14). This is precisely the
part of that source data used here, not a definition of the full TC3 axiom.

The negative sign is essential: TC3 identifies the two paths through
`−id ∧ h′` and `h ∧ id`. The fixed CommShift witnesses above identify their
common suspension target. No unsigned boundary formula is asserted. -/
structure MayPushpullData (B : MayContext Syn)
    (T U : HoCofiberSequence (C := Syn)) where
  vertex : Syn
  j1 : vertex ⟶ T.X ⊗ U.Z
  j2 : vertex ⟶ T.Y ⊗ U.Y
  j3 : vertex ⟶ T.Z ⊗ U.X
  square : j1 ≫ (T.f ▷ U.Z) = j2 ≫ (T.Y ◁ U.g)
  other_square : j2 ≫ (T.g ▷ U.Y) = j3 ≫ (T.Z ◁ U.f)
  boundary : letI := B.leftShift; letI := B.rightShift
    letI := B.leftExact; letI := B.rightExact
    j1 ≫ (U.map (tensorLeft T.X)).h = -(j3 ≫ (T.map (tensorRight U.X)).h)
  lift : ∀ (n : ℤ) (a : HomotopyGroup n (T.X ⊗ U.Z))
      (b : HomotopyGroup n (T.Y ⊗ U.Y)),
    a ≫ (T.f ▷ U.Z) = b ≫ (T.Y ◁ U.g) →
    ∃ v : HomotopyGroup n vertex, v ≫ j1 = a ∧ v ≫ j2 = b

/-- The signed elementwise consequence of TC3 and Lemma 4.6. Both boundary
classes lie in the same actual homotopy group. -/
def MayContext.SignedBoundary (B : MayContext Syn) : Prop :=
  letI := B.leftShift; letI := B.rightShift
  letI := B.leftExact; letI := B.rightExact
  ∀ (T U : HoCofiberSequence (C := Syn)) (n : ℤ)
    (a : HomotopyGroup n (T.X ⊗ U.Z))
    (b : HomotopyGroup n (T.Y ⊗ U.Y)),
    inducedMap (T.f ▷ U.Z) n a = inducedMap (T.Y ◁ U.g) n b →
    ∃ c : HomotopyGroup n (T.Z ⊗ U.X),
      inducedMap (T.g ▷ U.Y) n b = inducedMap (T.Z ◁ U.f) n c ∧
      connectingHomomorphism (U.map (tensorLeft T.X)) n a =
        -(connectingHomomorphism (T.map (tensorRight U.X)) n c)

/-- Historical unsigned target. This is NOT May's source theorem: sign
removal needs an additional premise on the actual boundary or on its image.
It is retained as a named compatibility target, not an external input. -/
def MayContext.Boundary (B : MayContext Syn) : Prop :=
  letI := B.leftShift; letI := B.rightShift
  letI := B.leftExact; letI := B.rightExact
  KIP126.Stable.MaySmashBoundary (C := Syn)

end KIP126.Literature.Route


/-! Low-dimensional and symmetric Toda inputs. The synthetic versions
are source-transport obligations, not verbatim classical formulas: λ²η,
rather than η, has bidegree (1,0). See the source/application distinction
in `docs/STAGE0_INTERFACES.md`. No high-stem indeterminacy is discarded. -/
namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- Regrading for the genuine Toda construction; no source iso is chosen
as an extra input. Suspension for a Toda bracket adds (1,0). -/
def tripleTodaSource (a aw b bw c cw : ℤ) :
    Smn (Syn := Syn) (a+(b+c)+1) (aw+(bw+cw)) ≅
      ((SyntheticCategory.biShift (b+c,bw+cw)).obj (Smn a aw))⟦(1 : ℤ)⟧ := by
  simpa only [Prod.mk_add_mk, add_zero, Smn, Functor.comp_obj] using
    ((SyntheticCategory.biShift_comp (a+(b+c),aw+(bw+cw)) (1,0)).app
      (S_0_0 : Syn)).symm ≪≫
    (SyntheticCategory.biShift (1,0)).mapIso
      ((SyntheticCategory.biShift_comp (a,aw) (b+c,bw+cw)).app S_0_0).symm ≪≫
    (SyntheticCategory.biShift_compat (Syn := Syn) 1).app _

/-- Complete Toda membership, including the actual distinguished triangle
and all choices of extensions. This is a defined relation, not a free Prop. -/
def TripleToda {a aw b bw c cw : ℤ}
    (x : BiHom a aw (S_0_0 : Syn)) (y : BiHom b bw (S_0_0 : Syn))
    (z : BiHom c cw (S_0_0 : Syn))
    (value : BiHom (a+(b+c)+1) (aw+(bw+cw)) (S_0_0 : Syn)) : Prop :=
  Toda.Relation ((tripleTodaSource a aw b bw c cw).inv ≫ value)
    ((SyntheticCategory.biShift (b+c,bw+cw)).map x)
    ((SyntheticCategory.biShift_comp (b,bw) (c,cw)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (c,cw)).map y) z

/-- Actual multiplication by two, with the zero suspension removed. -/
def syntheticTwo : BiHom 0 0 (S_0_0 : Syn) :=
  SyntheticCategory.biShift_zero.hom.app S_0_0 ≫ (2 • 𝟙 _)

/-- The one low-dimensional source choice. The label equation belongs to the
source result below; no second η or h₀ is selected during consumption. -/
structure TodaSourceData where
  h0 : BiHom 0 1 (S_0_0 : Syn)

/-- Exact secondary-operation evidence required before transporting the
symmetric theorem. `twoStar` is the degree-(1,0) star of multiplication by two.
Its product identification must be proved in this synthetic model; the
C-motivic value τη in IWX cannot simply be renamed λ²η. The low bracket also
requires an actual Massey/Moss or Toda calculation, beyond the ring equations.
This record is an INTERNAL construction/comparison obligation, not A(M). -/
structure TodaSecondaryComparison (η : BiHom 1 2 (S_0_0 : Syn))
    (S : TodaSourceData (Syn := Syn)) where
  low_bracket : TripleToda S.h0 η S.h0
    (sphereProduct (m := 1) (n := 2) (k := 1) (l := 2) η η)
  twoStar : BiHom 1 0 (S_0_0 : Syn)
  symmetric : ∀ θ : BiHom 62 64 (S_0_0 : Syn), θ + θ = 0 →
    TripleToda syntheticTwo θ syntheticTwo (sphereProduct (m := 1) (n := 0) (k := 62) (l := 64) twoStar θ)
  star_product : ∀ θ : BiHom 62 64 (S_0_0 : Syn),
    sphereProduct (m := 1) (n := 0) (k := 62) (l := 64) twoStar θ = lambdaMultiply 2 (sphereProduct η θ)

end
end KIP126.Literature.Route


namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

variable (D : Model H M Syn) (L : TmfLabels H)

/-- The classical θ₅ Hurewicz vanishing used in LWX Prop. 7.8.
The map is the unit of D's selected detector, interpreted as 2-completed
connective tmf. Source: BMQ Figure 1.1 and Theorem 1.2 in degree 62.
This does NOT assert synthetic θ₅ vanishing: that still needs the
synthetic/classical comparison and the relevant λ-torsion analysis. -/
def TmfTheta5Vanishing : Prop :=
  ∀ θ : HomotopyGroup (C := C) 62 SphereSpectrum,
    ClassicalTheta D θ → θ ≫ D.auxiliary.detectorUnit = 0

/-- Internal classical Adams consequence of the BMQ source, its product
comparison, and C(M) with vanishing/separation: the leading grade g⁴Δh₁g
survives nontrivially, and ONE class it detects has nonzero tmf image.
Independence of the detected representative is a Main deduction, requiring
higher-filtration vanishing; it is not a further external input.
Identification of the selected detector/unit and these two labels with
the source alone does not prove nonzero leading grade. -/
def TmfHigh125Detection : Prop :=
  NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
    (25,150) (L.high125 M) ∧
  ∃ α : HomotopyGroup (C := C) 125 SphereSpectrum,
    TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (L.high125 M) α ∧ α ≫ D.auxiliary.detectorUnit ≠ 0

/-- The small part of the classical tmf E₂ calculation needed to transport
the 62-stem vanishing through λ-localization. Source: BMQ §2,
H_*tmf = (A//A(2))_* and its change-of-rings E₂. There is no nonpositive-AF
class in positive stem 63. This is prior tmf input, not a Lin sphere CSV row. -/
def TmfLowFiltration63 : Prop :=
  ∀ s : ℤ, s ≤ 0 → Subsingleton (E2 H D.auxiliary.detector s (63+s))

end
end KIP126.Literature.Route


namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- Pstrągowski's realization comparison on bigraded spheres, using the
existing functor, ν-unit and λ powers. These are comparison witnesses for
an external existence result, not a second realization or arbitrary maps
on homotopy groups. The base unit and weight changes are pinned down. -/
structure RealizationCoordinates where
  sphere : ∀ m w : ℤ, Sphere (C := C) m ≅ D.recovery.realization.obj (Smn (Syn := Syn) m w)
  unit : (sphere 0 0).hom ≫ D.recovery.realization.map
      (SyntheticCategory.biShift_zero.hom.app (S_0_0 : Syn)) =
    (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫
      D.recovery.nuRealizationIso.inv.app SphereSpectrum ≫
      D.recovery.realization.map D.nu.unitIso.hom
  lambda : ∀ (m w : ℤ) (k : ℕ),
    (sphere m (w-k)).hom ≫
      D.recovery.realization.map (lambdaMultiply k (𝟙 (Smn (Syn := Syn) m w))) =
        (sphere m w).hom

def realizeNu (R : RealizationCoordinates D) (X : ClassicalObject) {m w : ℤ}
    (a : BiHom m w (D.nu.functor.obj (X.obj D.auxiliary))) :
    HomotopyGroup m (X.obj D.auxiliary) :=
  (R.sphere m w).hom ≫ D.recovery.realization.map a ≫
    D.recovery.nuRealizationIso.hom.app (X.obj D.auxiliary)

def realizeNuZero (R : RealizationCoordinates D) (X : ClassicalObject) {m w : ℤ}
    (a : BiHom m w (nuZero D X)) : HomotopyGroup m (X.obj D.auxiliary) :=
  realizeNu D R X (a ≫ SyntheticCategory.biShift_zero.hom.app _)

/-- Realization at a completed source object outside the selected closure.
The sphere-coordinate iso and ν-realization iso are the SAME as for the route. -/
def realizeNuZeroObject (R : RealizationCoordinates D) (X : C) {m w : ℤ}
    (a : BiHom m w
      ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X))) :
    HomotopyGroup m X :=
  (R.sphere m w).hom ≫ D.recovery.realization.map
    (a ≫ SyntheticCategory.biShift_zero.hom.app _) ≫
    D.recovery.nuRealizationIso.hom.app X

/-- Internal transport of BHS detection, prescribed lifts and torsion lifts
along the SAME q, νq and realization isomorphisms. The two image-reflection
clauses retain their specified ordinary homotopy class or finite λ exponent;
neither asserts arbitrary surjectivity into completed homotopy groups. -/
structure BHSRealizationComparison (R : RealizationCoordinates D)
    (Q : BHSCompletionData D) : Prop where
  survives_to : ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ)
    (x : E2 H (X.obj D.auxiliary) s t),
    (SurvivesTo (adamsTowerInternalSpectralSequence H.unit (X.obj D.auxiliary))
        (r+1) (s,t) x ↔
      SurvivesTo (adamsTowerInternalSpectralSequence H.unit (Q.completed X))
        (r+1) (s,t) (adamsInternalE2Induced H.unit (Q.map X) (s,t) x))
  nonzero_survival : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t),
    (NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit (X.obj D.auxiliary))
        (s,t) x ↔
      NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit (Q.completed X))
        (s,t) (adamsInternalE2Induced H.unit (Q.map X) (s,t) x))
  hit_on_page : ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ)
    (x : E2 H (X.obj D.auxiliary) s t),
    (HitOnPage (adamsTowerInternalSpectralSequence H.unit (X.obj D.auxiliary))
        r (s,t) x ↔
      HitOnPage (adamsTowerInternalSpectralSequence H.unit (Q.completed X))
        r (s,t) (adamsInternalE2Induced H.unit (Q.map X) (s,t) x))
  first_quotient_natural : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t) (a : BiHom (t-s) t (nuZero D X)),
    quotientClass 1 a = firstLabel D X s t x →
    quotientClass 1 (a ≫ (SyntheticCategory.biShift (0,0)).map
      (D.nu.functor.map (Q.map X))) = bhsFirstLabel D (Q.completed X) s t
        (adamsInternalE2Induced H.unit (Q.map X) (s,t) x)
  realization_natural : ∀ (X : ClassicalObject) (m w : ℤ)
    (a : BiHom m w (nuZero D X)),
    realizeNuZero D R X a ≫ Q.map X =
      realizeNuZeroObject D R (Q.completed X)
        (a ≫ (SyntheticCategory.biShift (0,0)).map (D.nu.functor.map (Q.map X)))
  detection : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t)
    (a : HomotopyGroup (t-s) (X.obj D.auxiliary)),
    (TowerDetection.Detects (D.classicalConvergence X) (s,t) x a ↔
      TowerDetection.Detects (Q.convergence X) (s,t)
        (adamsInternalE2Induced H.unit (Q.map X) (s,t) x) (a ≫ Q.map X))
  prescribed_lift_reflection : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t)
    (a : HomotopyGroup (t-s) (X.obj D.auxiliary)),
    (∃ b : BiHom (t-s) t
        ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj (Q.completed X))),
      quotientClass 1 b = bhsFirstLabel D (Q.completed X) s t
        (adamsInternalE2Induced H.unit (Q.map X) (s,t) x) ∧
      realizeNuZeroObject D R (Q.completed X) b = a ≫ Q.map X) →
    ∃ b : BiHom (t-s) t (nuZero D X),
      quotientClass 1 b = firstLabel D X s t x ∧ realizeNuZero D R X b = a
  torsion_lift_reflection : ∀ (X : ClassicalObject) (s t : ℤ) (k : ℕ)
    (x : E2 H (X.obj D.auxiliary) s t),
    (∃ a : BiHom (t-s) t
        ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj (Q.completed X))),
      quotientClass 1 a = bhsFirstLabel D (Q.completed X) s t
        (adamsInternalE2Induced H.unit (Q.map X) (s,t) x) ∧
      lambdaMultiply k a = 0) →
    ∃ a : BiHom (t-s) t (nuZero D X),
      quotientClass 1 a = firstLabel D X s t x ∧ lambdaMultiply k a = 0

end
end KIP126.Literature.Route


/-! Full-category localization and its scoped application to the route.

Pstrągowski's `prop:tau_inversion_functor_exists` constructs localization as
an actual telescope in full synthetic spectra. Its compact spheres (the remark
`rem:synthetic_spectra_compactly_generated_by_suspensions_of_synthetic_analogues_of_finite_projectives`)
give the finite-power kernel criterion. The source reflection is kept in its
full category; it is not assumed to recover the same classical category as
the selected complete model. Hypercompletion is a different step:
§4.5 identifies the complete objects and their inclusion. The data below must
come from that construction (or an equivalent comparison); an abstract
`SyntheticCategory` alone does not establish any of these facts.
-/
namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
noncomputable section
variable (Syn : Type w) [SyntheticCategory.{w, v} Syn]

/-- The FULL source, its actual λ-localization, and the completion/inclusion
adjunction. Spheres are compared AFTER the left adjoint; this does not identify
an uncompleted source sphere with an included completed sphere. No compactness
of the latter is asserted. -/
structure RealizationKernelSourceData where
  Full : Type w
  [fullCategory : SyntheticCategory.{w, v} Full]
  localization : LambdaLocalization Full
  completion : Full ⥤ Syn
  inclusion : Syn ⥤ Full
  fullyFaithful : inclusion.FullyFaithful
  adjunction : completion ⊣ inclusion
  [completionAdditive : completion.Additive]
  sphere : ∀ m w : ℤ, completion.obj (Smn (Syn := Full) m w) ≅ Smn (Syn := Syn) m w

attribute [instance] RealizationKernelSourceData.fullCategory
attribute [instance] RealizationKernelSourceData.completionAdditive

variable {Syn}

/-- The map on representatives is the ACTUAL adjunction map, precomposed with
the specified completed-sphere comparison. It is not an arbitrary bijection. -/
def RealizationKernelSourceData.representatives (S : RealizationKernelSourceData Syn)
    (X : Syn) (m w : ℤ) :
    BiHom m w X ≃+ BiHom m w (S.inclusion.obj X) where
  toFun a := S.adjunction.homAddEquiv _ _ ((S.sphere m w).hom ≫ a)
  invFun a := (S.sphere m w).inv ≫ (S.adjunction.homAddEquiv _ _).symm a
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := by simp [Preadditive.comp_add]

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- Exact local comparison needed to use the source kernel criterion. The
realization condition must be proved for the displayed included objects; it
is not a claim that full and hypercomplete localization commute on every object.
The λ condition compares all powers and records their changed weights. -/
structure RealizationKernelBinding (S : RealizationKernelSourceData Syn) : Prop where
  realization_zero : ∀ (X : SyntheticObject) (m w : ℤ)
      (a : BiHom m w (X.obj D.nu D.auxiliary)),
    D.recovery.realization.map a = 0 ↔
      S.localization.endofunctor.map (S.representatives _ m w a) = 0
  lambda : ∀ (X : SyntheticObject) (m w : ℤ) (k : ℕ)
      (a : BiHom m w (X.obj D.nu D.auxiliary)),
    S.representatives _ m (w-k) (lambdaMultiply k a) =
      lambdaMultiply k (S.representatives _ m w a)

end
end KIP126.Literature.Route


/-! The ordinary homotopy-category consequences of the external symmetric
monoidal and λ-quotient algebra theorems. A commutative monoid object here
is NOT advertised as a construction of an E∞ algebra. These explicit
consequences are exactly the algebraic operations the selected route uses. -/
namespace KIP126.Literature.Route
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- Multiplication of homotopy classes induced by an ACTUAL monoid object.
The order y ⊗ x matches the existing `sphereAction x y` convention. -/
noncomputable abbrev algebraProduct {A : Syn} (Q : MonObj A) {m n k l : ℤ}
    (x : BiHom m n A) (y : BiHom k l A) : BiHom (m+k) (n+l) A :=
  KIP126.Kervaire.Route.algebraProduct Q x y

/-- The source existence consequence of BHSmot Appendices B/C and
BX `cnstr:bock-maps`, transported along cofiber-object isomorphisms.
Each positive finite quotient has a commutative algebra whose unit is its
specified inclusion. No assertion about a preselected cofiber filler or
the route sphere action is accepted in this raw source statement. -/
structure QuotientAlgebraStructures (D : Model H M Syn) [BraidedCategory Syn] where
  algebra : ∀ q : ℕ, 0 < q → MonObj (XModLambdaN (S_0_0 : Syn) q)
  commutative : ∀ (q : ℕ) (hq : 0 < q),
    letI := algebra q hq; IsCommMonObj (XModLambdaN (S_0_0 : Syn) q)
  unit : ∀ (q : ℕ) (hq : 0 < q), (algebra q hq).one = XModLambdaN.incl S_0_0 q

/-- The route-ready quotient algebras. The two additional comparisons are
INTERNAL source-to-model obligations: a TR3 cofiber filler is not identified
with a source algebra restriction merely by having the same name or square.
Producing these fields for the selected source algebras remains an
Interface comparison obligation; source algebra existence alone is insufficient. -/
structure QuotientAlgebras [BraidedCategory Syn] extends QuotientAlgebraStructures D where
  /-- The algebra product extends the already fixed sphere action. -/
  sphere_action : ∀ (q : ℕ) (hq : 0 < q) (m n k l : ℤ)
      (x : BiHom m n (S_0_0 : Syn)) (y : BiHom k l (XModLambdaN S_0_0 q)),
    algebraProduct (algebra q hq) (quotientClass q x) y = sphereAction x y
  restriction : ∀ (i j : ℕ) (hi : 0 < i) (hij : i ≤ j),
    ((D.quotientTower (S_0_0 : Syn)).rho i j hij ⊗ₘ
        (D.quotientTower (S_0_0 : Syn)).rho i j hij) ≫ (algebra i hi).mul =
      (algebra j (hi.trans_le hij)).mul ≫ (D.quotientTower (S_0_0 : Syn)).rho i j hij

/-- The ring structure of the SAME detector and its synthetic analogue.
The units are fixed to D's actual Hurewicz maps. This is the ordinary
homotopy-category consequence of tmf being a commutative ring spectrum
and the synthetic analogue being lax monoidal. -/
structure DetectorAlgebra [BraidedCategory C] [BraidedCategory Syn] where
  classical : MonObj D.auxiliary.detector
  classical_commutative : letI := classical; IsCommMonObj D.auxiliary.detector
  classical_unit : classical.one = D.auxiliary.detectorUnit
  synthetic : MonObj (D.nu.functor.obj D.auxiliary.detector)
  synthetic_commutative : letI := synthetic
    IsCommMonObj (D.nu.functor.obj D.auxiliary.detector)
  synthetic_unit : synthetic.one = KIP126.Literature.Route.detectorMap D
  sphere_action : ∀ (m n k l : ℤ) (x : BiHom m n (S_0_0 : Syn))
      (y : BiHom k l (D.nu.functor.obj D.auxiliary.detector)),
    algebraProduct synthetic (x ≫ KIP126.Literature.Route.detectorMap D) y =
      sphereAction x y

/-- Existence witnesses for source algebra consequences, on the same
tensor products and realization. Providing these fields is an explicit
application of the external source to this model; no instance is installed.
Pstrągowski's λ-inversion is symmetric monoidal. -/
structure AlgebraData where
  classicalSymmetric : SymmetricCategory C
  syntheticSymmetric : SymmetricCategory Syn
  realizationMonoidal : letI := classicalSymmetric; letI := syntheticSymmetric
    D.recovery.SymmetricMonoidal
  quotients : letI := syntheticSymmetric; QuotientAlgebraStructures D
  detector : letI := classicalSymmetric; letI := syntheticSymmetric; DetectorAlgebra D

/-- Existence witnesses for source algebra consequences, on the same
tensor products and realization. Providing these fields is an explicit
application of the external source to this model; no instance is installed.
Pstrągowski's λ-inversion is symmetric monoidal. -/
structure AlgebraInput where
  classicalSymmetric : SymmetricCategory C
  syntheticSymmetric : SymmetricCategory Syn
  realizationMonoidal : letI := classicalSymmetric; letI := syntheticSymmetric
    D.recovery.SymmetricMonoidal
  quotients : letI := syntheticSymmetric; QuotientAlgebras D
  detector : letI := classicalSymmetric; letI := syntheticSymmetric; DetectorAlgebra D


/-- Compatibility of the source quotient structures with the actual route
sphere action and restriction maps. This is produced internally, separately
from the source existence result. -/
structure QuotientAlgebraBinding (I : AlgebraData D) : Prop where
  sphere_action : letI := I.syntheticSymmetric; ∀ (q : ℕ) (hq : 0 < q) (m n k l : ℤ)
      (x : BiHom m n (S_0_0 : Syn)) (y : BiHom k l (XModLambdaN S_0_0 q)),
    algebraProduct (I.quotients.algebra q hq) (quotientClass q x) y = sphereAction x y
  restriction : letI := I.syntheticSymmetric; ∀ (i j : ℕ) (hi : 0 < i) (hij : i ≤ j),
    ((D.quotientTower (S_0_0 : Syn)).rho i j hij ⊗ₘ
        (D.quotientTower (S_0_0 : Syn)).rho i j hij) ≫ (I.quotients.algebra i hi).mul =
      (I.quotients.algebra j (hi.trans_le hij)).mul ≫ (D.quotientTower (S_0_0 : Syn)).rho i j hij

/-- Assemble the consumer record on exactly the supplied source algebra. -/
def AlgebraData.withBinding (I : AlgebraData D) (B : QuotientAlgebraBinding D I) :
    AlgebraInput D where
  classicalSymmetric := I.classicalSymmetric
  syntheticSymmetric := I.syntheticSymmetric
  realizationMonoidal := I.realizationMonoidal
  quotients := by
    letI := I.syntheticSymmetric
    exact { I.quotients with sphere_action := B.sphere_action, restriction := B.restriction }
  detector := I.detector

end KIP126.Literature.Route


/-! Source data are chosen once. They contain actual spectra, unit maps,
classes and convergence data, not an uninterpreted `isTmf` predicate.
The BMQ results on these data and their identification with the route model
are separate records. No local route conclusion is assumed here. -/
namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- The ordinary sphere product is the actual shifted composite. -/
def classicalSphereProduct {m n : ℤ}
    (x : HomotopyGroup (C := C) m SphereSpectrum)
    (y : HomotopyGroup (C := C) n SphereSpectrum) :
    HomotopyGroup (C := C) (m+n) SphereSpectrum :=
  (shiftFunctorAdd C m n).hom.app SphereSpectrum ≫ (shiftFunctor C n).map x ≫ y

/-- The portion of the completed BMQ source model used by the proof. The
source existence theorem supplies these actual objects and maps together;
its interpretation is 2-completed connective tmf and its ring unit. The
completion/source identification is a separate model-construction theorem,
not an untyped `isTmf` field and not an arbitrary local-result assumption. -/
structure TmfSourceData (H : Mod2EilenbergMacLane (C := C)) where
  spectrum : C
  algebra : MonObj spectrum
  labels : TmfLabels H
  sphereConvergence : TowerDetection.Convergence H.unit SphereSpectrum
  convergence : TowerDetection.Convergence H.unit spectrum
  kappaBar : HomotopyGroup (C := C) 20 SphereSpectrum
  wClass : HomotopyGroup (C := C) 45 SphereSpectrum

def TmfSourceData.unit (S : TmfSourceData H) : SphereSpectrum ⟶ S.spectrum :=
  S.algebra.one

def TmfSourceData.high125 (S : TmfSourceData H) :
    HomotopyGroup (C := C) 125 SphereSpectrum :=
  classicalSphereProduct
    (classicalSphereProduct (classicalSphereProduct S.kappaBar S.kappaBar)
      (classicalSphereProduct S.kappaBar S.kappaBar)) S.wClass

/-- Explicit identities with the ONE route detector, its unit, its G labels
and its convergence. The page map is the map of the actual Adams tower,
so no unrelated linear equivalence is introduced. -/
structure TmfBinding (D : Model H M Syn) (G : TmfLabels H) (S : TmfSourceData H) where
  detectorIso : D.auxiliary.detector ≅ S.spectrum
  unit : D.auxiliary.detectorUnit ≫ detectorIso.hom = S.unit
  g : G.g = S.labels.g
  delta_h_1_mul_g : G.delta_h_1_mul_g = S.labels.delta_h_1_mul_g
  sphereConvergence : D.classicalConvergence .sphere = S.sphereConvergence

/-- Intrinsic identities of the two source labels, without choosing an
arbitrary nonzero class or relying on its name. The classical E2 groups
(4,24) and (9,54) each have exactly one nonzero element. Source: IWX v3,
`cor:main-Adams`, and the cited 2022 Zenodo v1 classical E2 chart CSV,
rows 59 (`g`, stem 20, AF 4) and 275 (`D h1 g`, stem 45, AF 9).
The chart's `D` denotes Delta. These finite prior calculations make the
source labels unique even when the source result is supplied existentially. -/
def TmfLabels.Standard (G : TmfLabels H) : Prop :=
  G.g ≠ 0 ∧ (∀ x : E2 H SphereSpectrum 4 24, x ≠ 0 → x = G.g) ∧
  G.delta_h_1_mul_g ≠ 0 ∧
    (∀ x : E2 H SphereSpectrum 9 54, x ≠ 0 → x = G.delta_h_1_mul_g)

/-- The classical multiplicative comparison required by the tmf adapter.
It relates the actual shifted homotopy product to the fixed cobar product;
it is a general comparison theorem to prove, not a BMQ result. -/
def ClassicalProductDetection (D : Model H M Syn) : Prop :=
  ∀ (s t s' t' : ℕ) (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum s' t')
    (a : HomotopyGroup (C := C) ((t : ℤ)-s) SphereSpectrum)
    (b : HomotopyGroup (C := C) ((t' : ℤ)-s') SphereSpectrum),
    TowerDetection.Detects (D.classicalConvergence .sphere) (s,t) x a →
    TowerDetection.Detects (D.classicalConvergence .sphere) (s',t') y b →
    TowerDetection.Detects (D.classicalConvergence .sphere) ((s+s' : ℕ),(t+t' : ℕ))
      (Sphere.Internal.product H M x y)
      (eqToHom (congrArg (fun n : ℤ => Sphere (C := C) n)
        (by simp only [Nat.cast_add]; omega : ((t+t' : ℕ) : ℤ)-(s+s') = ((t : ℤ)-s)+((t' : ℤ)-s'))) ≫ classicalSphereProduct a b)

/-- This is the CLASSICAL tail obligation used to remove the ambiguity of a
125-stem representative. It is a consequence of the C(M) E5-exhaustion,
Ravenel's vanishing line and the same tower's separated filtration. It is
not a tmf source theorem and says nothing about synthetic lambda torsion. -/
def ClassicalHigh125Tail (D : Model H M Syn) : Prop :=
  ∀ a : HomotopyGroup (C := C) 125 SphereSpectrum,
    a ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 26 125 → a = 0
end
end KIP126.Literature.Route


namespace KIP126.Literature.Route
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.Kervaire.Route
open KIP126.Literature.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- Moss (1970), Theorem 1.2, in the precise local specialization used by
LWX Lemma 7.16. The defining systems, two null products, two no-crossing
conditions and residual-tower condition remain explicit hypotheses.
It asserts existence of a detected bracket member, not that every member
is permanent or that the bracket has zero indeterminacy. The statement and
crossing convention were also checked against Belmont--Kong (2021),
Theorem 1.1 / 4.11 and Definition 2.10. Moss's original scan was unavailable;
the source inventory does not advertise it as independently read. -/
abbrev MossInput := KIP126.Literature.Route.ThetaBMossInput D

/-- The residual-tower hypothesis for the selected complete classical
sphere. This is an applicability obligation for the Moss source theorem,
not a computational no-crossing or Massey-value assertion. -/
abbrev MossTowerApplicability :=
  TowerDetection.ResidualInjectivity H.unit (SphereSpectrum (C := C))
end KIP126.Literature.Route


/-! Model multiplication comparisons. These are structural realization
obligations, kept separate from the statement that the source quotient
algebras exist. No specified local multiplication value is a field. -/
namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn) (I : AlgebraData D)

structure AlgebraBinding : Prop where
  classical_detection : ClassicalProductDetection D
  first_quotient : letI := I.syntheticSymmetric
    FirstQuotientMultiplicationCompatible D (I.quotients.algebra 1 (by decide))
  finite_detection : letI := I.syntheticSymmetric
    ∀ (q : ℕ) (hq : 0 < q),
      FiniteQuotientMultiplicationCompatible D q hq (I.quotients.algebra q hq)
  finite_action : FiniteQuotientSphereActionCompatible D
  action_filtration : SphereActionFiltrationCompatible D
  finite_filtration : letI := I.syntheticSymmetric
    ∀ (q : ℕ) (hq : 0 < q),
      FiniteQuotientFiltrationCompatible D q (I.quotients.algebra q hq)
end KIP126.Literature.Route


/-! Explicit source-to-model binding obligations. Existence of a good
geometric lift does not imply that an arbitrary previously selected lift
has that property. These conditions accompany A(M) instead of being
silently added to the frozen M, or asserted for every abstract model. -/
namespace KIP126.Literature.Route
open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- The first three sphere comparisons are CONSTRUCTED from the frozen ν
unit/suspension comparisons, rather than freely postulated isomorphisms. -/
def nuSphereOne : D.nu.functor.obj (Sphere (C := C) 1) ≅ Smn (Syn := Syn) 1 1 :=
  D.nu.suspensionIso SphereSpectrum ≪≫
    (SyntheticCategory.biShift (1,1)).mapIso D.nu.unitIso

def nuSphereTwo : D.nu.functor.obj (Sphere (C := C) 2) ≅ Smn (Syn := Syn) 2 2 :=
  D.nu.functor.mapIso ((shiftFunctorAdd' C 1 1 2 (by norm_num)).app SphereSpectrum) ≪≫
    D.nu.suspensionIso (Sphere (C := C) 1) ≪≫
    (SyntheticCategory.biShift (1,1)).mapIso (nuSphereOne D) ≪≫
    (SyntheticCategory.biShift_comp (1,1) (1,1)).app S_0_0

def nuSphereThree : D.nu.functor.obj (Sphere (C := C) 3) ≅ Smn (Syn := Syn) 3 3 :=
  D.nu.functor.mapIso ((shiftFunctorAdd' C 2 1 3 (by norm_num)).app SphereSpectrum) ≪≫
    D.nu.suspensionIso (Sphere (C := C) 2) ≪≫
    (SyntheticCategory.biShift (1,1)).mapIso (nuSphereTwo D) ≪≫
    (SyntheticCategory.biShift_comp (2,2) (1,1)).app S_0_0

/-- The normalized Hopf ν is the map already selected by D. -/
def normalizedNu (he : normalizedExponent H D.auxiliary.nuMap = 1) :
    BiHom 3 4 (S_0_0 : Syn) := by
  let e : (SyntheticCategory.biShift (0, (normalizedExponent H D.auxiliary.nuMap : ℤ))).obj
      (D.nu.functor.obj (Sphere (C := C) 3)) ≅ Smn (Syn := Syn) 3 4 := by
    rw [he]
    exact (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree D) ≪≫
      (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0
  exact e.inv ≫ (D.normalizedMap (.shift 3 .sphere) .sphere D.auxiliary.nuMap).map ≫
    D.nu.unitIso.hom

/-- Required binding to the actual Cν triangle. The source is the BHS
geometric triangle construction, with rotations, applied to the SAME maps.
Only this triangle is required; no assertion about all chosen lifts is made.
The distinguished condition is an explicit realization obligation, not a
new theorem of LWX or a consequence of the lift factorization alone. -/
structure NuCofiberApplicability : Prop where
  nu_exponent : normalizedExponent H D.auxiliary.nuMap = 1
  bottom_exponent : normalizedExponent H D.auxiliary.nuRouteTriangle.g = 0
  top_exponent : normalizedExponent H D.auxiliary.nuRouteTriangle.h = 0
  normalized_label :
    D.sphereFirstQuotient 1 4 (quotientClass 1 (normalizedNu D nu_exponent)) =
      Sphere.Internal.hi H M 2
  triangle : ∀ he :
      (normalizedExponent H D.auxiliary.nuRouteTriangle.f : ℤ) +
        normalizedExponent H D.auxiliary.nuRouteTriangle.g +
        normalizedExponent H D.auxiliary.nuRouteTriangle.h = 1,
    NormalizedTriangleCompatible D.toModelData D.auxiliary.nuRouteTriangle he

/-- The three lifts supplied by the Pstragowski/BHS geometric construction
for the actual nu cofiber. They are independent of D's later selected
normalized maps. Existence of this source data does not validate arbitrary
choices in D. -/
structure NuCofiberSourceData where
  nuLift : NormalizedSyntheticMap H D.nu D.auxiliary.nuMap
  bottomLift : NormalizedSyntheticMap H D.nu D.auxiliary.nuRouteTriangle.g
  topLift : NormalizedSyntheticMap H D.nu D.auxiliary.nuRouteTriangle.h

/-- The source top lift has exactly the same landing convention as the
route's normalized connecting arrow. -/
def sourceNormalizedConnecting (S : NuCofiberSourceData D)
    (he : (normalizedExponent H D.auxiliary.nuRouteTriangle.f : ℤ) +
      normalizedExponent H D.auxiliary.nuRouteTriangle.g +
      normalizedExponent H D.auxiliary.nuRouteTriangle.h = 1) :=
  let T := D.auxiliary.nuRouteTriangle
  let eg : ℤ := normalizedExponent H T.g
  let eh : ℤ := normalizedExponent H T.h
  let X := D.nu.functor.obj (T.X.obj D.auxiliary)
  (SyntheticCategory.biShift (0,-eg)).map
      (negativeLift (normalizedExponent H T.h) S.topLift.map) ≫
    (SyntheticCategory.biShift (0,-eg)).map
      ((SyntheticCategory.biShift (0,-eh)).map (D.nu.suspensionIso (T.X.obj D.auxiliary)).hom) ≫
    (SyntheticCategory.biShift (0,-eg)).map
      ((SyntheticCategory.biShift_comp (1,1) (0,-eh)).hom.app X) ≫
    (SyntheticCategory.biShift_comp ((1,1)+(0,-eh)) (0,-eg)).hom.app X ≫
    eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj X)
      (show ((1,1)+(0,-eh))+(0,-eg) = (0,(normalizedExponent H T.f : ℤ))+(1,0) from by
        dsimp [eg, eh, T]; ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd] <;> omega)) ≫
    (SyntheticCategory.biShift_comp (0,(normalizedExponent H T.f : ℤ)) (1,0)).inv.app X ≫
    (SyntheticCategory.biShift_compat (Syn := Syn) 1).hom.app _

def sourceNormalizedTriangle (S : NuCofiberSourceData D)
    (he : (normalizedExponent H D.auxiliary.nuRouteTriangle.f : ℤ) +
      normalizedExponent H D.auxiliary.nuRouteTriangle.g +
      normalizedExponent H D.auxiliary.nuRouteTriangle.h = 1) : Triangle Syn :=
  Triangle.mk S.nuLift.map
    (negativeLift (normalizedExponent H D.auxiliary.nuRouteTriangle.g) S.bottomLift.map)
    (sourceNormalizedConnecting D S he)

def sourceNormalizedNu (S : NuCofiberSourceData D)
    (he : normalizedExponent H D.auxiliary.nuMap = 1) : BiHom 3 4 (S_0_0 : Syn) := by
  let e : (SyntheticCategory.biShift (0, (normalizedExponent H D.auxiliary.nuMap : ℤ))).obj
      (D.nu.functor.obj (Sphere (C := C) 3)) ≅ Smn (Syn := Syn) 3 4 := by
    rw [he]
    exact (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree D) ≪≫
      (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0
  exact e.inv ≫ S.nuLift.map ≫ D.nu.unitIso.hom

/-- Binding the three actually selected route arrows to one compatible
source triple. This is model realization data, not the source theorem and
not a consequence of normalized-lift factorization alone. -/
structure NuCofiberLiftBinding (S : NuCofiberSourceData D) : Prop where
  nu : S.nuLift.map =
    (D.normalizedMap (.shift 3 .sphere) .sphere D.auxiliary.nuMap).map
  bottom : S.bottomLift.map =
    (D.normalizedMap D.auxiliary.nuRouteTriangle.Y D.auxiliary.nuRouteTriangle.Z
      D.auxiliary.nuRouteTriangle.g).map
  top : S.topLift.map =
    (D.normalizedMap D.auxiliary.nuRouteTriangle.Z (.shift 1 D.auxiliary.nuRouteTriangle.X)
      D.auxiliary.nuRouteTriangle.h).map


end
end KIP126.Literature.Route
