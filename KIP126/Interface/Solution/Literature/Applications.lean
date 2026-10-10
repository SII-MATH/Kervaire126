import KIP126.Interface.Challenge.Literature.Source
import KIP126.Def.Kervaire.Route.Tmf.Predicates

/-! Application obligations and consumer views of the literature sources.
These are internal construction/transport goals, not additional source inputs. -/

namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- The finite set of classical inputs consumed by the selected §7 route.
No h₆² differential or survival conclusion is a field. -/
structure ClassicalInputs (η : BiHom 1 2 (S_0_0 : Syn)) : Prop where
  theta5_exists : Theta5Existence D
  stem62_exponent_two : Stem62ExponentTwo (C := C)
  theta5_filtration_gap : Theta5FiltrationGap D
  two_detection : TwoDetection D
  hopf : HopfInput D η


end KIP126.Literature.Route

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

structure SyntheticInputs where
  lifts : KIP126.Literature.Route.SyntheticLiftInput D
  finite_lift : FiniteLiftCriterion D
  bockstein : BocksteinDifferential D
  permanent_lift : PermanentLiftCriterion D
  differentials : DifferentialRigidity D
  eInfty : EInftyInput D
  realization_kernel : RealizationKernel D
  filtration_lambda : FiltrationLambda D
  e2_weight_vanishing : E2WeightVanishing D
  finite_quotient_page_vanishing : FiniteQuotientPageVanishing D

/-- Pure assembly; source-to-model localization is supplied separately. -/
def SyntheticSourceInputs.toInputs (S : SyntheticSourceInputs D)
    (Q : BHSCompletionData D) (hQ : BHSCompletionApplicability D Q)
    (B : BHSCompletionComparison D Q)
    (kernel : RealizationKernel D) : SyntheticInputs D where
  lifts := S.lifts
  finite_lift := S.finite_lift
  bockstein := S.bockstein
  permanent_lift := by
    intro X s t x
    exact (B.permanent_cycles X s t x).trans
      ((S.permanent_lift (Q.completed X) Q.products (hQ.source X) s t
        (adamsInternalE2Induced H.unit (Q.map X) (s,t) x)).trans
        (B.first_quotient_image X s t x))
  differentials := S.differentials
  eInfty := S.eInfty
  realization_kernel := kernel
  filtration_lambda := by
    intro X m w s h a
    exact (B.filtration X m w s a).trans
      ((S.filtration_lambda (Q.completed X) Q.products (hQ.source X) m w s h
        (a ≫ D.nu.functor.map (Q.map X))).trans
        (B.lambda_divisibility X m w s h a))
  e2_weight_vanishing := S.e2_weight_vanishing
  finite_quotient_page_vanishing := S.finite_quotient_page_vanishing


end
end KIP126.Literature.Route

namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

variable {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]

/-- Ordinary transport along the displayed source equalities. The sole
synthetic premise is supplied separately, so the classical source theorem
does not assert it or normalized-map compatibility. -/
def classicalInputsOfSource (D : Model H M Syn) (η : BiHom 1 2 (S_0_0 : Syn))
    (S : ClassicalSourceData H) (hS : ClassicalSourceResults M S)
    (B : ClassicalSourceBinding D η S) (hη : EtaChoice M D.toModelData η) :
    ClassicalInputs D η where
  theta5_exists := ⟨hS.h5Square_permanent, S.theta5,
    by simpa [ClassicalTheta, B.convergence, ClassicalObject.obj] using hS.theta5_detection,
    hS.theta5_order_two⟩
  stem62_exponent_two := hS.stem62_exponent_two
  theta5_filtration_gap := by
    intro a b ha hb
    exact hS.theta5_filtration_gap a b
      (by simpa [ClassicalTheta, B.convergence, ClassicalObject.obj] using ha)
      (by simpa [ClassicalTheta, B.convergence, ClassicalObject.obj] using hb)
  two_detection := by simpa [TwoDetection, B.convergence, ClassicalObject.obj] using hS.two_detection
  hopf := by
    refine ⟨hη, ?_, hS.eta_permanent, hS.nu_permanent⟩
    refine ⟨?_, ?_, B.normalized_eta⟩
    · simpa [B.convergence, B.eta, ClassicalObject.obj] using hS.eta_detection
    · simpa [B.convergence, B.nu, ClassicalObject.obj] using hS.nu_detection


end KIP126.Literature.Route

namespace KIP126.Literature.Route
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.Synthetic.Context
universe u v
variable (Syn : Type u) [SyntheticCategory.{u, v} Syn]

/-- Applied May input, retaining the source sign and the fixed conventions.
Consumers may remove the sign only after proving the required exponent-two
condition. Mod-two E₂ coordinates alone do not prove such a condition on
homotopy groups. -/
structure MayInput extends MayContext Syn where
  boundary : toMayContext.SignedBoundary


end KIP126.Literature.Route

namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- Applied consumer package. Its BHS low-ring fields and INTERNAL secondary
operation comparison are delivered separately by `TodaSourceResults` and
`TodaApplication`. Toda 1962, Theorem 3.6 and IWX §6 motivate the latter;
IWX `cor:2-symmetric` is C-motivic and is NOT directly a synthetic theorem. The final field asserts only membership;
LWX's high-degree ZERO INDETERMINACY check remains a paper/C(M) task. -/
structure TodaInputs (η : BiHom 1 2 (S_0_0 : Syn)) where
  h0 : BiHom 0 1 (S_0_0 : Syn)
  h0_label : D.sphereFirstQuotient 1 1 (quotientClass 1 h0) = Sphere.Internal.hi H M 0
  lambda_h0 : lambdaMultiply 1 h0 = syntheticTwo
  h0_eta : sphereProduct h0 η = 0
  /-- η² belongs to <[h₀],η,[h₀]>. We do not replace a Toda set by
  a selected value; the low indeterminacy vanishing is a separate field. -/
  eta_squared : TripleToda h0 η h0
    (sphereProduct (m := 1) (n := 2) (k := 1) (l := 2) η η)
  /-- Consequence of the BHS low-stem ring: [h₀]·π_(2,3)=0.
  Together with graded commutativity it kills both indeterminacy summands
  of the preceding LOW bracket, not those of <2,θ₅,2>. -/
  low_indeterminacy : ∀ a : BiHom 2 3 (S_0_0 : Syn), sphereProduct h0 a = 0
  /-- Symmetric Toda identity at the only other degree used by this route.
  No claim that the bracket is a singleton or that θ is order two is made. -/
  symmetric_two : ∀ θ : BiHom 62 64 (S_0_0 : Syn), θ + θ = 0 →
    TripleToda syntheticTwo θ syntheticTwo (lambdaMultiply 2 (sphereProduct η θ))

/-- Internal source-to-model application: actual secondary Toda relations on
the same sphere and chosen h₀,η. No high-degree indeterminacy is removed. -/
structure TodaApplication (η : BiHom 1 2 (S_0_0 : Syn))
    (S : TodaSourceData (Syn := Syn)) : Prop where
  eta_squared : TripleToda S.h0 η S.h0
    (sphereProduct (m := 1) (n := 2) (k := 1) (l := 2) η η)
  symmetric_two : ∀ θ : BiHom 62 64 (S_0_0 : Syn), θ + θ = 0 →
    TripleToda syntheticTwo θ syntheticTwo (lambdaMultiply 2 (sphereProduct η θ))

/-- Assemble the unchanged consumer API from source ring facts and separately
certified secondary operations. This introduces no choice or axiom. -/
def todaInputsOfSource (η : BiHom 1 2 (S_0_0 : Syn)) (S : TodaSourceData (Syn := Syn))
    (A : TodaSourceResults D η S) (P : TodaApplication η S) : TodaInputs D η where
  h0 := S.h0
  h0_label := A.h0_label
  lambda_h0 := A.lambda_h0
  h0_eta := A.h0_eta
  eta_squared := P.eta_squared
  low_indeterminacy := A.low_indeterminacy
  symmetric_two := P.symmetric_two


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

/-- BHS A.1(2b),(3b). The same standard E₂ label detects the realized
class, and every specified detected class has an appropriate lift.
Neither clause replaces an arbitrary E₂ class by a later-page element. -/
structure RealizationDetection (R : RealizationCoordinates D) : Prop where
  /-- BHS A.1(2a): nonzero survival to E_(r+1) controls the lifetime
  of EVERY lift of a permanent cycle. The exponent is r-1, not r. -/
  lifetime : ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : E2 H (X.obj D.auxiliary) s t) (a : BiHom (t-s) t (nuZero D X)),
    x ∈ PageRepresentatives.permanentCycles H (X.obj D.auxiliary) (s,t) →
    SurvivesTo (adamsTowerInternalSpectralSequence H.unit (X.obj D.auxiliary))
      (r+1) (s,t) x → quotientClass 1 a = firstLabel D X s t x →
    lambdaMultiply (r-1) a ≠ 0
  detection : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t) (a : BiHom (t-s) t (nuZero D X)),
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit (X.obj D.auxiliary))
      (s,t) x → quotientClass 1 a = firstLabel D X s t x →
    TowerDetection.Detects (D.classicalConvergence X) (s,t) x (realizeNuZero D R X a)
  prescribed_lift : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t) (α : HomotopyGroup (t-s) (X.obj D.auxiliary)),
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit (X.obj D.auxiliary))
      (s,t) x → TowerDetection.Detects (D.classicalConvergence X) (s,t) x α →
    ∃ a : BiHom (t-s) t (nuZero D X),
      quotientClass 1 a = firstLabel D X s t x ∧ realizeNuZero D R X a = α
  /-- BHS A.1(3a): only SOME lift of a permanent boundary is torsion.
  It would be wrong to demand this of every lift. -/
  boundary_lift : ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ (y : E2 H (X.obj D.auxiliary) s t),
    y ∈ PageRepresentatives.permanentCycles H (X.obj D.auxiliary) (s,t) →
    HitOnPage (adamsTowerInternalSpectralSequence H.unit (X.obj D.auxiliary)) r (s,t) y →
    ∃ a : BiHom (t-s) t (nuZero D X),
      quotientClass 1 a = firstLabel D X s t y ∧ lambdaMultiply (r-1) a = 0

/-- The comparison data and laws travel together in A(M). -/
structure RealizationInput where
  coordinates : RealizationCoordinates D
  detection : RealizationDetection D coordinates


end
end KIP126.Literature.Route

namespace KIP126.Literature.Route
open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- These are model applicability obligations, recorded separately from
the source statements. They neither assert no-crossing computations nor
the ν-extension constructed in LWX Lemma 7.19. -/
structure Applicability : Prop where
  moss : MossTowerApplicability (H := H)
  nuCofiber : NuCofiberApplicability D


end
end KIP126.Literature.Route

namespace KIP126.Literature.Route
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn) (η : BiHom 1 2 (S_0_0 : Syn)) (L : TmfLabels H)

/-- Applied consumer facts, specialized to one model and η. This package
includes internal Main deductions and is not itself the external A(M).
The same tmf labels are used for the high class and its C(M) comparison.
`applicability` records source-to-model obligations separately so that a
source existence theorem cannot validate unrelated chosen lifts. -/
structure Inputs where
  classical : ClassicalInputs D η
  bx : BXDistinguishedInput D η
  synthetic : SyntheticInputs D
  realization : RealizationInput D
  algebra : AlgebraInput D
  may : MayInput Syn
  toda : TodaInputs D η
  tmf : TmfInputs D L
  moss : MossInput D
  applicability : Applicability D

/-- Internal source-application target, separate from A(M).
May retains its sign; Toda uses actual secondary-operation evidence; the
kernel and Moss statements use the fixed source/model comparisons. The
compatible normalized triple likewise requires
internal construction and multiplicative comparison. These fields are not
new independent external theorems or separately chosen stage witnesses. -/
structure Application {background : Background D} (B : Bindings D η L background) : Prop where
  bhsApplicability : BHSCompletionApplicability D B.bhsCompletion
  bhsComparison : BHSCompletionComparison D B.bhsCompletion
  realization : RealizationDetection D B.realization
  may : B.may.SignedBoundary
  toda : TodaApplication η B.todaSource
  realizationKernel : RealizationKernel D
  moss : MossInput D
  nuSource : NuCofiberSourceResults D B.nuSource
  nuCofiber : NuCofiberApplicability D

/-- Assemble the consumer API from the SAME sources, certified comparisons,
and the tmf consequences proved internally in Main. In particular, high125
survival is not transferred as part of the Challenge2 delivery. -/
def Statements.toInputs {background : Background D} {B : Bindings D η L background} (A : Statements D η L B)
    (P : Application D η L B) (tmf : TmfInputs D L) : Inputs D η L where
  classical := classicalInputsOfSource D η B.classicalSource A.classical
    B.classicalBinding B.synthetic_eta
  bx := A.bx
  synthetic := A.synthetic.toInputs D B.bhsCompletion P.bhsApplicability
    P.bhsComparison P.realizationKernel
  realization := ⟨B.realization, P.realization⟩
  algebra := B.algebra.withBinding D B.quotientBinding
  may := { B.may with boundary := P.may }
  toda := todaInputsOfSource D η B.todaSource A.toda P.toda
  tmf := tmf
  moss := P.moss
  applicability := ⟨B.moss, P.nuCofiber⟩


end KIP126.Literature.Route
