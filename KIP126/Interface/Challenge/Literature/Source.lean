import KIP126.Def.StageInput.StandardSphere.Background.Data
import KIP126.Def.StageInput.StandardSphere.Classes.Family

/-! Parameterized literature statements and correlated source bindings.
These describe prior results on specified objects; model applications and
consumer assembly are declared in Interface/Solution/Literature/Applications. -/

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

/-- BHS A.9/A.11 with the compatible E∞ formulas on the SAME family.
All label, λ and ρ compatibility is part of the supplied source application.
No unrelated E∞ equivalences may be inserted as substitutes. -/
structure EInftyInput where
  presentation : KIP126.Literature.Route.EInftyFormulaInput D
  weightShift : EInftyWeightShift D.family
  maps : KIP126.Literature.Route.EInftyCompatibilityInput D presentation weightShift
  labels : KIP126.Literature.Route.EInftyLabelAgreement D presentation

/-- External BHS inputs excluding the internal full-to-selected-model kernel transport. -/
structure SyntheticSourceInputs where
  lifts : KIP126.Literature.Route.SyntheticLiftInput D
  finite_lift : FiniteLiftCriterion D
  bockstein : BocksteinDifferential D
  /-- BHS A.1(2), retaining the source object's actual convergence conditions. -/
  permanent_lift : ∀ (X : C) (products : CategoryTheory.Limits.HasProductsOfShape ℕ C),
    BHSObjectApplicability products H.unit X → BHSPermanentLiftAt D X
  differentials : DifferentialRigidity D
  eInfty : EInftyInput D
  /-- BHS cor:tau-surj, before transporting back from completed objects. -/
  filtration_lambda : ∀ (X : C) (products : CategoryTheory.Limits.HasProductsOfShape ℕ C),
    BHSObjectApplicability products H.unit X → BHSFiltrationLambdaAt D X
  e2_weight_vanishing : E2WeightVanishing D
  /-- BHS A.11 (1),(3): both zero regions on every finite page, including E2. -/
  finite_quotient_page_vanishing : FiniteQuotientPageVanishing D


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

/-- Xu Cor.1.3, the IWX 62-stem computation and the ordinary low-stem
Hopf detections, with one actual convergence and concrete homotopy maps.
No synthetic or arbitrary-choice strengthening is included. -/
structure ClassicalSourceResults (M : MilnorCooperations H) (S : ClassicalSourceData H) : Prop where
  h5Square_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (2,64)
      (Sphere.Internal.hiSquare H M 5)
  theta5_detection : TowerDetection.Detects S.convergence (2,64)
    (Sphere.Internal.hiSquare H M 5) S.theta5
  theta5_order_two : S.theta5 + S.theta5 = 0
  stem62_exponent_two : ∀ a : HomotopyGroup (C := C) 62 SphereSpectrum, a+a=0
  theta5_filtration_gap : ∀ a b : HomotopyGroup (C := C) 62 SphereSpectrum,
    TowerDetection.Detects S.convergence (2,64) (Sphere.Internal.hiSquare H M 5) a →
    TowerDetection.Detects S.convergence (2,64) (Sphere.Internal.hiSquare H M 5) b →
    a-b ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 6 62
  two_detection : TowerDetection.Detects S.convergence (1,1) (Sphere.Internal.hi H M 0)
    ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ (2 • 𝟙 _))
  eta_detection : TowerDetection.Detects S.convergence (1,2) (Sphere.Internal.hi H M 1) S.eta
  nu_detection : TowerDetection.Detects S.convergence (1,4) (Sphere.Internal.hi H M 2) S.nu
  eta_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (1,2) (Sphere.Internal.hi H M 1)
  nu_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (1,4) (Sphere.Internal.hi H M 2)

def ClassicalSourceExistence (H : Mod2EilenbergMacLane (C := C))
    (M : MilnorCooperations H) : Prop :=
  ∃ S : ClassicalSourceData H, ClassicalSourceResults M S

variable {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]


end KIP126.Literature.Route

namespace KIP126.Literature.Route
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.Synthetic.Context
universe u v
variable (Syn : Type u) [SyntheticCategory.{u, v} Syn]

/-- May's source result, on specified tensor suspension conventions. The
existence of this source input on the selected synthetic model remains a
production obligation; no fresh model or global witness is selected here. -/
def MaySourceResults (B : MayContext Syn) : Prop :=
  ∀ T U : HoCofiberSequence (C := Syn), Nonempty (MayPushpullData Syn B T U)


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

/-- BHS `prop:syn-toda-range`, low-ring/label consequences on the selected
sphere. These equations do not prove a secondary Toda membership. -/
structure TodaSourceResults (η : BiHom 1 2 (S_0_0 : Syn))
    (S : TodaSourceData (Syn := Syn)) : Prop where
  h0_label : D.sphereFirstQuotient 1 1 (quotientClass 1 S.h0) = Sphere.Internal.hi H M 0
  lambda_h0 : lambdaMultiply 1 S.h0 = syntheticTwo
  h0_eta : sphereProduct S.h0 η = 0
  low_indeterminacy : ∀ a : BiHom 2 3 (S_0_0 : Syn), sphereProduct S.h0 a = 0


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

/-- BHS A.1(2a),(2b),(3a),(3b) on ONE source object and its canonical
classical convergence. Applicability is retained in BHSRealizationSourceResults. -/
structure BHSRealizationDetectionAt (R : RealizationCoordinates D) (X : C)
    (convergence : TowerDetection.Convergence H.unit X) : Prop where
  /-- BHS A.1(2a): nonzero survival to E_(r+1) controls the lifetime
  of EVERY lift of a permanent cycle. The exponent is r-1, not r. -/
  lifetime : ∀ (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : E2 H X s t) (a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X))),
    x ∈ PageRepresentatives.permanentCycles H X (s,t) →
    SurvivesTo (adamsTowerInternalSpectralSequence H.unit X)
      (r+1) (s,t) x → quotientClass 1 a = bhsFirstLabel D X s t x →
    lambdaMultiply (r-1) a ≠ 0
  detection : ∀ (s t : ℤ)
    (x : E2 H X s t) (a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X))),
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit X)
      (s,t) x → quotientClass 1 a = bhsFirstLabel D X s t x →
    TowerDetection.Detects convergence (s,t) x (realizeNuZeroObject D R X a)
  prescribed_lift : ∀ (s t : ℤ)
    (x : E2 H X s t) (α : HomotopyGroup (t-s) X),
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit X)
      (s,t) x → TowerDetection.Detects convergence (s,t) x α →
    ∃ a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X)),
      quotientClass 1 a = bhsFirstLabel D X s t x ∧ realizeNuZeroObject D R X a = α
  /-- BHS A.1(3a): only SOME lift of a permanent boundary is torsion.
  It would be wrong to demand this of every lift. -/
  boundary_lift : ∀ (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ (y : E2 H X s t),
    y ∈ PageRepresentatives.permanentCycles H X (s,t) →
    HitOnPage (adamsTowerInternalSpectralSequence H.unit X) r (s,t) y →
    ∃ a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj X)),
      quotientClass 1 a = bhsFirstLabel D X s t y ∧ lambdaMultiply (r-1) a = 0

/-- The completed-source BHS theorem. No assertion is made here for an
uncompleted selected X; the actual source hypotheses must be supplied. -/
def BHSRealizationSourceResults (R : RealizationCoordinates D) : Prop :=
  ∀ (X : C) (products : CategoryTheory.Limits.HasProductsOfShape ℕ C),
    BHSObjectApplicability products H.unit X →
    ∀ convergence : TowerDetection.Convergence H.unit X,
      BHSRealizationDetectionAt D R X convergence


end
end KIP126.Literature.Route

namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
noncomputable section
variable (Syn : Type w) [SyntheticCategory.{w, v} Syn]

variable {Syn}

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- Consequence of full-category telescope localization and compact source
spheres, restricted to the INCLUDED route objects. It is supplied as a source
result, never inferred from compactness of the completed sphere. -/
def RealizationKernelSourceResults (S : RealizationKernelSourceData Syn) : Prop :=
  ∀ (X : SyntheticObject) (m w : ℤ)
    (a : BiHom m w (S.inclusion.obj (X.obj D.nu D.auxiliary))),
    (S.localization.endofunctor.map a = 0 ↔ ∃ k : ℕ, lambdaMultiply k a = 0)


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

/-- BMQ v4 (2021), Figure 1.1, §2 and §7, after the explicitly separate
2-local-to-2-complete transport. In §7 the nonzero class is the image of
the actual product kappaBar^4*w. The stronger universal statement about
ALL classes detected by g^4 Delta h1 g is deliberately absent. -/
structure TmfSourceResults (S : TmfSourceData H) : Prop where
  /-- The source is connective tmf with degreewise finite mod-2 homology.
  These are the scope facts needed for BHS completion/convergence after
  transport; local values in stems 62/125 alone would not imply them. -/
  connective : ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n S.spectrum)
  finiteMod2Type : FiniteMod2Type H S.spectrum
  standard_labels : S.labels.Standard
  vanishing62 : ∀ x : HomotopyGroup (C := C) 62 S.spectrum, x = 0
  low_filtration63 : ∀ s : ℤ, s ≤ 0 → Subsingleton (E2 H S.spectrum s (63+s))
  kappaBar_detection : TowerDetection.Detects S.sphereConvergence (4,24)
    S.labels.g S.kappaBar
  w_detection : TowerDetection.Detects S.sphereConvergence (9,54)
    S.labels.delta_h_1_mul_g S.wClass
  high125_nonzero : S.high125 ≫ S.unit ≠ 0

/-- Exact existence form of the accepted local BMQ/IWX source result in
an identified completed classical sphere model. It does not assert the
results for every detector, every label or every preselected route D.
A consumer supplies `TmfBinding` before applying the source result to D.
The standard-model source/2-completion adapter must construct this witness
from BMQ v4 and the finite IWX label computations; no global choice is
performed in this definition. -/
def TmfSourceExistence (H : Mod2EilenbergMacLane (C := C)) : Prop :=
  ∃ S : TmfSourceData H, TmfSourceResults S


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

/-- Predicate for Main's local Moss conclusion on the CLASSICAL sphere resolution.
It has no synthetic-model parameter. Its derivation must identify the
displayed convergence with the comparison from that actual multiplicative
Adams resolution; an arbitrary associated-graded isomorphism does not
establish applicability. All defining-system, crossing and residual
hypotheses are retained. Main derives it from the general Moss literature
statement; this definition does not assert it or add a Challenge2 field. -/
def MossSourceInput (M : MilnorCooperations H)
    (convergence : TowerDetection.Convergence H.unit SphereSpectrum) : Prop :=
  ∀ (B : E2 H SphereSpectrum 8 70)
    (θ β : HomotopyGroup (C := C) 62 SphereSpectrum)
    (two : HomotopyGroup (C := C) 0 SphereSpectrum),
    two = (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ (2 • 𝟙 _) →
    TowerDetection.Detects convergence (2,64) (Sphere.Internal.hiSquare H M 5) θ →
    TowerDetection.Detects convergence (1,1) (Sphere.Internal.hi H M 0) two →
    TowerDetection.Detects convergence (8,70) B β →
    θ + θ = 0 → β + β = 0 →
    (ThetaBMassey M B).Nonempty →
    ¬ SphereMossCrossing (H := H) 3 (3,65) →
    ¬ SphereMossCrossing (H := H) 3 (9,71) →
    TowerDetection.ResidualInjectivity H.unit (SphereSpectrum (C := C)) →
    ∃ (z : E2 H SphereSpectrum 9 134)
      (ξ : HomotopyGroup (C := C) 125 SphereSpectrum),
      ThetaBMasseyDefiningSystem M B z ∧
      TowerDetection.Detects convergence (9,134) z ξ ∧ ThetaBToda θ β ξ


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

/-- Internal construction target for a compatible triple, with cofiber
maps and the h2 label. Pstragowski Lemma 4.23 and BHS Lemma 9.15 supply
the separate exactness and divisibility leaves; neither is quoted as
the full compatible-three-lifts-and-label statement below. The assembly
must also use actual Hopf detection and the first-quotient comparison.
This asserts nothing about arbitrary selected lifts. -/
structure NuCofiberSourceResults (S : NuCofiberSourceData D) : Prop where
  nu_exponent : normalizedExponent H D.auxiliary.nuMap = 1
  bottom_exponent : normalizedExponent H D.auxiliary.nuRouteTriangle.g = 0
  top_exponent : normalizedExponent H D.auxiliary.nuRouteTriangle.h = 0
  normalized_label :
    D.sphereFirstQuotient 1 4 (quotientClass 1 (sourceNormalizedNu D S nu_exponent)) =
      Sphere.Internal.hi H M 2
  triangle : ∀ he, sourceNormalizedTriangle D S he ∈ distTriang Syn

/-- Internal model-adaptation target for the identified nu background.
It is not a permissible replacement for the separate Pstragowski/BHS
source leaves in Main/Axiom. Its construction and the subsequent binding
of D's normalized maps remain separate proof responsibilities. -/
def NuCofiberSourceExistence : Prop :=
  ∃ S : NuCofiberSourceData D, NuCofiberSourceResults D S


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

/-- Source choices and model comparisons for ONE delivered route. These
are internal construction obligations, separate from the source results. -/
structure Bindings (background : Background D) where
  todaSource : TodaSourceData (Syn := Syn)
  kernelSource : RealizationKernelSourceData Syn
  kernelBinding : RealizationKernelBinding D kernelSource
  classicalSource : ClassicalSourceData H
  classicalBinding : ClassicalSourceBinding D η classicalSource
  synthetic_eta : EtaChoice M D.toModelData η
  tmfSource : TmfSourceData H
  tmfBinding : TmfBinding D L tmfSource
  bhsCompletion : BHSCompletionData D
  /-- Truth of the source hypotheses and of the transport along this same completion. -/
  completionApplicability : BHSCompletionApplicability D bhsCompletion
  completionComparison : BHSCompletionComparison D bhsCompletion
  realizationComparison : BHSRealizationComparison D background.realization bhsCompletion
  /-- The completion source for the detector is the SAME completed tmf,
  and its comparison carries the SAME actual ring unit. -/
  bhsDetectorIso : bhsCompletion.completed .detector ≅ tmfSource.spectrum
  bhsDetectorUnit : D.auxiliary.detectorUnit ≫ bhsCompletion.map .detector ≫
    bhsDetectorIso.hom = tmfSource.unit
  nuSource : NuCofiberSourceData D
  nuBinding : NuCofiberLiftBinding D nuSource
  moss : MossTowerApplicability (H := H)

namespace Bindings
variable {D η L} {background : Background D}
abbrev realization (_B : Bindings D η L background) := background.realization
abbrev algebra (_B : Bindings D η L background) := background.algebra
abbrev quotientBinding (_B : Bindings D η L background) := background.quotientBinding
abbrev algebraBinding (_B : Bindings D η L background) := background.algebraBinding
abbrev may (_B : Bindings D η L background) := background.may
abbrev realizationAdditive (_B : Bindings D η L background) := background.realizationAdditive
abbrev weights (_B : Bindings D η L background) := background.weights
abbrev nuE2 (_B : Bindings D η L background) := background.nuE2
end Bindings

/-- External results on the source objects fixed in B. Classical and tmf
results are not asserted for arbitrary preselected route objects or lifts. -/
structure Statements {background : Background D} (B : Bindings D η L background) where
  classical : ClassicalSourceResults M B.classicalSource
  bx : BXDistinguishedInput D η
  synthetic : SyntheticSourceInputs D
  realizationKernel : RealizationKernelSourceResults D B.kernelSource
  realization : BHSRealizationSourceResults D B.realization
  may : MaySourceResults Syn B.may
  toda : TodaSourceResults D η B.todaSource
  tmf : TmfSourceResults B.tmfSource
  moss : MossSourceInput M B.classicalSource.convergence


end KIP126.Literature.Route

namespace KIP126.Challenge2
open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams Core.SpectralSequence
universe u v w

section Moss

open StableHomotopy StableHomotopy.Cohomology Classical.Adams.Moss

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated] [MonoidalPreadditive C]
  [∀ A : C, (tensorLeft A).CommShift ℤ]

/-- Compatibility package retaining its original fields and constructor.
The source-bearing Moss conclusion is separated from this context in Challenge2. -/
structure MossInterface {ι : Type w} (objects : ι → C) where
  composition : CompositionPairing H R
  coherent : composition.Coherent H R
  convergence : ∀ X Y : ι, MappingAdamsConvergence H.unit (objects X) (objects Y)
  weak_convergence : ∀ X Y : ι, MappingAdamsTower H.unit (objects X) (objects Y)
  detection : ∀ X Y Z : ι,
    composition.DetectionCompatible H R (objects X) (objects Y) (objects Z)
      (convergence X Y) (convergence Y Z) (convergence X Z)
  indeterminacy : ∀ (r : ℤ) (hr : 3 ≤ r) (W X Y Z : ι) (i j k : ℤ × ℤ)
    (a : (mappingSequence H.unit (objects W) (objects X)).Page r i)
    (b : (mappingSequence H.unit (objects X) (objects Y)).Page r j)
    (c : (mappingSequence H.unit (objects Y) (objects Z)).Page r k)
    (x₀ x : (mappingSequence H.unit (objects W) (objects Z)).Page r
      (PageMassey.degree r i j k)),
    PageMassey.Relation H R composition r hr x₀ a b c →
      (PageMassey.Relation H R composition r hr x a b c ↔
        PageMassey.Indeterminacy H R composition r (j := j) a c (x - x₀))
  moss : Classical.Adams.Moss.Statement H R composition objects convergence


end Moss

/-- am8/am15 的固定球面交付；基础、HF₂、ring 与所有 tensor 选择
均来自 Def 的同一个固定实现，没有增加另一个可独立选择的模型。
这里的球面映射谱仍需通过实际 ihom(unit,unit) 同构与 sphereAdamsData 比较。
保留原兼容接口；总包分别存放 context 与文献结论。 -/
def StandardSphereMossInterface : Type 1 :=
  let c := KIP126.Def.StageInput.witness
  letI : Foundation.TensorInput c.foundationInput := c.tensorInput
  MossInterface c.foundationInput.hf2 c.cooperationInput.ring
    (fun _ : Unit => StableHomotopy.SphereSpectrum (C := c.foundationInput.Spectrum))

end KIP126.Challenge2
