import KIP126.Interface.Challenge.Literature.Source
import KIP126.Def.StageInput.StandardSphere.Background.Fixed
import KIP126.Def.StageInput.StandardSphere.EInfty.Data
import KIP126.Def.ClassicalAdams.Tmf.Br21.Data

/-! Literature delivery: source choices and truthful comparisons, followed by
the exact source results. The mathematical route is fixed independently in Def. -/
namespace KIP126.Challenge2
open CategoryTheory Classical.Adams Core.SpectralSequence
open StableHomotopy StableHomotopy.Cohomology Synthetic.Context Synthetic.SpectralSequence
open Literature.Route Classical.Adams.PageRepresentatives Kervaire.Route Synthetic
set_option autoImplicit false

/-- Moss's conclusion on the selected composition and convergence data. -/
def StandardSphereMossStatement (context : StandardSphereMossContext) : Prop :=
  let c := KIP126.Def.StageInput.witness
  letI : Foundation.TensorInput c.foundationInput := c.tensorInput
  Classical.Adams.Moss.Statement c.foundationInput.hf2 c.cooperationInput.ring
    context.composition
    (fun _ : Unit => StableHomotopy.SphereSpectrum (C := c.foundationInput.Spectrum))
    context.convergence


/-- Sources and their comparisons with the one fixed Def background.
No program presentation or internal paper conclusion is selected here. -/
structure LiteratureBindings where
  tmfLabels : Literature.Route.TmfLabels standardFoundation.hf2
  route : Literature.Route.Bindings standardRouteModel Def.standardRouteEta
    tmfLabels Def.standardRouteBackground
  br21Classes : Tmf.Br21Classes standardFoundation.hf2 route.tmfSource.spectrum
  eInfty_nu : NuEInftyFormula standardFoundation.hf2 standardRouteModel.nu standardRouteModel.family
  eInfty_quotient : FiniteEInftyFormula standardFoundation.hf2 standardRouteModel.nu standardRouteModel.family
  eInfty_specialFiber : ∀ (X : standardFoundation.Spectrum) (p : ℤ × ℤ) (w : ℤ),
    ((standardRouteModel.family.nuQuotient standardRouteModel.nu X 1).sequence.ssData (p.1, p.2, w)).eInfty ≃ₗ[ℤ]
      finiteEInftyModel standardFoundation.hf2 X 1 p w

namespace LiteratureBindings

/-- The E∞ comparison uses the one set of delivered source coordinates. -/
noncomputable def eInftyPresentation (bindings : LiteratureBindings) :
    EInftyFormulaInput standardRouteModel where
  nu := bindings.eInfty_nu
  quotient := bindings.eInfty_quotient
  specialFiber := bindings.eInfty_specialFiber

/-- The weight comparison is fixed by the actual Adams tower construction,
not independently selected by a literature delivery. -/
noncomputable def eInftyWeightShift (_bindings : LiteratureBindings) :
    EInftyWeightShift standardRouteModel.family :=
  Def.standardEInftyWeightShift

end LiteratureBindings

/-- Individual prior results on the same source bindings. Consumer views in Solution
are assembled from these fields and introduce no independent input. -/
structure LiteratureResults (bindings : LiteratureBindings) : Prop where
  /-- BR21 Table 5.4 / Theorem 5.18 on the source endpoint classes.
  This asserts only the differential equation, with no extra survival claim. -/
  br21 : HasDifferential
    (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit
      bindings.route.tmfSource.spectrum) 3 (16, 112) (19, 114)
    bindings.br21Classes.v2Sixteen bindings.br21Classes.betaGFour
  moss : StandardSphereMossStatement Def.standardSphereMossContext
  sphereVanishing : SphereVanishingLine standardFoundation.hf2
  adamsOneLine_d2 (j : ℕ) (hj : 4 ≤ j) :
      HasNonzeroDifferential sphereAdamsData 2
        (1, ((2 ^ j : ℕ) : ℤ)) (3, ((1 + 2 ^ (j - 1 + 1) : ℕ) : ℤ))
        (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations j)
        (Sphere.Internal.h0HiSquare standardFoundation.hf2 standardMilnorCooperations (j - 1))
  classical_h5Square_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum) (2,64)
      (Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations 5)
  classical_theta5_detection : TowerDetection.Detects bindings.route.classicalSource.convergence (2,64)
    (Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations 5) bindings.route.classicalSource.theta5
  classical_theta5_order_two : bindings.route.classicalSource.theta5 + bindings.route.classicalSource.theta5 = 0
  classical_stem62_exponent_two : ∀ a : HomotopyGroup (C := standardFoundation.Spectrum) 62 SphereSpectrum, a+a=0
  classical_theta5_filtration_gap : ∀ a b : HomotopyGroup (C := standardFoundation.Spectrum) 62 SphereSpectrum,
    TowerDetection.Detects bindings.route.classicalSource.convergence (2,64) (Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations 5) a →
    TowerDetection.Detects bindings.route.classicalSource.convergence (2,64) (Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations 5) b →
    a-b ∈ TowerDetection.filtrationSubmodule standardFoundation.hf2.unit SphereSpectrum 6 62
  classical_two_detection : TowerDetection.Detects bindings.route.classicalSource.convergence (1,1) (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 0)
    ((shiftFunctorZero standardFoundation.Spectrum ℤ).hom.app SphereSpectrum ≫ (2 • 𝟙 _))
  classical_eta_detection : TowerDetection.Detects bindings.route.classicalSource.convergence (1,2) (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 1) bindings.route.classicalSource.eta
  classical_nu_detection : TowerDetection.Detects bindings.route.classicalSource.convergence (1,4) (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 2) bindings.route.classicalSource.nu
  classical_eta_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum) (1,2) (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 1)
  classical_nu_permanent : NonzeroSurvival
    (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum) (1,4) (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 2)
  route_bx : BXDistinguishedInput standardRouteModel Def.standardRouteEta
  route_realizationKernel : RealizationKernelSourceResults standardRouteModel bindings.route.kernelSource
  route_may : MaySourceResults Def.standardRouteInput.Syn bindings.route.may
  synthetic_nu_cofiber : NuCofiberCriterion standardFoundation.hf2 standardRouteModel.nu
  synthetic_lift : SyntheticLiftComparison standardFoundation.hf2 standardRouteModel.nu
  synthetic_triangle_lift : SyntheticTriangleLiftComparison standardFoundation.hf2 standardRouteModel.nu
  synthetic_finite_lift : FiniteLiftCriterion standardRouteModel
  synthetic_bockstein : BocksteinDifferential standardRouteModel
  synthetic_permanent_lift : ∀ (X : standardFoundation.Spectrum) (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X → BHSPermanentLiftAt standardRouteModel X
  synthetic_differentials : DifferentialRigidity standardRouteModel
  synthetic_filtration_lambda : ∀ (X : standardFoundation.Spectrum) (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X → BHSFiltrationLambdaAt standardRouteModel X
  synthetic_e2_weight_vanishing : E2WeightVanishing standardRouteModel
  synthetic_finite_quotient_page_vanishing : FiniteQuotientPageVanishing standardRouteModel
  eInfty_lambda_nu : ∀ (X : standardFoundation.Spectrum) (k : ℕ) (p : ℤ × ℤ) (w : ℤ) (hw : w ≤ p.2)
    (x : ((standardRouteModel.family.nu standardRouteModel.nu X).sequence.ssData (p.1, p.2, w)).eInfty),
    bindings.eInftyPresentation.nuWindow X p (w - k) (by omega) (bindings.eInftyWeightShift.lambdaMap (standardRouteModel.nu.functor.obj X) k p w x) =
      permanentQuotientMap standardFoundation.hf2 X (by omega) p (bindings.eInftyPresentation.nuWindow X p w hw x)
  eInfty_lambda_finite : ∀ (X : standardFoundation.Spectrum) (q k : ℕ) (hkq : k < q) (p : ℤ × ℤ) (w : ℤ)
    (hw : 0 ≤ p.2 - w ∧ p.2 - w < (q - k : ℕ))
    (x : ((standardRouteModel.family.nuQuotient standardRouteModel.nu X (q - k)).sequence.ssData (p.1, p.2, w)).eInfty),
    bindings.eInftyPresentation.finiteWindow X q (by omega) p (w - k) (by constructor <;> omega)
        (bindings.eInftyWeightShift.finiteLambdaMap (standardRouteModel.quotientTower (standardRouteModel.nu.functor.obj X)) q k hkq p w x) =
      quotientMap standardFoundation.hf2 X (by omega) (by omega) p
        (bindings.eInftyPresentation.finiteWindow X (q - k) (by omega) p w hw x)
  eInfty_rho_finite : ∀ (X : standardFoundation.Spectrum) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j)
    (p : ℤ × ℤ) (w : ℤ) (hw : 0 ≤ p.2 - w ∧ p.2 - w < i)
    (x : ((standardRouteModel.family.nuQuotient standardRouteModel.nu X j).sequence.ssData (p.1, p.2, w)).eInfty),
    bindings.eInftyPresentation.finiteWindow X i hi p w hw
        (((standardRouteModel.family.functor.map ((standardRouteModel.quotientTower (standardRouteModel.nu.functor.obj X)).rho i j hij)).eInftyMap (p.1, p.2, w)).hom x) =
      quotientMap standardFoundation.hf2 X (by omega) (le_refl (1 + p.2 - w)) p
        (bindings.eInftyPresentation.finiteWindow X j (by omega) p w (by constructor <;> omega) x)
  eInfty_rho_nu : ∀ (X : standardFoundation.Spectrum) (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ) (w : ℤ)
    (hw : 0 ≤ p.2 - w ∧ p.2 - w < q)
    (x : ((standardRouteModel.family.nu standardRouteModel.nu X).sequence.ssData (p.1, p.2, w)).eInfty),
    bindings.eInftyPresentation.finiteWindow X q hq p w hw
        (((standardRouteModel.family.quotientProjection (standardRouteModel.nu.functor.obj X) q).eInftyMap (p.1, p.2, w)).hom x) =
      permanentToFinite standardFoundation.hf2 X (q - p.2 + w) (1 + p.2 - w) p
        (bindings.eInftyPresentation.nuWindow X p w (by omega) x)
  eInfty_labels : Literature.Route.EInftyLabelAgreement standardRouteModel bindings.eInftyPresentation
  realization_lifetime : ∀ (X : standardFoundation.Spectrum)
    (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X →
    ∀ _convergence : TowerDetection.Convergence standardFoundation.hf2.unit X,
    ∀ (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : E2 standardFoundation.hf2 X s t) (a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (standardRouteModel.nu.functor.obj X))),
    x ∈ PageRepresentatives.permanentCycles standardFoundation.hf2 X (s,t) →
    SurvivesTo (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit X)
      (r+1) (s,t) x → quotientClass 1 a = bhsFirstLabel standardRouteModel X s t x →
    lambdaMultiply (r-1) a ≠ 0
  realization_detection : ∀ (X : standardFoundation.Spectrum)
    (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X →
    ∀ convergence : TowerDetection.Convergence standardFoundation.hf2.unit X,
    ∀ (s t : ℤ)
    (x : E2 standardFoundation.hf2 X s t) (a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (standardRouteModel.nu.functor.obj X))),
    NonzeroSurvival (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit X)
      (s,t) x → quotientClass 1 a = bhsFirstLabel standardRouteModel X s t x →
    TowerDetection.Detects convergence (s,t) x (realizeNuZeroObject standardRouteModel bindings.route.realization X a)
  realization_prescribed_lift : ∀ (X : standardFoundation.Spectrum)
    (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X →
    ∀ convergence : TowerDetection.Convergence standardFoundation.hf2.unit X,
    ∀ (s t : ℤ)
    (x : E2 standardFoundation.hf2 X s t) (α : HomotopyGroup (t-s) X),
    NonzeroSurvival (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit X)
      (s,t) x → TowerDetection.Detects convergence (s,t) x α →
    ∃ a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (standardRouteModel.nu.functor.obj X)),
      quotientClass 1 a = bhsFirstLabel standardRouteModel X s t x ∧ realizeNuZeroObject standardRouteModel bindings.route.realization X a = α
  realization_boundary_lift : ∀ (X : standardFoundation.Spectrum)
    (products : CategoryTheory.Limits.HasProductsOfShape ℕ standardFoundation.Spectrum),
    BHSObjectApplicability products standardFoundation.hf2.unit X →
    ∀ _convergence : TowerDetection.Convergence standardFoundation.hf2.unit X,
    ∀ (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ (y : E2 standardFoundation.hf2 X s t),
    y ∈ PageRepresentatives.permanentCycles standardFoundation.hf2 X (s,t) →
    HitOnPage (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit X) r (s,t) y →
    ∃ a : BiHom (t-s) t ((SyntheticCategory.biShift (0,0)).obj (standardRouteModel.nu.functor.obj X)),
      quotientClass 1 a = bhsFirstLabel standardRouteModel X s t y ∧ lambdaMultiply (r-1) a = 0
  toda_h0_label : standardRouteModel.sphereFirstQuotient 1 1 (quotientClass 1 bindings.route.todaSource.h0) = Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 0
  toda_lambda_h0 : lambdaMultiply 1 bindings.route.todaSource.h0 = syntheticTwo
  toda_h0_eta : sphereProduct bindings.route.todaSource.h0 Def.standardRouteEta = 0
  toda_low_indeterminacy : ∀ a : BiHom 2 3 (S_0_0 : Def.standardRouteInput.Syn), sphereProduct bindings.route.todaSource.h0 a = 0
  tmf_connective : ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n bindings.route.tmfSource.spectrum)
  tmf_finiteMod2Type : FiniteMod2Type standardFoundation.hf2 bindings.route.tmfSource.spectrum
  tmf_standard_labels : bindings.route.tmfSource.labels.Standard
  tmf_vanishing62 : ∀ x : HomotopyGroup (C := standardFoundation.Spectrum) 62 bindings.route.tmfSource.spectrum, x = 0
  tmf_low_filtration63 : ∀ s : ℤ, s ≤ 0 → Subsingleton (E2 standardFoundation.hf2 bindings.route.tmfSource.spectrum s (63+s))
  tmf_kappaBar_detection : TowerDetection.Detects bindings.route.tmfSource.sphereConvergence (4,24)
    bindings.route.tmfSource.labels.g bindings.route.tmfSource.kappaBar
  tmf_w_detection : TowerDetection.Detects bindings.route.tmfSource.sphereConvergence (9,54)
    bindings.route.tmfSource.labels.delta_h_1_mul_g bindings.route.tmfSource.wClass
  tmf_high125_nonzero : bindings.route.tmfSource.high125 ≫ bindings.route.tmfSource.unit ≠ 0

/-- One literature delivery, whose results use exactly its source bindings. -/
structure LiteratureInterface where
  bindings : LiteratureBindings
  results : LiteratureResults bindings

end KIP126.Challenge2
