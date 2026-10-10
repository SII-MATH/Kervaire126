import KIP126.Def.ClassicalAdams.SphereSequence.Data
import KIP126.Def.Algebra.Coefficients.Data
import KIP126.Def.Synthetic.AdamsSequence.Data
import KIP126.Def.StableHomotopy.Context.Data

/-!
# Stable and synthetic data used by the Kervaire endpoint

These structures are interfaces.  They carry the maps, graded groups, and
coherence data that an endpoint proof must consume; they do not assert any
external computation or permanence result.
-/

namespace KIP126.Kervaire

open KIP126.Classical.Adams
open KIP126.Core.Algebra
open KIP126.Synthetic.SpectralSequence

/-- A synthetic stable context with the deformation element and its quotients. -/
structure SyntheticHomotopyContext (C : StableHomotopyContext) where
  Spectrum : Type
  sphere : Spectrum
  homotopy : ℤ × ℤ → Spectrum → Type
  homotopyAddCommGroup : ∀ (d : ℤ × ℤ) (X : Spectrum),
    AddCommGroup (homotopy d X)
  lambda : homotopy (0, -1) sphere
  lambdaPower : ∀ n : ℕ, homotopy (0, -n) sphere
  quotient : ℕ → Spectrum → Spectrum
  quotientMap : ∀ (_n : ℕ) (_X : Spectrum), Spectrum → Spectrum
  unit : Spectrum
  unitIso : unit = sphere

attribute [instance] SyntheticHomotopyContext.homotopyAddCommGroup

/-- A detected synthetic class, retaining both its page representative and
its abutment value. -/
structure SyntheticDetectedClass
    {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    (A : SyntheticAdamsSS) where
  degree : Tridegree
  representative : A.E₂ degree
  abutment : S.homotopy (degree.1, degree.2.2) S.sphere

/-- The chosen $θ_5$ and $η$ data used by the near-126 conditions. -/
structure SyntheticTheta5EtaData
    {C : StableHomotopyContext} (S : SyntheticHomotopyContext C)
    (A : SyntheticAdamsSS) where
  theta5 : S.homotopy (62, 64) S.sphere
  theta5Detected : SyntheticDetectedClass (S := S) A
  theta5Degree : theta5Detected.degree = (5, 32, 32)
  eta : S.homotopy (1, 2) S.sphere
  etaDetected : SyntheticDetectedClass (S := S) A
  etaDegree : etaDetected.degree = (1, 2, 2)
  quotientImage : ∀ (n : ℕ), S.homotopy (62, 64) S.sphere →
    S.homotopy (62, 64) (S.quotient n S.sphere)

/-- Page and abutment operations needed to state the three near-126
conditions.  Every operation is supplied with its typing data. -/
structure Near126Input
    {C : StableHomotopyContext} (S : SyntheticHomotopyContext C)
    (A : SyntheticAdamsSS) where
  x_126_8_4 : A.E₂ (8, 16, 4)
  x_126_8 : A.E₂ (8, 16, 4)
  d6 : A.E₂ (8, 16, 4) →ₗ[ℤ] A.E₂ (14, 21, 4)
  x_124_8 : A.E₂ (8, 16, 8)
  x_109_12 : A.E₂ (12, 24, 12)
  h_0_sq_mul_x_124_8 : S.homotopy (124, 128) S.sphere
  h_1_mul_h_4_mul_x_109_12 : S.homotopy (125, 133) S.sphere
  etaAction : S.homotopy (124, 128) S.sphere → S.homotopy (125, 133) S.sphere
  lambda6 : S.homotopy (124, 128) S.sphere → S.homotopy (124, 128) S.sphere
  lambda3 : S.homotopy (125, 133) S.sphere → S.homotopy (125, 133) S.sphere
  lambda_pow_six_on_h_1_mul_h_4 : S.homotopy (125, 133) S.sphere → S.homotopy (125, 133) S.sphere
  theta5Square : S.homotopy (124, 128) S.sphere

namespace Near126Input

variable {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
  {A : SyntheticAdamsSS}

/-- The three named conditions from the near-126 argument. -/
def c3 (D : Near126Input S A) : Prop :=
  D.d6 (D.x_126_8_4 + D.x_126_8) = 0

def c4 (D : Near126Input S A) : Prop :=
  D.theta5Square = D.lambda6 D.h_0_sq_mul_x_124_8 ∧ D.theta5Square ≠ 0

def c5 (D : Near126Input S A) : Prop :=
  D.lambda3 (D.etaAction D.h_0_sq_mul_x_124_8) =
    D.lambda_pow_six_on_h_1_mul_h_4 D.h_1_mul_h_4_mul_x_109_12

end Near126Input

/-- The exact propositional forms of $C_3$, $C_4$, and $C_5$. -/
structure Near126Conditions
    {C : StableHomotopyContext} {S : SyntheticHomotopyContext C}
    {A : SyntheticAdamsSS} (D : Near126Input S A) where
  C3 : D.d6 (D.x_126_8_4 + D.x_126_8) = 0
  C4 : D.theta5Square = D.lambda6 D.h_0_sq_mul_x_124_8 ∧
    D.theta5Square ≠ 0
  C5 : D.lambda3 (D.etaAction D.h_0_sq_mul_x_124_8) =
    D.lambda_pow_six_on_h_1_mul_h_4 D.h_1_mul_h_4_mul_x_109_12

/-- Explicit object and grading transports between classical and synthetic
sphere Adams data. -/
structure SphereAdamsCoherence
    {C : StableHomotopyContext} (S : SyntheticHomotopyContext C)
    {A : ClassicalAdamsSS C C.sphere} (B : SyntheticAdamsSS) where
  classicalSphere : C.sphere = C.sphere
  syntheticSphere : S.sphere = S.sphere
  unitName : String
  h5Degree : KIP126.Classical.Adams.Bidegree
  h5Degree_eq : h5Degree = (1, 32)
  regrading : ∀ b : KIP126.Classical.Adams.Bidegree,
    nuDegree b = (b.1, b.2, b.2)

end KIP126.Kervaire
