import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Canonical.Data
import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.Route.Data
import KIP126.Def.Comparison.ClassicalSynthetic.FirstQuotient.Detection.Proofs

/-! The first-quotient comparison, pinned to realization and actual tower
arrows. Realization of nu X/lambda itself is zero, so applying realization
directly to its homotopy class CANNOT define its classical E2 label.
Instead the label uses the actual quotient projection on Adams pages,
the actual realization map on the unquotiented tower, and the J/cofiber
image of a lift in the quotient tower. Equality remains in E-infinity;
there is no unwarranted equality between independently chosen E2 lifts.
-/
namespace KIP126.Comparison.ClassicalSynthetic.RealizationTower
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section

section ActualRepresentatives
variable {S : Type u} [StableHomotopyCategory.{u,v} S]
  [HasFunctorialCofiber (C := S)] {HS : S}
  (unit : SphereSpectrum ⟶ HS) (Y : S) (p : ℤ × ℤ)

/-- Project the SAME actual common representative to the initial E2. -/
def infiniteE2 (z : TowerDetection.InfiniteRepresentative unit Y p) :
    (adamsTowerInternalSpectralSequence unit Y).Page 2 p :=
  let E := (adamsTowerInternalSpectralSequence unit Y).ssData p
  (Subobject.ofLE (E.Z ⊤) (E.Z 0) (E.Z_anti le_top) ≫ E.pageπ 0) z

def infiniteClass (z : TowerDetection.InfiniteRepresentative unit Y p) :
    ((adamsTowerInternalSpectralSequence unit Y).ssData p).eInfty :=
  ((adamsTowerInternalSpectralSequence unit Y).ssData p).pageπ ⊤ z
end ActualRepresentatives

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

def firstQuotientObject (X : ClassicalObject) (a : ℤ) : Syn :=
  XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
    (D.nu.functor.obj (X.obj D.auxiliary))) 1

def firstQuotientWeighted (X : ClassicalObject) (a w : ℤ) : Syn :=
  (SyntheticCategory.biShift (0,-w)).obj (firstQuotientObject D X a)

def firstQuotientWeightInclusion (X : ClassicalObject) (a w : ℤ) :
    nuWeightObject D X a w ⟶ firstQuotientWeighted D X a w :=
  (SyntheticCategory.biShift (0,-w)).map (XModLambdaN.incl _ 1)

variable [D.recovery.realization.Monoidal] [D.recovery.realization.Additive]
local instance fqRealizationShift : D.recovery.realization.CommShift ℤ := D.realizationShift
variable (bases : WeightBases D) (B : NuE2Binding D bases)

/-- All objects and maps in this relation are actual: realization of
unquotiented representatives, inclusion of the FIRST lambda cofiber,
cofiber J in its Adams tower, and projection to stage zero. The two common
representatives need only agree modulo all incoming boundaries, retaining
the correct associated-graded meaning. No convergence iso or firstQuotient
equivalence is used to DEFINE this source-label relation. -/
def ActualFirstQuotientLabel (X : ClassicalObject) (a s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t)
    (α : BiHom (t-s) (t+a) (firstQuotientObject D X a)) : Prop :=
  let U := nuCoefficientUnit H.unit D.nu
  let Y := firstQuotientWeighted D X a (t+a)
  ∃ z : (weightTower U
      ((SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.auxiliary)))
      (t+a)).Page 2 (s,t),
    internalE2Map (B.tower X a (t+a)) (s,t) z = x ∧
    ∃ (r : TowerDetection.InfiniteRepresentative U Y (s,t))
      (b : HomotopyGroup (t-s) (adamsTowerAt U Y s))
      (j : TowerDetection.InfiniteRepresentative U Y (s,t)),
      infiniteE2 U Y (s,t) r =
        adamsInternalE2Induced U (firstQuotientWeightInclusion D X a (t+a)) (s,t) z ∧
      TowerDetection.infiniteRepresentativeE1 U Y (s,t) j = adamsJ U Y s t b ∧
      infiniteClass U Y (s,t) r = infiniteClass U Y (s,t) j ∧
      inducedMap (adamsTowerMap U Y 0 s.toNat (Nat.zero_le _)) (t-s) b =
        weightHomotopyMap (t-s) (t+a) (firstQuotientObject D X a) α

/-- The selected firstQuotient equivalence must label every inverse image
by the actual relation above. This is a model comparison obligation, never
an additional accepted external fact for arbitrary choices of D. -/
def FirstQuotientBinding : Prop :=
  ∀ (X : ClassicalObject) (a s t : ℤ) (x : E2 H (X.obj D.auxiliary) s t),
    ActualFirstQuotientLabel D bases B X a s t x
      ((D.firstQuotient (X.obj D.auxiliary) a s t).symm x)


end
end KIP126.Comparison.ClassicalSynthetic.RealizationTower
