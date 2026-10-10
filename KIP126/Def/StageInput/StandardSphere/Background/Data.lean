import KIP126.Def.ClassicalAdams.Moss.Context.Data
import KIP126.Def.ClassicalAdams.Tmf.Model.Binding.Data
import KIP126.Def.StageInput.StandardSphere.Sequence.Data
import KIP126.Def.Kervaire.Route.SourceLanguage

/-! The fixed sphere's mathematical comparison context, before any external
Moss theorem or program-coordinate result is supplied. -/

namespace KIP126.Kervaire.Route

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : KIP126.Classical.Adams.MilnorCooperations H}

/-- Structural mathematics on the same route: actual realization, tensor
algebras, boundary conventions and tower comparisons. No source theorem,
source-object binding, CSV coordinate interpretation or Main consequence
is included. Completing the fixed construction must establish these
internal properties on the explicitly selected synthetic background. -/
structure Background (D : Model H M Syn) where
  realization : KIP126.Literature.Route.RealizationCoordinates D
  algebra : KIP126.Literature.Route.AlgebraData D
  quotientBinding : KIP126.Literature.Route.QuotientAlgebraBinding D algebra
  algebraBinding : KIP126.Literature.Route.AlgebraBinding D algebra
  may : KIP126.Literature.Route.MayContext Syn
  realizationAdditive : D.recovery.realization.Additive
  weights : KIP126.Comparison.ClassicalSynthetic.RealizationWeightComparison D.nu D.recovery
  nuE2 :
    letI := algebra.classicalSymmetric
    letI := algebra.syntheticSymmetric
    letI := algebra.realizationMonoidal.realization
    letI := realizationAdditive
    KIP126.Comparison.ClassicalSynthetic.RealizationTower.NuE2Binding D
      (fun X a w => KIP126.Comparison.ClassicalSynthetic.RealizationWeightComparison.doubleShift
        D.nu D.recovery weights (X.obj D.auxiliary) a (-w))

end KIP126.Kervaire.Route

namespace KIP126.Challenge2

/-- The actual sphere mapping pairing, convergence and detection context.
This type contains the internal compatibility conditions required to apply
Moss; it does not contain Moss's external conclusion. -/
def StandardSphereMossContext : Type 1 :=
  let c := KIP126.Def.StageInput.witness
  letI : KIP126.Foundation.TensorInput c.foundationInput := c.tensorInput
  KIP126.Challenge2.MossContext c.foundationInput.hf2 c.cooperationInput.ring
    (fun _ : Unit => KIP126.StableHomotopy.SphereSpectrum
      (C := c.foundationInput.Spectrum))

end KIP126.Challenge2
