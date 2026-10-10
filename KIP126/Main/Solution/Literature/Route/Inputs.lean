import KIP126.Main.Solution.Literature.Route.Applicability
import KIP126.Interface.Challenge.Challenge2
import KIP126.Interface.Solution.Literature.Applications

namespace KIP126.Literature.Route
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn) (η : BiHom 1 2 (S_0_0 : Syn)) (L : TmfLabels H)

/-- Supply the already frozen forward differential language from the
external BHS rigidity input. This is only projection, not a proof of BHS. -/
theorem Inputs.differentialLift (I : Inputs D η L) :
    KIP126.Literature.Route.DifferentialLiftInput D := by
  intro X a s t r k hr x y h
  exact (I.synthetic.differentials X a s t r k hr x y).mp h

/-- The actual Cν triangle required by the Mahowald tool is available
without assuming the tool's conclusion or a computed ν-extension. -/
theorem Inputs.nuTriangle (I : Inputs D η L) :
    NormalizedTriangleCompatible D.toModelData D.auxiliary.nuRouteTriangle
      (I.applicability.nuCofiber.exponent_sum D) :=
  I.applicability.nuCofiber.triangle _
end KIP126.Literature.Route
