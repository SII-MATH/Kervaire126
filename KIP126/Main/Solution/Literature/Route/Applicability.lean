import KIP126.Interface.Challenge.Challenge2
import KIP126.Interface.Solution.Literature.Applications

namespace KIP126.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : Model H M Syn)

/-- The compatibility premise is applicable: its exponent equation is
proved from the three source-bound exponents, not left as a vacuous ∀. -/
theorem NuCofiberApplicability.exponent_sum (P : NuCofiberApplicability D) :
    (normalizedExponent H D.auxiliary.nuRouteTriangle.f : ℤ) +
      normalizedExponent H D.auxiliary.nuRouteTriangle.g +
      normalizedExponent H D.auxiliary.nuRouteTriangle.h = 1 := by
  change (normalizedExponent H D.auxiliary.nuMap : ℤ) + _ + _ = 1
  rw [P.nu_exponent, P.bottom_exponent, P.top_exponent]
  norm_num

end
end KIP126.Literature.Route
