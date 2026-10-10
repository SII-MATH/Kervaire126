import KIP126.Interface.Challenge.Challenge2
import KIP126.Interface.Solution.Literature.Applications

namespace KIP126.Interface.Solution.Literature.Route
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.Kervaire.Route
open KIP126.Literature.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

/-- Pure equality transport from the same classical source convergence.
This adapter adds neither a source theorem nor a synthetic-source premise. -/
theorem mossInputOfClassicalSource (η : BiHom 1 2 (S_0_0 : Syn))
    (S : ClassicalSourceData H) (B : ClassicalSourceBinding D η S)
    (h : MossSourceInput M S.convergence) : MossInput D := by
  change MossSourceInput M (D.classicalConvergence .sphere)
  rw [B.convergence]
  exact h

end KIP126.Interface.Solution.Literature.Route
