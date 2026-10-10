import KIP126.Main.Solution.Tools.GeneralizedLeibniz
import KIP126.Main.Solution.Tools.GeneralizedMahowald
import KIP126.Main.Solution.Tools.PageExtensionStretching

/-!
# Independently proved paper rules available to computation certification

The original derivation of log 2411720 uses Generalized Leibniz; its equation
is retained as sphere staircase records 2791/3011. A replay following that
path must prove the rule's explicit cycle, extension and no-crossing premises.
These adapters supply only the general rules, not any recorded differential.
Their Main producers take no computation input, selected stage witness, tmf
high-class result, or final theorem. The producers currently contain `sorry`.

Direct proofs of the same fixed `Statement` remain possible. No choice of replay
algorithm, no manual image-J seed and no statement merely present in a log is
installed as an extra external assumption by this module.
-/
namespace KIP126.Interface.Solution.LinProgram.Rules

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Kervaire.Route KIP126.Classical.Adams
open KIP126.Literature.Route

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

/-- Independent general rule; a replay must still prove every instance premise. -/
theorem generalizedLeibniz (synthetic : SyntheticInputs D)
    (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) :
    KIP126.Kervaire.Route.Tools.GeneralizedLeibnizLaw D X Y f :=
  KIP126.Main.Solution.Tools.generalizedLeibniz D synthetic X Y f

/-- The normalized triangle and its crossing conditions are not dropped. -/
theorem generalizedMahowald (synthetic : SyntheticInputs D) (may : MayInput Syn)
    (T : TriangleData D.auxiliary) :
    KIP126.Kervaire.Route.Tools.GeneralizedMahowaldLaw D T :=
  KIP126.Main.Solution.Tools.generalizedMahowald D synthetic may T

/-- This finite rule supplies no infinite or coherent lift. -/
theorem finitePageExtensionStretching (synthetic : SyntheticInputs D)
    (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) :
    KIP126.Kervaire.Route.Tools.FinitePageExtensionStretchingLaw D X Y f :=
  KIP126.Main.Solution.Tools.finitePageExtensionStretching D synthetic X Y f

end KIP126.Interface.Solution.LinProgram.Rules
