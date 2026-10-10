import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Canonical.Predicates
import KIP126.Def.Kervaire.Route.Model.Predicates

namespace KIP126.Kervaire.Route
open KIP126.Classical.Adams
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H) (Syn : Type w)
  [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]

/-- Coherent shared route data. This construction is deliberately
parameterized: no global witness, literature theorem, or computation result
is produced by declaring the structure. -/
structure Model extends ModelData H Syn where
  towerPresentation : TowerPresentation (nuCoefficientUnit H.unit nu) family
  /-- Detection uses the actual tower lift/cofiber comparison for this
  ONE presentation. An arbitrary E-infinity/associated-graded isomorphism
  does not identify the detected homotopy class. -/
  convergence_canonical : ∀ X,
    TowerConvergence.Canonical (nuCoefficientUnit H.unit nu) (convergence X) towerPresentation
  comparisonCompatible : ComparisonCompatible toModelData
  homotopySeparated : HomotopySeparated toModelData
  sphereProductCommutative : SphereProductCommutative (Syn := Syn)
  multiplicationCompatible : MultiplicationCompatible toModelData M
end KIP126.Kervaire.Route
