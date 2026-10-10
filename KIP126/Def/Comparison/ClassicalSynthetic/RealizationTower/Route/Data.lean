import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.Pages.Data
import KIP126.Def.Kervaire.Route.Model.Coherent.Data

/-! Same-model binding of the route's nu E2 labels to actual realization.
The weight-base isomorphisms are explicit parameters: the source model
must provide them by its lambda-inversion weight comparison and recovery,
not by independent isomorphisms chosen for named elements. -/
namespace KIP126.Comparison.ClassicalSynthetic.RealizationTower
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

def nuWeightObject (X : ClassicalObject) (a w : ℤ) : Syn :=
  (SyntheticCategory.biShift (0,-w)).obj
    ((SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.auxiliary)))

/-- These maps identify the actual weight-desuspended objects, not merely
their isomorphism classes. The standard source constructs the collection
using its zero-weight recovery map and the actual realized lambda maps. -/
abbrev WeightBases := ∀ (X : ClassicalObject) (a w : ℤ),
  D.recovery.realization.obj (nuWeightObject D X a w) ≅ X.obj D.auxiliary

variable [D.recovery.realization.Monoidal] [D.recovery.realization.Additive]
local instance realizationShift : D.recovery.realization.CommShift ℤ := D.realizationShift

/-- The coefficient iso is the SAME recovery component at HF2. -/
def coefficientIso :
    D.recovery.realization.obj (D.nu.functor.obj H.HF2) ≅ H.HF2 :=
  D.recovery.nuRealizationIso.app H.HF2

/-- Structural comparison obligation tying the named labels to the
canonical direction of tau inversion. The chosen tower presentation of D
is used literally. The E2 map is constructed from F.map on representatives
and the exact monoidal layer formula in `RealizationTower.Data`.

This record does NOT contain BHS differential rigidity, an E-infinity
formula, a permanence conclusion, or any selected local computation. -/
structure NuE2Binding (bases : WeightBases D) where
  tower : ∀ (X : ClassicalObject) (a w : ℤ),
    Comparison D.recovery.realization (nuCoefficientUnit H.unit D.nu) H.unit
      (coefficientIso D) (nuWeightObject D X a w) (X.obj D.auxiliary) (bases X a w)
  label : ∀ (X : ClassicalObject) (a s t : ℤ) (k : ℕ)
      (x : E2 H (X.obj D.auxiliary) s t),
    internalE2Map (tower X a (t+a-k)) (s,t)
      ((D.towerPresentation.forward
        ((SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.auxiliary)))
        (t+a-k)).pageMap (s,t) 0 (D.nuE2 X a s t k x)) = x

end
end KIP126.Comparison.ClassicalSynthetic.RealizationTower
