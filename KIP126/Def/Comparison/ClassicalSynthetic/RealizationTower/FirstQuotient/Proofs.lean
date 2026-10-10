import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.FirstQuotient.Predicates

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

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

variable [D.recovery.realization.Monoidal] [D.recovery.realization.Additive]
local instance fqProofRealizationShift : D.recovery.realization.CommShift ℤ := D.realizationShift
variable (bases : WeightBases D) (B : NuE2Binding D bases)

/-- The route's nu_first_quotient condition gives a family representative.
Naturality of the SAME tower presentation transports the actual quotient
map; canonical convergence transports the actual tower lift and J image.
NuE2Binding fixes its classical label through realization. -/
theorem firstQuotientBinding_of_nuE2 : FirstQuotientBinding D bases B := by sorry

/-- The remaining higher-filtration ambiguity is eliminated exactly by
the BHS p=1 single-filtration range, not by strengthening detection to an
unconditional equality of arbitrary representatives. -/
theorem actualFirstQuotientLabel_unique (X : ClassicalObject) (a s t : ℤ)
    (hzero : FirstQuotientNextFiltrationZero D X a s t)
    (x : E2 H (X.obj D.auxiliary) s t)
    (α β : BiHom (t-s) (t+a) (firstQuotientObject D X a))
    (hα : ActualFirstQuotientLabel D bases B X a s t x α)
    (hβ : ActualFirstQuotientLabel D bases B X a s t x β) : α = β := by sorry

end
end KIP126.Comparison.ClassicalSynthetic.RealizationTower
