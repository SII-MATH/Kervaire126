import KIP126.Def.Kervaire.Route.Model.Coherent.Data

/-! Detection determines a homotopy representative only when the next
actual Adams filtration vanishes. For the first lambda quotient, BHS
`cor:synth-ctau-ASS` at p=1 supplies the single-filtration range; applying
that range and separated convergence is a separate internal obligation.
Neither the range nor BHS's theorem is silently added to Model.
-/
namespace KIP126.Comparison.ClassicalSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {HS : Syn} {unit : S_0_0 ⟶ HS} {family : SyntheticAdamsFamily Syn} {Y : Syn}

variable {C : Type w} [StableHomotopyCategory.{w, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

/-- The precise range obligation needed to remove first-quotient
indeterminacy, at stem t-s and weight t+a. The object is the actual
quotient of the same shifted nu object, and the next filtration is s+1. -/
def FirstQuotientNextFiltrationZero (X : ClassicalObject) (a s t : ℤ) : Prop :=
  towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
    ((SyntheticObject.quotient 1 (.shift (0,a) (.nu X))).obj D.nu D.auxiliary)
    (s+1) (t-s,t+a) = ⊥

/-- BHS `cor:synth-ctau-ASS` at p=1, expressed only as its single-filtration
range after an actual weight shift. At stem m and weight w, the only
possible filtration is w-a-m. It does not select an E-infinity isomorphism.
The source theorem and its transport must supply this proposition. -/
def FirstQuotientSingleFiltration (X : ClassicalObject) (a : ℤ) : Prop :=
  ∀ (m w j : ℤ), j ≠ w-a-m →
    Subsingleton (((D.family.obj
      ((SyntheticObject.quotient 1 (.shift (0,a) (.nu X))).obj D.nu D.auxiliary)).sequence.ssData
        (j,m+j,w)).eInfty)


end
end KIP126.Comparison.ClassicalSynthetic
