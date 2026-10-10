import KIP126.LinProgram.Interpretation.Route.Data
import KIP126.LinProgram.Model.BasisTable.Data
import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Data
import KIP126.Def.SpectralSequence.Computation.State.Predicates

namespace KIP126.Computation.Route
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Core.SpectralSequence KIP126.Synthetic.Context KIP126.Kervaire.Route
open KIP126.LinE2
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- Mathematical interpretation, including successful coordinate decoding.
Nonzero on E₂ is never substituted for nonzero on a later page. -/
def Statement {D : Model H M Syn} (R : Realization D) (c : Raw.Claim) : Prop :=
  ∃ x, R.decode c.spectrum c.s c.t c.x = some x ∧
    match c.kind with
    | .reaches => ReachesPage (sequence D c.spectrum) c.r (c.s,c.t) x
    | .boundaryBy => IsBoundaryBy (sequence D c.spectrum) c.r (c.s,c.t) x
    | .equation => ∃ y, R.decode c.spectrum c.ts c.tt c.y = some y ∧
        HasDifferential (sequence D c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y
    | .refutation => ∃ y, R.decode c.spectrum c.ts c.tt c.y = some y ∧
        ¬ HasDifferential (sequence D c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y

/-- Different provenance records can impose the same mathematical obligation.
Keep their origin and record identifiers for traceability; they do not change
the decoded claim or supply a proof of it. -/
theorem statement_with_provenance {D : Model H M Syn} (R : Realization D)
    (c : Raw.Claim) (origin : String) (record : Nat) :
    Statement R { c with origin := origin, record := record } ↔ Statement R c :=
  Iff.rfl

/-- Explicit additive bases, including empty degrees and ALL linear combinations.
An integer-linear equivalence to F₂ coordinates uses the actual additive group;
it neither chooses a second group law nor postulates a new scalar action. -/
def BasisCorrect {D : Model H M Syn} (R : Realization D) (d : Raw.Degree) : Prop :=
  ∃ e : Page D d.spectrum d.s d.t ≃ₗ[ℤ]
      (Fin d.monomials.length →₀ KIP126.Core.Algebra.F2),
    ∀ i, e.symm (Finsupp.single i 1) = R.basis d.spectrum d.s d.t i.val

/-- Each selected sphere basis value is the specified CSV monomial, interpreted
through the same comparison used for named elements and products. Homogeneity
is a required witness; no invalid monomial is silently mapped to zero. -/
def SphereBasisValue {D : Model H M Syn} (R : Realization D)
    (d : Raw.Degree) : Prop :=
  d.spectrum = .sphere → ∀ i : Fin d.monomials.length,
    ∃ z : E2At d.s d.t,
      z.val = projection (monomialOfString d.monomials[i]) ∧
      R.sphere d.s d.t z = R.basis .sphere d.s d.t i.val

/-- Only the selected product degrees, using the relation quotient, not a stored
multiplication table. Both operations are fixed before this condition is stated. -/
def ProductCorrect {D : Model H M Syn} (R : Realization D) (p : Raw.Product) : Prop :=
  ∀ (x : E2At p.s p.t) (y : E2At p.sp p.tp),
    R.sphere (p.s+p.sp) (p.t+p.tp) (mulAt x y) =
      Sphere.Internal.product H M (R.sphere p.s p.t x) (R.sphere p.sp p.tp y)

/-- Bottom-cell labels are images under the actual inclusion of the same cofiber. -/
def BottomCorrect {D : Model H M Syn} (R : Realization D) (p : Raw.BottomMap) : Prop :=
  ∃ x y, R.decode .sphere p.s p.t p.x = some x ∧
    R.decode .nuCofiber p.s p.t p.y = some y ∧
    adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibι D.auxiliary.nuMap)
      (p.s,p.t) x = y

/-- The top-cell value is compared via D's actual tower suspension data, not
an arbitrary degree-shifted linear map. Two canonical shift-addition maps
and four one-fold desuspensions identify Σ(S³) with S⁰ in degree t-4. -/
def TopCorrect {D : Model H M Syn} (R : Realization D) : Prop :=
  ∃ (x : Page D .nuCofiber 8 134) (y : Page D .sphere 8 130)
    (a3 : E2 H (Sphere 3) 8 133)
    (a2 : E2 H (Sphere 2) 8 132)
    (a1 : E2 H (Sphere 1) 8 131),
    R.decode .nuCofiber 8 134 [0] = some x ∧
    R.decode .sphere 8 130 [0] = some y ∧
    (D.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 8 134
      (adamsInternalE2Induced H.unit (HasFunctorialCofiber.cofibδ D.auxiliary.nuMap)
        (8,134) x) a3 ∧
    (D.classicalSuspension (.shift 2 .sphere)).DesuspendsClass 8 133
      (adamsInternalE2Induced H.unit
        ((shiftFunctorAdd' C (2 : ℤ) 1 3 (by decide)).hom.app SphereSpectrum)
        (8,133) a3) a2 ∧
    (D.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 8 132
      (adamsInternalE2Induced H.unit
        ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by decide)).hom.app SphereSpectrum)
        (8,132) a2) a1 ∧
    (D.classicalSuspension .sphere).DesuspendsClass 8 131 a1 y

end
end KIP126.Computation.Route
