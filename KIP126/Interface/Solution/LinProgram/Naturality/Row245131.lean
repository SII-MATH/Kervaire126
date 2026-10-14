module

public import KIP126.Interface.Challenge.Computation.Delivery
public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Proofs
public import KIP126.Def.ClassicalAdams.Suspension.Internal.Proofs
public import KIP126.Def.ClassicalAdams.Suspension.Construction.Comparison.Data
public import KIP126.LinProgram.Raw.Naturality
public import KIP126.Interface.Solution.LinProgram.Naturality.Row245131Coordinates

@[expose] public section


/-!
# Interface/Solution/LinProgram/Naturality/Row245131

Fixed-model Interface construction or conditional theorem. A supplied presentation is not constructed by its use.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-!
# Conditional replay of native naturality log 245131

The actual top-cell map of the fixed η cofiber lands in ΣS¹. The native
map `Ceta__S0` has suspension shift two; it is not a degree-preserving
map from this cofiber to S⁰. The first theorem below proves naturality
to ΣS¹ using the constructed tower map.

The final native statement is conditional on the source differential,
and its actual coordinate comparisons through both fixed tower suspensions.
Compatibility of the two desuspensions with differentials is proved from
the actual tower squares: the two single-desuspension signs cancel. No
computation delivery, table soundness theorem or consumer witness is read here.
-/

namespace KIP126.Interface.Solution.LinProgram.Naturality

open CategoryTheory KIP126.StableHomotopy KIP126.Classical.Adams
open KIP126.Core.SpectralSequence KIP126.LinE2

noncomputable section

/-- The internal source object is built from the same route's η map. -/
abbrev Ceta : standardFoundation.Spectrum :=
  HasFunctorialCofiber.cofib standardRouteModel.auxiliary.etaMap

abbrev cetaSequence :=
  adamsTowerInternalSpectralSequence standardFoundation.hf2.unit Ceta

/-- Construct the auxiliary object's comparison from the same fixed foundation.
This does not replace the existing sphere comparisons or identify native labels. -/
def cetaTowerComparison : Suspension.TowerComparison standardFoundation.hf2 Ceta := by
  letI : Foundation.TensorInput standardFoundation := Def.StageInput.witness.tensorInput
  exact Suspension.Construction.towerComparison standardFoundation.hf2 Ceta

/-- The same construction applies at every integer shift of this Cη.
In particular it supplies the three shifted comparisons needed by shift four. -/
def cetaShiftTowerComparison (n : ℤ) :
    Suspension.TowerComparison standardFoundation.hf2 (Ceta⟦n⟧) := by
  letI : Foundation.TensorInput standardFoundation := Def.StageInput.witness.tensorInput
  exact Suspension.Construction.towerComparison standardFoundation.hf2 (Ceta⟦n⟧)

/-- The actual cofiber connecting map; its target retains both suspensions. -/
def topCell : Ceta ⟶ (Sphere (C := standardFoundation.Spectrum) 1)⟦(1 : ℤ)⟧ :=
  HasFunctorialCofiber.cofibδ standardRouteModel.auxiliary.etaMap

/-- An explicit interpretation of the auxiliary Cη basis labels. Its
agreement with the pinned Cη data is still an instance obligation; this
parameter neither chooses a second route model nor asserts a basis theorem. -/
abbrev CetaCoordinates :=
  (s t : Nat) → Nat → cetaSequence.Page 2 ((s : ℤ), (t : ℤ))

/-- Exact source-candidate equation from log 245130, with both native [0]
coordinates on the actual η-cofiber sequence. It is a premise, not a
consequence of its D tag or its position before log 245131. -/
def SourceEquation (coordinates : CetaCoordinates) : Prop :=
  HasDifferential cetaSequence 3 (2, 19) (5, 21)
    (coordinates 2 19 0) (coordinates 5 21 0)

/-- The actual naturality step closes before any suspension comparison.
The source and target internal degrees are still 19 and 21. -/
theorem row245130_topCell (coordinates : CetaCoordinates)
    (source : SourceEquation coordinates) :
    HasDifferential
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit
        ((Sphere (C := standardFoundation.Spectrum) 1)⟦(1 : ℤ)⟧))
      3 (2, 19) (5, 21)
      (adamsInternalE2Induced standardFoundation.hf2.unit topCell (2, 19)
        (coordinates 2 19 0))
      (adamsInternalE2Induced standardFoundation.hf2.unit topCell (5, 21)
        (coordinates 5 21 0)) :=
  adamsInternalE2Induced_hasDifferential standardFoundation.hf2.unit topCell source

/-- The universal suspension proposition on the same two
fixed tower comparisons. It ranges over all pages, bidegrees and labels.
Two successive desuspensions account for `sus = 2`; no single-desuspension
same-sign differential rule is assumed (the tower connecting squares carry
the suspension sign). The theorem below proves this property. -/
def DoubleDesuspensionCompatible : Prop :=
  ∀ (r s t u v : ℤ)
    (sx : PageRepresentatives.Ambient standardFoundation.hf2
      ((Sphere (C := standardFoundation.Spectrum) 1)⟦(1 : ℤ)⟧) (s, t))
    (sy : PageRepresentatives.Ambient standardFoundation.hf2
      ((Sphere (C := standardFoundation.Spectrum) 1)⟦(1 : ℤ)⟧) (u, v))
    (x1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (s, t - 1))
    (y1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (u, v - 1))
    (x : sphereAdamsData.Page 2 (s, t - 1 - 1))
    (y : sphereAdamsData.Page 2 (u, v - 1 - 1)),
    (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
      s t sx x1 →
    (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
      u v sy y1 →
    (standardRouteModel.classicalSuspension .sphere).DesuspendsClass
      s (t - 1) x1 x →
    (standardRouteModel.classicalSuspension .sphere).DesuspendsClass
      u (v - 1) y1 y →
    HasDifferential
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit
        ((Sphere (C := standardFoundation.Spectrum) 1)⟦(1 : ℤ)⟧))
      r (s, t) (u, v) sx sy →
    HasDifferential sphereAdamsData r (s, t - 1 - 1) (u, v - 1 - 1) x y

/-- The fixed comparisons satisfy the full universal statement by the generic
actual two-desuspension theorem. Its fixed-model foundational dependencies
are inherited; no extra compatibility premise is introduced. -/
theorem doubleDesuspensionCompatible : DoubleDesuspensionCompatible := by
  intro r s t u v sx sy x1 y1 x y hsx hsy hx hy h
  exact (standardRouteModel.classicalSuspension .sphere).hasDifferential_desuspendTwice
    (standardRouteModel.classicalSuspension (.shift 1 .sphere)) hsx hsy hx hy h

/-- Naturality along the fixed top-cell map followed by the actual two
fixed desuspensions. This reusable statement retains every integer page,
bidegree and representative; only the source differential and the four
representative comparisons are inputs. -/
theorem topCell_hasDifferential_desuspendTwice (r s t u v : ℤ)
    (a : cetaSequence.Page 2 (s, t)) (b : cetaSequence.Page 2 (u, v))
    (x1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (s, t - 1))
    (y1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (u, v - 1))
    (x : sphereAdamsData.Page 2 (s, t - 1 - 1))
    (y : sphereAdamsData.Page 2 (u, v - 1 - 1))
    (source_first :
      (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
        s t (adamsInternalE2Induced standardFoundation.hf2.unit topCell (s, t) a) x1)
    (target_first :
      (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
        u v (adamsInternalE2Induced standardFoundation.hf2.unit topCell (u, v) b) y1)
    (source_second :
      (standardRouteModel.classicalSuspension .sphere).DesuspendsClass s (t - 1) x1 x)
    (target_second :
      (standardRouteModel.classicalSuspension .sphere).DesuspendsClass u (v - 1) y1 y)
    (source : HasDifferential cetaSequence r (s, t) (u, v) a b) :
    HasDifferential sphereAdamsData r (s, t - 1 - 1) (u, v - 1 - 1) x y :=
  doubleDesuspensionCompatible r s t u v
    (adamsInternalE2Induced standardFoundation.hf2.unit topCell (s, t) a)
    (adamsInternalE2Induced standardFoundation.hf2.unit topCell (u, v) b)
    x1 y1 x y source_first target_first source_second target_second
    (adamsInternalE2Induced_hasDifferential standardFoundation.hf2.unit topCell source)

/-- Package native coordinate witnesses and an actual differential using
the same presentation on both endpoints. -/
theorem statement_of_hasDifferential (P : LinE2Presentation)
    (row : KIP126.Computation.LinProofs.DifferentialRow)
    (hx : row.t ≤ 261) (hy : row.t + row.r - 1 ≤ 261)
    (x : E2At row.s row.t)
    (y : E2At (row.s + row.r) (row.t + row.r - 1))
    (x_coordinates : KIP126.Challenge2.HasCoordinates x row.x)
    (y_coordinates : KIP126.Challenge2.HasCoordinates y row.dx)
    (h : HasDifferential sphereAdamsData row.r
      ((row.s : ℤ), (row.t : ℤ))
      (((row.s + row.r : Nat) : ℤ), ((row.t + row.r - 1 : Nat) : ℤ))
      (P.comparison row.s row.t hx x)
      (P.comparison (row.s + row.r) (row.t + row.r - 1) hy y)) :
    KIP126.Challenge2.DifferentialStatement P row :=
  ⟨hx, hy, x, y, x_coordinates, y_coordinates, h⟩

/-- The full native output, with explicit remaining source and map-coordinate
premises. The universal suspension law is proved above. The statement does not strengthen [0]
to a nonzero later-page class or translate it to a paper name. -/
theorem row245131 (P : LinE2Presentation) (coordinates : CetaCoordinates)
    (source : SourceEquation coordinates)
    (x : E2At 2 17) (y : E2At 5 19)
    (x_coordinates : KIP126.Challenge2.HasCoordinates x [0])
    (y_coordinates : KIP126.Challenge2.HasCoordinates y [0])
    (x1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (2, 18))
    (y1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (5, 20))
    (source_first :
      (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
        2 19
        (adamsInternalE2Induced standardFoundation.hf2.unit topCell (2, 19)
          (coordinates 2 19 0)) x1)
    (target_first :
      (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
        5 21
        (adamsInternalE2Induced standardFoundation.hf2.unit topCell (5, 21)
          (coordinates 5 21 0)) y1)
    (source_second :
      (standardRouteModel.classicalSuspension .sphere).DesuspendsClass
        2 18 x1 (P.comparison 2 17 (by decide) x))
    (target_second :
      (standardRouteModel.classicalSuspension .sphere).DesuspendsClass
        5 20 y1 (P.comparison 5 19 (by decide) y)) :
    KIP126.Challenge2.DifferentialStatement P
      KIP126.Computation.LinProofs.Raw.Naturality.output245131 := by
  have h : HasDifferential sphereAdamsData 3 (2, 17) (5, 19)
      (P.comparison 2 17 (by decide) x) (P.comparison 5 19 (by decide) y) :=
    topCell_hasDifferential_desuspendTwice 3 2 19 5 21
      (coordinates 2 19 0) (coordinates 5 21 0) x1 y1
      (P.comparison 2 17 (by decide) x) (P.comparison 5 19 (by decide) y)
      source_first target_first source_second target_second source
  exact statement_of_hasDifferential P
    KIP126.Computation.LinProofs.Raw.Naturality.output245131
    (by decide) (by decide) x y x_coordinates y_coordinates h

/-- Native endpoint using the two fixed archived sphere coordinates. Their
coordinate witnesses are proved; the actual source differential and the four
actual map comparisons remain explicit. -/
theorem row245131_native (P : LinE2Presentation) (coordinates : CetaCoordinates)
    (source : SourceEquation coordinates)
    (x1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (2, 18))
    (y1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (5, 20))
    (source_first :
      (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
        2 19
        (adamsInternalE2Induced standardFoundation.hf2.unit topCell (2, 19)
          (coordinates 2 19 0)) x1)
    (target_first :
      (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
        5 21
        (adamsInternalE2Induced standardFoundation.hf2.unit topCell (5, 21)
          (coordinates 5 21 0)) y1)
    (source_second :
      (standardRouteModel.classicalSuspension .sphere).DesuspendsClass
        2 18 x1 (P.comparison 2 17 (by decide) KIP126.LinE2.NaturalityCoordinates.source))
    (target_second :
      (standardRouteModel.classicalSuspension .sphere).DesuspendsClass
        5 20 y1 (P.comparison 5 19 (by decide) KIP126.LinE2.NaturalityCoordinates.target)) :
    KIP126.Challenge2.DifferentialStatement P
      KIP126.Computation.LinProofs.Raw.Naturality.output245131 := by
  exact row245131 P coordinates source
    KIP126.LinE2.NaturalityCoordinates.source KIP126.LinE2.NaturalityCoordinates.target
    NaturalityCoordinates.source_hasCoordinates NaturalityCoordinates.target_hasCoordinates
    x1 y1 source_first target_first source_second target_second

end
end KIP126.Interface.Solution.LinProgram.Naturality
