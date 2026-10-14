module

public import KIP126.Interface.Solution.LinProgram.EtaNu
public import KIP126.Interface.Solution.LinProgram.Naturality.CWModel
public import KIP126.Interface.Solution.LinProgram.Naturality.Row462481
public import KIP126.Def.ClassicalAdams.Suspension.Fourfold.Proofs

@[expose] public section


/-!
# Interface/Solution/LinProgram/Naturality/CWToCeta

Fixed-model Interface construction or conditional theorem. A supplied presentation is not constructed by its use.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Conditional replay of the fixed CW→Cη→sphere chain. The same selected
extension and cofiber are used throughout. The zero composite, actual CW
source differential and native coordinate comparisons remain explicit.
Neither a native D tag nor the conditional object construction supplies them. -/
namespace KIP126.Interface.Solution.LinProgram.NaturalityCW

open CategoryTheory KIP126.StableHomotopy KIP126.Classical.Adams
open KIP126.Core.SpectralSequence KIP126.LinE2
open Naturality Suspension.Fourfold
noncomputable section

local notation "Sp" => standardFoundation.Spectrum
local notation "η" => standardRouteModel.auxiliary.etaMap
local notation "ν" => standardRouteModel.auxiliary.nuMap

/-- Reassociate the target of the same actual q into four successive shifts. -/
def toQuadCeta (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0) :
    CW hzero ⟶ quadShift Ceta :=
  q hzero ≫ (quadShiftIso Ceta).inv

/-- Four actual quotient maps, using the same foundation and the existing
Cη and ΣCη comparisons. No native labels or pagewise equivalence are inputs. -/
def cetaDesuspendFour (r : ℤ) (p : ℤ × ℤ) :
    (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit (quadShift Ceta)).Page r p ⟶
      cetaSequence.Page r (p.1, p.2 - 1 - 1 - 1 - 1) := by
  letI : Foundation.TensorInput standardFoundation := Def.StageInput.witness.tensorInput
  exact desuspendFourInternalPage cetaTowerComparison (cetaShiftTowerComparison 1)
    (Suspension.Construction.towerComparison standardFoundation.hf2 ((Ceta⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧))
    (Suspension.Construction.towerComparison standardFoundation.hf2
      (((Ceta⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)) r p

set_option maxRecDepth 4096 in
theorem cetaDesuspendFour_hasDifferential {r : ℤ} {p q : ℤ × ℤ}
    {x : (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit (quadShift Ceta)).Page 2 p}
    {y : (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit (quadShift Ceta)).Page 2 q}
    (h : HasDifferential
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit (quadShift Ceta)) r p q x y) :
    HasDifferential cetaSequence r
      (p.1, p.2 - 1 - 1 - 1 - 1) (q.1, q.2 - 1 - 1 - 1 - 1)
      (cetaDesuspendFour 2 p x) (cetaDesuspendFour 2 q y) := by
  letI : Foundation.TensorInput standardFoundation := Def.StageInput.witness.tensorInput
  exact desuspendFourInternalPage_hasDifferential cetaTowerComparison (cetaShiftTowerComparison 1)
    (Suspension.Construction.towerComparison standardFoundation.hf2 ((Ceta⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧))
    (Suspension.Construction.towerComparison standardFoundation.hf2
      (((Ceta⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)) h

abbrev cwSequence (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0) :=
  adamsTowerInternalSpectralSequence standardFoundation.hf2.unit (CW hzero)

/-- The specified spectrum map followed by its actual four desuspensions. -/
def cwToCetaE2 (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0) (p : ℤ × ℤ) :
    (cwSequence hzero).Page 2 p →ₗ[ℤ]
      cetaSequence.Page 2 (p.1, p.2 - 1 - 1 - 1 - 1) :=
  (cetaDesuspendFour 2 p).hom.comp
    (adamsInternalE2Induced standardFoundation.hf2.unit (toQuadCeta hzero) p)

/-- This common transfer retains every integer page and bidegree. -/
theorem cwToCetaE2_hasDifferential
    (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0)
    {r : ℤ} {p q : ℤ × ℤ}
    {x : (cwSequence hzero).Page 2 p} {y : (cwSequence hzero).Page 2 q}
    (h : HasDifferential (cwSequence hzero) r p q x y) :
    HasDifferential cetaSequence r
      (p.1, p.2 - 1 - 1 - 1 - 1) (q.1, q.2 - 1 - 1 - 1 - 1)
      (cwToCetaE2 hzero p x) (cwToCetaE2 hzero q y) :=
  cetaDesuspendFour_hasDifferential
    (adamsInternalE2Induced_hasDifferential standardFoundation.hf2.unit (toQuadCeta hzero) h)

/-- An interpretation on this same selected CW. Its agreement with the
pinned full native module is an outstanding obligation. -/
abbrev CWCoordinates (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0) :=
  (s t : Nat) → Nat → (cwSequence hzero).Page 2 ((s : ℤ), (t : ℤ))

/-- Exact native D462479; its D tag does not prove this equation. -/
def SourceEquation (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0)
    (coordinates : CWCoordinates hzero) : Prop :=
  HasDifferential (cwSequence hzero) 3 (15, 144) (18, 146)
    (coordinates 15 144 1) (coordinates 18 146 0)

/-- Native N462480 on the existing Cη. The two endpoint equations compare
the native labels with the explicitly constructed actual composite map. -/
theorem row462480 (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0)
    (cwCoordinates : CWCoordinates hzero) (coordinates : CetaCoordinates)
    (source : SourceEquation hzero cwCoordinates)
    (source_comparison : cwToCetaE2 hzero (15, 144) (cwCoordinates 15 144 1) =
      coordinates 15 140 1)
    (target_comparison : cwToCetaE2 hzero (18, 146) (cwCoordinates 18 146 0) =
      coordinates 18 142 0) :
    NaturalityHighStem.SourceEquation coordinates := by
  change HasDifferential cetaSequence 3 (15, 140) (18, 142)
    (coordinates 15 140 1) (coordinates 18 142 0)
  have h := cwToCetaE2_hasDifferential hzero source
  change HasDifferential cetaSequence 3 (15, 140) (18, 142) _ _ at h
  simpa only [source_comparison, target_comparison] using h

/-- Compose the two recorded naturality steps using the same Cη, sphere
presentation and fixed sphere comparisons. All remaining premises are explicit. -/
theorem row462481_from_cw (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0)
    (P : LinE2Presentation) (cwCoordinates : CWCoordinates hzero)
    (coordinates : CetaCoordinates) (source : SourceEquation hzero cwCoordinates)
    (cw_source_comparison : cwToCetaE2 hzero (15, 144) (cwCoordinates 15 144 1) =
      coordinates 15 140 1)
    (cw_target_comparison : cwToCetaE2 hzero (18, 146) (cwCoordinates 18 146 0) =
      coordinates 18 142 0)
    (x1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (15, 139))
    (y1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (18, 141))
    (source_first :
      (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
        15 140
        (adamsInternalE2Induced standardFoundation.hf2.unit topCell (15, 140)
          (coordinates 15 140 1)) x1)
    (target_first :
      (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
        18 142
        (adamsInternalE2Induced standardFoundation.hf2.unit topCell (18, 142)
          (coordinates 18 142 0)) y1)
    (source_second :
      (standardRouteModel.classicalSuspension .sphere).DesuspendsClass
        15 139 x1
        (P.comparison 15 138 (by decide) KIP126.LinE2.NaturalityHighStemCoordinates.source))
    (target_second :
      (standardRouteModel.classicalSuspension .sphere).DesuspendsClass
        18 141 y1
        (P.comparison 18 140 (by decide) KIP126.LinE2.NaturalityHighStemCoordinates.target)) :
    KIP126.Challenge2.DifferentialStatement P
      KIP126.Computation.LinProofs.Raw.NaturalityHighStem.output462481 :=
  NaturalityHighStem.row462481 P coordinates
    (row462480 hzero cwCoordinates coordinates source cw_source_comparison cw_target_comparison)
    x1 y1 source_first target_first source_second target_second

/-- Replay the same native output after deriving the CW null-composite from
this same P and literature. The existing fixed-sphere separation theorem
remains an explicit dependency of that derivation; actual source and coordinate
premises are unchanged. This does not construct a total computation delivery. -/
theorem row462481_from_literature
    (bindings : KIP126.Challenge2.LiteratureBindings)
    (results : KIP126.Challenge2.LiteratureResults bindings)
    (P : LinE2Presentation)
    (cwCoordinates : CWCoordinates (EtaNu.eta_nu_zero bindings results P))
    (coordinates : CetaCoordinates) (source : SourceEquation (EtaNu.eta_nu_zero bindings results P) cwCoordinates)
    (cw_source_comparison : cwToCetaE2 (EtaNu.eta_nu_zero bindings results P) (15, 144) (cwCoordinates 15 144 1) =
      coordinates 15 140 1)
    (cw_target_comparison : cwToCetaE2 (EtaNu.eta_nu_zero bindings results P) (18, 146) (cwCoordinates 18 146 0) =
      coordinates 18 142 0)
    (x1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (15, 139))
    (y1 : PageRepresentatives.Ambient standardFoundation.hf2
      (Sphere (C := standardFoundation.Spectrum) 1) (18, 141))
    (source_first :
      (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
        15 140
        (adamsInternalE2Induced standardFoundation.hf2.unit topCell (15, 140)
          (coordinates 15 140 1)) x1)
    (target_first :
      (standardRouteModel.classicalSuspension (.shift 1 .sphere)).DesuspendsClass
        18 142
        (adamsInternalE2Induced standardFoundation.hf2.unit topCell (18, 142)
          (coordinates 18 142 0)) y1)
    (source_second :
      (standardRouteModel.classicalSuspension .sphere).DesuspendsClass
        15 139 x1
        (P.comparison 15 138 (by decide) KIP126.LinE2.NaturalityHighStemCoordinates.source))
    (target_second :
      (standardRouteModel.classicalSuspension .sphere).DesuspendsClass
        18 141 y1
        (P.comparison 18 140 (by decide) KIP126.LinE2.NaturalityHighStemCoordinates.target)) :
    KIP126.Challenge2.DifferentialStatement P
      KIP126.Computation.LinProofs.Raw.NaturalityHighStem.output462481 :=
  row462481_from_cw (EtaNu.eta_nu_zero bindings results P) P
    cwCoordinates coordinates source cw_source_comparison cw_target_comparison
    x1 y1 source_first target_first source_second target_second

end
end KIP126.Interface.Solution.LinProgram.NaturalityCW
