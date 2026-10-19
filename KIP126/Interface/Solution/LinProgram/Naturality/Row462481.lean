module

public import KIP126.Interface.Solution.LinProgram.Naturality.Row245131
public import KIP126.LinProgram.Certificates.Naturality.Row462481Coordinates
public import KIP126.LinProgram.Raw.NaturalityHighStem

@[expose] public section


/-!
# Interface/Solution/LinProgram/Naturality/Row462481

Fixed-model Interface construction or conditional theorem. A supplied presentation is not constructed by its use.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Conditional actual replay of native naturality log 462481. Both sphere
coordinates are proved for the original quotient, and the same actual Ceta,
eta map, top-cell map, tower comparisons and presentation are used throughout.
The source differential and four actual coordinate comparisons remain
explicit. The source's N tag and the surrounding trial trace supply none of
these premises. No aggregate computation delivery or consumer is read. -/
namespace KIP126.Interface.Solution.LinProgram.NaturalityHighStem

open CategoryTheory KIP126.StableHomotopy KIP126.Classical.Adams
open KIP126.Core.SpectralSequence KIP126.LinE2
open Naturality

noncomputable section

/-- Literal (15,138)[2] from archived S0 basis row 3002. -/
theorem source_hasCoordinates :
    KIP126.Challenge2.HasCoordinates
      KIP126.LinE2.NaturalityHighStemCoordinates.source [2] := by
  refine ⟨[KIP126.LinE2.NaturalityHighStemCoordinates.sourceRow], rfl, ?_, ?_⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact ⟨KIP126.LinE2.NaturalityHighStemCoordinates.sourceRow_mem, rfl, rfl⟩
  · simpa only [List.map_singleton, List.sum_singleton] using
      KIP126.LinE2.NaturalityHighStemCoordinates.source_value

/-- Literal (18,140)[2] from archived S0 basis row 3140. -/
theorem target_hasCoordinates :
    KIP126.Challenge2.HasCoordinates
      KIP126.LinE2.NaturalityHighStemCoordinates.target [2] := by
  refine ⟨[KIP126.LinE2.NaturalityHighStemCoordinates.targetRow], rfl, ?_, ?_⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact ⟨KIP126.LinE2.NaturalityHighStemCoordinates.targetRow_mem, rfl, rfl⟩
  · simpa only [List.map_singleton, List.sum_singleton] using
      KIP126.LinE2.NaturalityHighStemCoordinates.target_value

/-- Exact Ceta source of N record 462480. This remains an actual differential
premise, independently of the recorded reason and adjacent branch events. -/
def SourceEquation (coordinates : CetaCoordinates) : Prop :=
  HasDifferential cetaSequence 3 (15, 140) (18, 142)
    (coordinates 15 140 1) (coordinates 18 142 0)

/-- The fixed native sphere output under the exact source differential and
four actual map-coordinate comparisons. The coordinate lists are proved;
no nonzero later-page class, paper-name conversion or branch conclusion
is inferred from a nonempty native vector. -/
theorem row462481 (P : LinE2Presentation) (coordinates : CetaCoordinates)
    (source : SourceEquation coordinates)
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
      KIP126.Computation.LinProofs.Raw.NaturalityHighStem.output462481 := by
  have h : HasDifferential sphereAdamsData 3 (15, 138) (18, 140)
      (P.comparison 15 138 (by decide) KIP126.LinE2.NaturalityHighStemCoordinates.source)
      (P.comparison 18 140 (by decide) KIP126.LinE2.NaturalityHighStemCoordinates.target) :=
    topCell_hasDifferential_desuspendTwice 3 15 140 18 142
      (coordinates 15 140 1) (coordinates 18 142 0) x1 y1
      (P.comparison 15 138 (by decide) KIP126.LinE2.NaturalityHighStemCoordinates.source)
      (P.comparison 18 140 (by decide) KIP126.LinE2.NaturalityHighStemCoordinates.target)
      source_first target_first source_second target_second source
  exact Naturality.statement_of_hasDifferential P
    KIP126.Computation.LinProofs.Raw.NaturalityHighStem.output462481
    (by decide) (by decide)
    KIP126.LinE2.NaturalityHighStemCoordinates.source
    KIP126.LinE2.NaturalityHighStemCoordinates.target
    source_hasCoordinates target_hasCoordinates h

end
end KIP126.Interface.Solution.LinProgram.NaturalityHighStem
