module

public import KIP126.LinProgram.Certificates.Naturality.Row245131Coordinates
public import KIP126.Interface.Challenge.Computation.Delivery

@[expose] public section


/-!
# Interface/Solution/LinProgram/Naturality/Row245131Coordinates

Fixed-model Interface construction or conditional theorem. A supplied presentation is not constructed by its use.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Literal native coordinates of the fixed sphere representatives used by
log 245131. Singleton witnesses use only archived row membership and value;
no basis delivery, actual map comparison, or differential is assumed. -/
namespace KIP126.Interface.Solution.LinProgram.NaturalityCoordinates
open KIP126.LinE2

/-- Fixed sphere source (2,17)[0] from the same native catalogue. -/
theorem source_hasCoordinates :
    KIP126.Challenge2.HasCoordinates KIP126.LinE2.NaturalityCoordinates.source [0] := by
  refine ⟨[KIP126.LinE2.NaturalityCoordinates.sourceRow], rfl, ?_, ?_⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact ⟨KIP126.LinE2.NaturalityCoordinates.sourceRow_mem, rfl, rfl⟩
  · simpa only [List.map_singleton, List.sum_singleton] using
      KIP126.LinE2.NaturalityCoordinates.source_value

/-- Fixed sphere target (5,19)[0] from the same native catalogue. -/
theorem target_hasCoordinates :
    KIP126.Challenge2.HasCoordinates KIP126.LinE2.NaturalityCoordinates.target [0] := by
  refine ⟨[KIP126.LinE2.NaturalityCoordinates.targetRow], rfl, ?_, ?_⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact ⟨KIP126.LinE2.NaturalityCoordinates.targetRow_mem, rfl, rfl⟩
  · simpa only [List.map_singleton, List.sum_singleton] using
      KIP126.LinE2.NaturalityCoordinates.target_value

end KIP126.Interface.Solution.LinProgram.NaturalityCoordinates
