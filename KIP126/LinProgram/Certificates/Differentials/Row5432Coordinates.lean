module

public import KIP126.LinProgram.Certificates.BasisCatalogue.Archive
public import KIP126.LinProgram.Tactic.LinBasisLine
public import KIP126.LinProgram.Model.E2.Proofs
public import KIP126.LinProgram.Certificates.SquareDetection.Certificate

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-!
# LinProgram/Certificates/Differentials/Row5432Coordinates

Fixed-data certificate in the original complete quotient or module; it supplies no actual-spectrum comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Local source-coordinate certificates for the first low-stem replay.
These prove facts about the fixed data quotient, not sphere differentials. -/
namespace KIP126.LinE2.LowStem
open MvPolynomial

/-- The source of proofs.db record 5432, in the original local coordinates. -/
def ph1Row : BasisRow := ⟨5, 14, 0, "5,1"⟩

theorem ph1_degree : generatorDegree ⟨5, by decide⟩ = (5, 14) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount,
    Array.getElem!_eq_getD]

noncomputable def ph1 : E2At 5 14 :=
  ⟨generator ⟨5, by decide⟩, by
    simpa only [ph1_degree] using generator_mem ⟨5, by decide⟩⟩

theorem ph1_value : ph1.val = basisValue ph1Row := by
  have hs : "5,1".splitOn "," = ["5", "1"] := by
    rw [SquareDetection.splitOn_comma]
    decide
  have h5 : "5".toNat? = some 5 := by
    rw [SquareDetection.toNat?_eq_chars]
    cbv
  have h1 : "1".toNat? = some 1 := by
    rw [SquareDetection.toNat?_eq_chars]
    cbv
  simp [ph1, basisValue, ph1Row, monomialOfString, hs, h5, h1,
    polynomialOfPowers, RawData.generatorCount, generator]

attribute [local cbv_eval] BasisCatalogue.splitOn_pipe SquareDetection.toNat?_eq_chars

set_option maxRecDepth 100000 in
/-- Exact membership in the original CSV catalogue, using certified parser
success rather than assuming that the catalogue is a mathematical basis. -/
theorem ph1Row_mem : ph1Row ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid
    "5|14|0|5,1"
  · lin_basis_line 0 "5|14|0|5,1"
  · cbv

end KIP126.LinE2.LowStem
