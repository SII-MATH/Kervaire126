module

public import KIP126.LinProgram.Certificates.AdamsOneLine.H4Source
public import KIP126.LinProgram.Model.Product.Data

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-!
# LinProgram/Certificates/Naturality/Row245131Coordinates

Fixed-data certificate in the original complete quotient or module; it supplies no actual-spectrum comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Fixed native sphere coordinates for naturality log 245131. The values
belong to the same archived quotient. Exact catalogue membership and values
supply literal coordinates without a mathematical basis certification. -/
namespace KIP126.LinE2.NaturalityCoordinates
open MvPolynomial

set_option maxRecDepth 100000
local instance : NeZero RawData.generatorCount := ⟨by decide⟩
attribute [local cbv_eval] BasisCatalogue.splitOn_pipe SquareDetection.splitOn_comma
  SquareDetection.toNat?_eq_chars

/-- Original S0 basis row id39, local coordinate (2,17)[0]. -/
def sourceRow : BasisRow := ⟨2, 17, 0, "0,1,7,1"⟩
/-- Original S0 basis row id46, local coordinate (5,19)[0]. -/
def targetRow : BasisRow := ⟨5, 19, 0, "0,1,8,1"⟩

theorem sourceRow_mem : sourceRow ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid
    "2|17|0|0,1,7,1"
  · lin_basis_line 0 "2|17|0|0,1,7,1"
  · cbv

theorem targetRow_mem : targetRow ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid
    "5|19|0|0,1,8,1"
  · lin_basis_line 0 "5|19|0|0,1,8,1"
  · cbv

private theorem degree8 : generatorDegree (8 : Generator) = (4, 18) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount,
    Array.getElem!_eq_getD]

/-- The native source is the product of the already constructed data classes. -/
noncomputable def source : E2At 2 17 := @mulAt 1 1 1 16 dataH0 OneLine.dataH4

noncomputable def target : E2At 5 19 :=
  @mulAt 1 1 4 18 dataH0
    ⟨generator (8 : Generator), by simpa only [degree8] using generator_mem (8 : Generator)⟩

private theorem parse_monomial (code : String) (ns : List ℕ)
    (hne : code ≠ "")
    (hp : (code.splitOn ",").map (fun n => n.toNat?.getD 0) = ns) :
    monomialOfString code = polynomialOfPowers ns := by
  simp only [monomialOfString, if_neg hne, hp]

private theorem source_polynomial : monomialOfString "0,1,7,1" =
    (X (0 : Generator) * X 7 : Poly) := by
  rw [parse_monomial "0,1,7,1" [0,1,7,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

private theorem target_polynomial : monomialOfString "0,1,8,1" =
    (X (0 : Generator) * X 8 : Poly) := by
  rw [parse_monomial "0,1,8,1" [0,1,8,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

theorem source_value : source.val = basisValue sourceRow := by
  change projection (X ⟨0, by decide⟩) * projection (X (7 : Generator)) =
    projection (monomialOfString "0,1,7,1")
  rw [source_polynomial, map_mul]
  rfl

theorem target_value : target.val = basisValue targetRow := by
  change projection (X ⟨0, by decide⟩) * projection (X (8 : Generator)) =
    projection (monomialOfString "0,1,8,1")
  rw [target_polynomial, map_mul]
  rfl

end KIP126.LinE2.NaturalityCoordinates
