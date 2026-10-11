module

public import KIP126.LinProgram.Certificates.AdamsOneLine.H4Source
public import KIP126.LinProgram.Model.Product.Data

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-!
# LinProgram/Certificates/Naturality/Row462481Coordinates

Fixed-data certificate in the original complete quotient or module; it supplies no actual-spectrum comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Fixed native sphere coordinates for naturality log 462481 in the
original quotient. Catalogue membership and value equalities do not assert
that the catalogue is a basis for the actual Adams page. -/
namespace KIP126.LinE2.NaturalityHighStemCoordinates
open MvPolynomial

set_option maxRecDepth 100000
local instance : NeZero RawData.generatorCount := ⟨by decide⟩
attribute [local cbv_eval] BasisCatalogue.splitOn_pipe SquareDetection.splitOn_comma
  SquareDetection.toNat?_eq_chars

/-- Original S0 basis row id3002, local coordinate (15,138)[2]. -/
def sourceRow : BasisRow := ⟨15, 138, 2, "0,2,418,1"⟩
/-- Original S0 basis row id3140, local coordinate (18,140)[2]. -/
def targetRow : BasisRow := ⟨18, 140, 2, "0,2,437,1"⟩

theorem sourceRow_mem : sourceRow ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid
    "15|138|2|0,2,418,1"
  · lin_basis_line 2 "15|138|2|0,2,418,1"
  · cbv

set_option maxHeartbeats 1000000 in
theorem targetRow_mem : targetRow ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid
    "18|140|2|0,2,437,1"
  · lin_basis_line 3 "18|140|2|0,2,437,1"
  · cbv

private theorem degree418 : generatorDegree (418 : Generator) = (13, 136) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk13, RawData.generatorCount,
    Array.getElem!_eq_getD]

private theorem degree437 : generatorDegree (437 : Generator) = (16, 138) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk13, RawData.generatorCount,
    Array.getElem!_eq_getD]

/-- Native x₀²x₄₁₈, with homogeneity proved in the same quotient. -/
noncomputable def source : E2At 15 138 :=
  @mulAt 2 2 13 136 (@mulAt 1 1 1 1 dataH0 dataH0)
    ⟨generator (418 : Generator), by
      simpa only [degree418] using generator_mem (418 : Generator)⟩

/-- Native x₀²x₄₃₇, with homogeneity proved in the same quotient. -/
noncomputable def target : E2At 18 140 :=
  @mulAt 2 2 16 138 (@mulAt 1 1 1 1 dataH0 dataH0)
    ⟨generator (437 : Generator), by
      simpa only [degree437] using generator_mem (437 : Generator)⟩

private theorem parse_monomial (code : String) (ns : List ℕ)
    (hne : code ≠ "")
    (hp : (code.splitOn ",").map (fun n => n.toNat?.getD 0) = ns) :
    monomialOfString code = polynomialOfPowers ns := by
  simp only [monomialOfString, if_neg hne, hp]

private theorem source_polynomial : monomialOfString "0,2,418,1" =
    ((X (0 : Generator)) ^ 2 * X 418 : Poly) := by
  rw [parse_monomial "0,2,418,1" [0,2,418,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

private theorem target_polynomial : monomialOfString "0,2,437,1" =
    ((X (0 : Generator)) ^ 2 * X 437 : Poly) := by
  rw [parse_monomial "0,2,437,1" [0,2,437,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

theorem source_value : source.val = basisValue sourceRow := by
  change (projection (X ⟨0, by decide⟩) * projection (X ⟨0, by decide⟩)) *
    projection (X (418 : Generator)) = projection (monomialOfString "0,2,418,1")
  rw [source_polynomial, map_mul, map_pow, pow_two]
  rfl

theorem target_value : target.val = basisValue targetRow := by
  change (projection (X ⟨0, by decide⟩) * projection (X ⟨0, by decide⟩)) *
    projection (X (437 : Generator)) = projection (monomialOfString "0,2,437,1")
  rw [target_polynomial, map_mul, map_pow, pow_two]
  rfl

end KIP126.LinE2.NaturalityHighStemCoordinates
