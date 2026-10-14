module

public import KIP126.LinProgram.Certificates.Products.Trial152097
public import KIP126.LinProgram.Certificates.BasisCatalogue.Archive
public import KIP126.LinProgram.Tactic.LinBasisLine
public import KIP126.LinProgram.Model.Classes.Data
public import KIP126.LinProgram.Model.Product.Data

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-!
# LinProgram/Certificates/Products/Trial152097Coordinates

Fixed-data certificate in the original complete quotient or module; it supplies no actual-spectrum comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Typed coordinates for the product diagnostic of native trial 152097.
The four rows retain their native indices and monomial strings. Membership
in the archived catalogue does not assert independence, spanning, nonvanishing,
or any differential, and no actual-model delivery enters these proofs. -/
namespace KIP126.LinE2.ReplayCoordinates
set_option maxRecDepth 100000
open MvPolynomial

local instance : NeZero RawData.generatorCount := ⟨by decide⟩
attribute [local cbv_eval] BasisCatalogue.splitOn_pipe SquareDetection.splitOn_comma
  SquareDetection.toNat?_eq_chars

/-- Source coordinate shared by the trial 152097 and retained record 152098. -/
def sourceRow : BasisRow := ⟨4, 42, 1, "0,2,3,1,18,1"⟩
def multiplierRow : BasisRow := ⟨1, 2, 0, "1,1"⟩
/-- The nonzero-coordinate candidate target of the trial, not record 152098's zero target. -/
def trialTargetRow : BasisRow := ⟨8, 45, 0, "9,1,13,1"⟩
def productTargetRow : BasisRow := ⟨9, 47, 0, "0,3,36,1"⟩

set_option maxRecDepth 100000 in
theorem sourceRow_mem : sourceRow ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid
    "4|42|1|0,2,3,1,18,1"
  · lin_basis_line 0 "4|42|1|0,2,3,1,18,1"
  · cbv

set_option maxRecDepth 100000 in
theorem multiplierRow_mem : multiplierRow ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid
    "1|2|0|1,1"
  · lin_basis_line 0 "1|2|0|1,1"
  · cbv

set_option maxRecDepth 100000 in
theorem trialTargetRow_mem : trialTargetRow ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid
    "8|45|0|9,1,13,1"
  · lin_basis_line 0 "8|45|0|9,1,13,1"
  · cbv

set_option maxRecDepth 100000 in
theorem productTargetRow_mem : productTargetRow ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid
    "9|47|0|0,3,36,1"
  · lin_basis_line 0 "9|47|0|0,3,36,1"
  · cbv

private theorem degree0 : generatorDegree (0 : Generator) = (1, 1) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount,
    Array.getElem!_eq_getD]

private theorem degree3 : generatorDegree (3 : Generator) = (1, 8) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount,
    Array.getElem!_eq_getD]

private theorem degree18 : generatorDegree (18 : Generator) = (1, 32) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount,
    Array.getElem!_eq_getD]

private theorem degree9 : generatorDegree (9 : Generator) = (4, 21) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount,
    Array.getElem!_eq_getD]

private theorem degree13 : generatorDegree (13 : Generator) = (4, 24) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount,
    Array.getElem!_eq_getD]

private theorem degree36 : generatorDegree (36 : Generator) = (6, 44) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk1, RawData.generatorCount,
    Array.getElem!_eq_getD]

noncomputable def source : E2At 4 42 :=
  ⟨generator (0 : Generator) ^ 2 * generator 3 * generator 18, by
    simpa only [degree0, degree3, degree18] using
      multiply_mem (multiply_mem (generator_pow_mem (0 : Generator) 2)
        (generator_mem (3 : Generator))) (generator_mem (18 : Generator))⟩

noncomputable def trialTarget : E2At 8 45 :=
  ⟨generator (9 : Generator) * generator 13, by
    simpa only [degree9, degree13] using
      multiply_mem (generator_mem (9 : Generator)) (generator_mem (13 : Generator))⟩

noncomputable def productTarget : E2At 9 47 :=
  ⟨generator (0 : Generator) ^ 3 * generator 36, by
    simpa only [degree0, degree36] using
      multiply_mem (generator_pow_mem (0 : Generator) 3) (generator_mem (36 : Generator))⟩

private theorem parse_monomial (code : String) (ns : List ℕ)
    (hne : code ≠ "")
    (hp : (code.splitOn ",").map (fun n => n.toNat?.getD 0) = ns) :
    monomialOfString code = polynomialOfPowers ns := by
  simp only [monomialOfString, if_neg hne, hp]

private theorem source_polynomial : monomialOfString "0,2,3,1,18,1" =
    (X (0 : Generator) ^ 2 * (X 3 * X 18) : Poly) := by
  rw [parse_monomial "0,2,3,1,18,1" [0,2,3,1,18,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

private theorem multiplier_polynomial : monomialOfString "1,1" =
    (X (1 : Generator) : Poly) := by
  rw [parse_monomial "1,1" [1,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

private theorem trialTarget_polynomial : monomialOfString "9,1,13,1" =
    (X (9 : Generator) * X 13 : Poly) := by
  rw [parse_monomial "9,1,13,1" [9,1,13,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

private theorem productTarget_polynomial : monomialOfString "0,3,36,1" =
    (X (0 : Generator) ^ 3 * X 36 : Poly) := by
  rw [parse_monomial "0,3,36,1" [0,3,36,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

theorem source_value : source.val = basisValue sourceRow := by
  simp only [source, basisValue, sourceRow, source_polynomial, map_mul, map_pow,
    generator, mul_assoc]

theorem multiplier_value : dataH1.val = basisValue multiplierRow := by
  simp only [dataH1, h1, basisValue, multiplierRow, multiplier_polynomial, generator]
  rfl

theorem trialTarget_value : trialTarget.val = basisValue trialTargetRow := by
  simp only [trialTarget, basisValue, trialTargetRow, trialTarget_polynomial, map_mul, generator]

theorem productTarget_value : productTarget.val = basisValue productTargetRow := by
  simp only [productTarget, basisValue, productTargetRow, productTarget_polynomial,
    map_mul, map_pow, generator]

/-- The native source times the native multiplier is zero in degree (5,44). -/
theorem source_mul_multiplier : mulAt source dataH1 = (0 : E2At 5 44) := by
  apply Subtype.ext
  change (generator (0 : Generator) ^ 2 * generator 3 * generator 18) * generator 1 = 0
  calc
    _ = generator 0 ^ 2 * generator 1 * generator 3 * generator 18 := by ring
    _ = 0 := ReplayProducts.source_product_zero

/-- The trial target times the multiplier has the recorded coordinate (9,47)[0]. -/
theorem multiplier_mul_trialTarget : mulAt dataH1 trialTarget = productTarget := by
  apply Subtype.ext
  change generator (1 : Generator) * (generator 9 * generator 13) = generator 0 ^ 3 * generator 36
  simpa only [mul_assoc] using ReplayProducts.target_product

end KIP126.LinE2.ReplayCoordinates
