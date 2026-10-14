module

public import KIP126.LinProgram.Model.E2.Proofs
public import KIP126.LinProgram.Tactic.LinRelation
public import KIP126.LinProgram.Certificates.SquareDetection.Certificate
public import Mathlib.Tactic.Ring

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-!
# LinProgram/Certificates/Products/Trial152097

Fixed-data certificate in the original complete quotient or module; it supplies no actual-spectrum comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Closed certificates for the two product reductions used in the native
proofs.db trial 152097, preceding the retained D record 152098. The conclusion
is about the fixed CSV quotient E2. No Adams differential or basis independence
is inferred from these algebraic identities. -/
namespace KIP126.LinE2.ReplayProducts
open MvPolynomial

local instance : NeZero RawData.generatorCount := ⟨by decide⟩
attribute [local cbv_eval] SquareDetection.splitOn_comma
  SquareDetection.splitOn_semicolon SquareDetection.toNat?_eq_chars

set_option maxRecDepth 100000 in
theorem relation26_mem : "1,1,9,1;0,1,10,1" ∈ RawData.relations := by
  lin_relation 0 "1,1,9,1;0,1,10,1"

set_option maxRecDepth 100000 in
theorem relation188_mem : "10,1,13,1;2,1,32,1" ∈ RawData.relations := by
  lin_relation 0 "10,1,13,1;2,1,32,1"

set_option maxRecDepth 100000 in
theorem relation190_mem : "2,1,32,1;0,2,36,1" ∈ RawData.relations := by
  lin_relation 0 "2,1,32,1;0,2,36,1"

private theorem parse_monomial (code : String) (ns : List ℕ)
    (hne : code ≠ "")
    (hp : (code.splitOn ",").map (fun n => n.toNat?.getD 0) = ns) :
    monomialOfString code = polynomialOfPowers ns := by
  simp only [monomialOfString, if_neg hne, hp]

private theorem monomial_01 : monomialOfString "0,1,1,1" =
    (X (0 : Generator) * X 1 : Poly) := by
  rw [parse_monomial "0,1,1,1" [0,1,1,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

private theorem monomial_19 : monomialOfString "1,1,9,1" =
    (X (1 : Generator) * X 9 : Poly) := by
  rw [parse_monomial "1,1,9,1" [1,1,9,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

private theorem monomial_010 : monomialOfString "0,1,10,1" =
    (X (0 : Generator) * X 10 : Poly) := by
  rw [parse_monomial "0,1,10,1" [0,1,10,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

private theorem monomial_1013 : monomialOfString "10,1,13,1" =
    (X (10 : Generator) * X 13 : Poly) := by
  rw [parse_monomial "10,1,13,1" [10,1,13,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

private theorem monomial_232 : monomialOfString "2,1,32,1" =
    (X (2 : Generator) * X 32 : Poly) := by
  rw [parse_monomial "2,1,32,1" [2,1,32,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

private theorem monomial_036 : monomialOfString "0,2,36,1" =
    (X (0 : Generator) ^ 2 * X 36 : Poly) := by
  rw [parse_monomial "0,2,36,1" [0,2,36,1] (by decide) (by cbv)]
  norm_num [polynomialOfPowers, RawData.generatorCount]
  rfl

private theorem relation1 :
    generator (0 : Generator) * generator 1 = 0 := by
  have hmem : "0,1,1,1" ∈ RawData.relations :=
    List.mem_append_left _ (by simp [RawData.firstRelations])
  have h := csv_relation_zero _ hmem
  have hs : "0,1,1,1".splitOn ";" = ["0,1,1,1"] := by cbv
  simpa only [relationPolynomial, hs, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, monomial_01, map_mul, generator] using h

private theorem relation26 :
    generator (1 : Generator) * generator 9 + generator 0 * generator 10 = 0 := by
  have h := csv_relation_zero _ relation26_mem
  have hs : "1,1,9,1;0,1,10,1".splitOn ";" = ["1,1,9,1", "0,1,10,1"] := by cbv
  simpa only [relationPolynomial, hs, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, monomial_19, monomial_010,
    map_add, map_mul, generator] using h

private theorem relation188 :
    generator (10 : Generator) * generator 13 + generator 2 * generator 32 = 0 := by
  have h := csv_relation_zero _ relation188_mem
  have hs : "10,1,13,1;2,1,32,1".splitOn ";" = ["10,1,13,1", "2,1,32,1"] := by cbv
  simpa only [relationPolynomial, hs, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, monomial_1013, monomial_232,
    map_add, map_mul, generator] using h

private theorem relation190 :
    generator (2 : Generator) * generator 32 + generator 0 ^ 2 * generator 36 = 0 := by
  have h := csv_relation_zero _ relation190_mem
  have hs : "2,1,32,1;0,2,36,1".splitOn ";" = ["2,1,32,1", "0,2,36,1"] := by cbv
  simpa only [relationPolynomial, hs, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, monomial_232, monomial_036,
    map_add, map_mul, map_pow, generator] using h

/-- First archived product reduction, certified in the actual fixed quotient. -/
theorem source_product_zero :
    generator (0 : Generator) ^ 2 * generator 1 * generator 3 * generator 18 = 0 := by
  calc
    _ = (generator 0 * generator 3 * generator 18) *
        (generator 0 * generator 1) := by ring
    _ = 0 := by rw [relation1, mul_zero]

/-- Three archived relations certify the nontrivial product reduction. -/
theorem target_product :
    generator (1 : Generator) * generator 9 * generator 13 =
      generator 0 ^ 3 * generator 36 := by
  have hp : (1 : Poly) + 1 = 0 := by
    have hc : (1 : KIP126.Core.Algebra.F2) + 1 = 0 := by decide
    simpa only [map_add, map_one, map_zero] using
      congrArg (MvPolynomial.C : KIP126.Core.Algebra.F2 →+* Poly) hc
  have he : (1 : E2) + 1 = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg projection hp
  have h2 : (2 : E2) = 0 := by simpa only [one_add_one_eq_two] using he

  calc
    _ = generator 0 ^ 3 * generator 36 +
      (generator 13 * (generator 1 * generator 9 + generator 0 * generator 10) +
       generator 0 * (generator 10 * generator 13 + generator 2 * generator 32) +
       generator 0 * (generator 2 * generator 32 + generator 0 ^ 2 * generator 36)) := by
      ring_nf
      simp [h2]
    _ = _ := by rw [relation26, relation188, relation190]; simp

/-- Native monomial statement; no paper aliases enter the target. -/
theorem native_target_product :
    projection (monomialOfString "1,1,9,1,13,1") =
      projection (monomialOfString "0,3,36,1") := by
  have hs : monomialOfString "1,1,9,1,13,1" =
      (X (1 : Generator) * (X 9 * X 13) : Poly) := by
    rw [parse_monomial "1,1,9,1,13,1" [1,1,9,1,13,1] (by decide) (by cbv)]
    norm_num [polynomialOfPowers, RawData.generatorCount]
    rfl
  have ht : monomialOfString "0,3,36,1" =
      (X (0 : Generator) ^ 3 * X 36 : Poly) := by
    rw [parse_monomial "0,3,36,1" [0,3,36,1] (by decide) (by cbv)]
    norm_num [polynomialOfPowers, RawData.generatorCount]
    rfl
  rw [hs, ht]
  simpa only [map_mul, map_pow, generator, mul_assoc] using target_product

/-- Native first product statement, retaining all original generators. -/
theorem native_source_product_zero :
    projection (monomialOfString "0,2,1,1,3,1,18,1") = 0 := by
  have hs : monomialOfString "0,2,1,1,3,1,18,1" =
      (X (0 : Generator) ^ 2 * (X 1 * (X 3 * X 18)) : Poly) := by
    rw [parse_monomial "0,2,1,1,3,1,18,1" [0,2,1,1,3,1,18,1] (by decide) (by cbv)]
    norm_num [polynomialOfPowers, RawData.generatorCount]
    rfl
  rw [hs]
  simpa only [map_mul, map_pow, generator, mul_assoc] using source_product_zero

end KIP126.LinE2.ReplayProducts
