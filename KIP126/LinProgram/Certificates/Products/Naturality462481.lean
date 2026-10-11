module

public import KIP126.LinProgram.Model.E2.Proofs
public import KIP126.LinProgram.Tactic.LinRelation
public import KIP126.LinProgram.Certificates.SquareDetection.Certificate
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.MvPolynomial.Basic

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-!
# LinProgram/Certificates/Products/Naturality462481

Fixed-data certificate in the original complete quotient or module; it supplies no actual-spectrum comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Three exact sphere quotient relations in the native context of log 462481.
The first reduces the extra Ceta-to-S0 matrix column; the second is used in
an ancestor trial's formal module calculation. The third reduces the
product used in a reconstruction of a prior native differential. These are statements in the
original 2914-generator quotient, not actual cofiber map or differential
certificates. All native generator identifiers are retained. -/
namespace KIP126.LinE2.NaturalityHighStemProducts

attribute [local cbv_eval] SquareDetection.splitOn_semicolon

set_option maxRecDepth 100000 in
/-- CSV ordinal 10209 (zero based), or S0 relation SQLite rowid 10210. -/
theorem map_relation_mem : "24,1,189,1;7,1,279,1" ∈ RawData.relations := by
  lin_relation 9 "24,1,189,1;7,1,279,1"

set_option maxRecDepth 100000 in
/-- CSV ordinal 13636 (zero based), or S0 relation SQLite rowid 13637. -/
theorem h0_relation_mem : "0,1,519,1" ∈ RawData.relations := by
  lin_relation 13 "0,1,519,1"

set_option maxRecDepth 100000 in
/-- CSV ordinal 10935 (zero based), or S0 relation SQLite rowid 10936. -/
theorem ancestor_relation_mem : "3,1,358,1;0,2,437,1" ∈ RawData.relations := by
  lin_relation 10 "3,1,358,1;0,2,437,1"

/-- The full source matrix's first column has this exact quotient reduction.
Its use as a map on actual Adams pages still needs the actual map comparison. -/
theorem native_map_column0 :
    projection (monomialOfString "24,1,189,1") =
      projection (monomialOfString "7,1,279,1") := by
  have h := csv_relation_zero _ map_relation_mem
  have hs : "24,1,189,1;7,1,279,1".splitOn ";" =
      ["24,1,189,1", "7,1,279,1"] := by cbv
  have hn : -(projection (monomialOfString "7,1,279,1")) =
      projection (monomialOfString "7,1,279,1") := by
    rw [← map_neg]
    exact congrArg projection (CharTwo.neg_eq _)
  simpa only [relationPolynomial, hs, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, map_add,
    add_eq_zero_iff_eq_neg, hn] using h

/-- Exact zero product used by the native h0 trial diagnostic. It does not
prove the corresponding CW module product or any boundary nonmembership. -/
theorem native_h0_product_zero :
    projection (monomialOfString "0,1,519,1") = 0 := by
  have h := csv_relation_zero _ h0_relation_mem
  have hs : "0,1,519,1".splitOn ";" = ["0,1,519,1"] := by cbv
  simpa only [relationPolynomial, hs, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] using h

/-- Exact product in the independent native reconstruction of the prior
CW differential. No actual CW module action or historical trace edge is inferred. -/
theorem native_ancestor_product :
    projection (monomialOfString "3,1,358,1") =
      projection (monomialOfString "0,2,437,1") := by
  have h := csv_relation_zero _ ancestor_relation_mem
  have hs : "3,1,358,1;0,2,437,1".splitOn ";" =
      ["3,1,358,1", "0,2,437,1"] := by cbv
  have hn : -(projection (monomialOfString "0,2,437,1")) =
      projection (monomialOfString "0,2,437,1") := by
    rw [← map_neg]
    exact congrArg projection (CharTwo.neg_eq _)
  simpa only [relationPolynomial, hs, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, map_add,
    add_eq_zero_iff_eq_neg, hn] using h

end KIP126.LinE2.NaturalityHighStemProducts
