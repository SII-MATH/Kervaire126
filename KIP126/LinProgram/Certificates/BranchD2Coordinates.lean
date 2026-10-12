module

public import KIP126.Def.Algebra.Coefficients.Data
public import KIP126.LinProgram.Interpretation.Branch.Decode.Data
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic
public import Init.Data.Nat.ToString
public import KIP126.LinProgram.Certificates.SquareDetection.Certificate

import all Init.Data.List.SplitOn.Basic
import all Init.Data.Repr

@[expose] public section


/-! The complete native 5 → 4 → 4 d₂ coordinate complex at the target of
CW_nu_eta log 462479. These are fixed-data matrix theorems. They assert no
comparison with an actual Adams page and no actual candidate coverage.
The input rows are checked against the existing archived database by the
row462481 trace snapshot checker. -/
namespace KIP126.LinProgram.BranchD2Coordinates

open KIP126.Core.Algebra
open KIP126.Computation.LinProofs.Branch

attribute [local cbv_eval] KIP126.LinE2.SquareDetection.splitOn_comma
  KIP126.LinE2.SquareDetection.toNat?_eq_chars Nat.repr_eq_ofList_toDigits

abbrev Coordinates (n : ℕ) := Fin n → F2

def incomingDegree : ℕ × ℕ := (16, 145)
def middleDegree : ℕ × ℕ := (18, 146)
def outgoingDegree : ℕ × ℕ := (20, 147)

/-- Every basis row in the incoming degree, including the four known zeros. -/
def rawIncoming : List (Nat × Option String) :=
  [(5600, some "1,3"), (5601, some ""), (5602, some ""),
   (5603, some ""), (5604, some "")]

/-- Every basis row in the middle degree, in native local-index order. -/
def rawOutgoing : List (Nat × Option String) :=
  [(5720, some ""), (5721, some "2"), (5722, some ""), (5723, some "2")]

def outgoingBasisIds : List Nat := [5854, 5855, 5856, 5857]

inductive MatrixIssue where
  | coordinate (issue : CoordinateIssue)
  | notIncreasing
  | outOfRange
  | columnCount
  deriving Repr, DecidableEq

/-- Preserve SQL NULL and sentinel failures. Reject duplicate, unsorted,
and out-of-range coordinates before constructing a finite vector. -/
def decodeColumn (n : ℕ) (raw : Option String) : Except MatrixIssue (Coordinates n) := do
  let indices ← (decodeCoordinates raw).mapError MatrixIssue.coordinate
  if ¬ indices.Pairwise (· < ·) then throw .notIncreasing
  if ¬ ∀ i ∈ indices, i < n then throw .outOfRange
  return fun i => if i.val ∈ indices then 1 else 0

/-- All columns must be present; a missing column is never a zero column. -/
def decodeMatrix (m n : ℕ) (raw : List (Option String)) :
    Except MatrixIssue (Matrix (Fin m) (Fin n) F2) := do
  let columns ← raw.mapM (decodeColumn m)
  if h : columns.length = n then
    return fun i j => columns.get ⟨j.val, by simp [h]⟩ i
  else throw .columnCount

/-- Columns are respectively [1,3], [], [], [], []. -/
def incomingMatrix : Matrix (Fin 4) (Fin 5) F2 :=
  !![0, 0, 0, 0, 0;
     1, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     1, 0, 0, 0, 0]

/-- Columns are respectively [], [2], [], [2]. -/
def outgoingMatrix : Matrix (Fin 4) (Fin 4) F2 :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 1, 0, 1;
     0, 0, 0, 0]

abbrev incoming : Coordinates 5 →ₗ[F2] Coordinates 4 := incomingMatrix.mulVecLin
abbrev outgoing : Coordinates 4 →ₗ[F2] Coordinates 4 := outgoingMatrix.mulVecLin

theorem incoming_decoded :
    decodeMatrix 4 5 (rawIncoming.map Prod.snd) = .ok incomingMatrix := by
  cbv
  congr 1
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem outgoing_decoded :
    decodeMatrix 4 4 (rawOutgoing.map Prod.snd) = .ok outgoingMatrix := by
  cbv
  congr 1
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Both original domain dimensions are retained in these equations. -/
theorem incoming_apply : ∀ x : Coordinates 5,
    incoming x = ![0, x 0, 0, x 0] := by
  decide +kernel

theorem outgoing_apply : ∀ x : Coordinates 4,
    outgoing x = ![0, 0, x 1 + x 3, 0] := by
  decide +kernel

def boundary : Coordinates 4 := ![0, 1, 0, 1]

/-- The three-dimensional kernel, checked on all sixteen input vectors. -/
theorem kernel_iff (x : Coordinates 4) :
    x ∈ LinearMap.ker outgoing ↔ x 1 = x 3 := by
  have h : ∀ x : Coordinates 4, outgoing x = 0 ↔ x 1 = x 3 := by decide +kernel
  exact h x

/-- The entire image of the five-dimensional incoming domain has two elements. -/
theorem image_iff (x : Coordinates 4) :
    x ∈ LinearMap.range incoming ↔ x = 0 ∨ x = boundary := by
  have h : ∀ x : Coordinates 4,
      (∃ a : Coordinates 5, incoming a = x) ↔ x = 0 ∨ x = boundary := by decide +kernel
  exact h x

theorem image_le_kernel : LinearMap.range incoming ≤ LinearMap.ker outgoing := by
  intro x hx
  rw [image_iff] at hx
  rw [kernel_iff]
  rcases hx with rfl | rfl <;> rfl

/-- Native representatives in exactly the order [], [0], [2], [0,2]. -/
def representative : Fin 4 → Coordinates 4 :=
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 1, 0], ![1, 0, 1, 0]]

def rawRepresentatives : List (Option String) :=
  [some "", some "0", some "2", some "0,2"]

theorem representatives_decoded : ∀ i : Fin 4,
    decodeColumn 4 (rawRepresentatives.get ⟨i.val, i.isLt⟩) = .ok (representative i) := by
  intro i
  fin_cases i <;> cbv
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem representative_mem_kernel : ∀ i : Fin 4,
    representative i ∈ LinearMap.ker outgoing := by
  intro i
  rw [kernel_iff]
  fin_cases i <;> rfl

/-- Exact kernel/image quotient representatives. The quantifier ranges over
ALL four-dimensional native vectors, not just retained trials or listed cycles.
Uniqueness concerns the representative, not a preimage under the incoming map. -/
theorem kernel_mod_image_representatives (x : Coordinates 4) :
    x ∈ LinearMap.ker outgoing ↔
      ∃! i : Fin 4, x - representative i ∈ LinearMap.range incoming := by
  have h : ∀ x : Coordinates 4,
      outgoing x = 0 ↔ ∃ i : Fin 4,
        (∃ a : Coordinates 5, incoming a = x - representative i) ∧
        ∀ j : Fin 4, (∃ a : Coordinates 5, incoming a = x - representative j) → j = i := by
    decide +kernel
  exact h x

end KIP126.LinProgram.BranchD2Coordinates
