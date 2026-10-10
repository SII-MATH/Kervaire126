import Mathlib.Data.List.Basic
import Lean.Elab.Tactic

/-!
Executable prime-two Milnor dual coproduct certificates in a finite degree window.
Monomial coordinate 0 denotes xi_1; xi_0 = 1. Polynomial lists carry F_2
coefficients by multiplicity modulo two, so cancellation is mathematical parity.
The semantics is the dual of the explicit Milnor coproduct, not a comparison
with an unverified C++ multiplication answer. Identification with Steenrod
operations on topological cohomology is outside this module.
-/
namespace MilnorCertificates

abbrev Monomial := List Nat
abbrev Polynomial := List Monomial
abbrev TensorMonomial := Monomial × Monomial

def unitMonomial (rank : Nat) : Monomial := List.replicate rank 0

def multiplyMonomial (a b : Monomial) : Monomial :=
  List.zipWith (· + ·) a b

def generatorPower (rank index exponent : Nat) : Monomial :=
  (List.range rank).map fun j => if j + 1 = index then exponent else 0

def tensorMultiply (a b : List TensorMonomial) : List TensorMonomial :=
  a.flatMap fun x => b.map fun y =>
    (multiplyMonomial x.1 y.1, multiplyMonomial x.2 y.2)

def tensorPower (rank : Nat) (a : List TensorMonomial) : Nat → List TensorMonomial
  | 0 => [(unitMonomial rank, unitMonomial rank)]
  | n + 1 => tensorMultiply (tensorPower rank a n) a

/-- Delta(xi_k) = sum_{i=0}^k xi_{k-i}^{2^i} tensor xi_i. -/
def generatorCoproduct (rank k : Nat) : List TensorMonomial :=
  (List.range (k + 1)).map fun i =>
    (generatorPower rank (k - i) (2 ^ i), generatorPower rank i 1)

/-- Extend the generator coproduct multiplicatively on the polynomial algebra. -/
def coproduct (rank : Nat) (m : Monomial) : List TensorMonomial :=
  ((List.range rank).map fun j =>
    tensorPower rank (generatorCoproduct rank (j + 1)) (m[j]?.getD 0)).foldl
    tensorMultiply [(unitMonomial rank, unitMonomial rank)]

def coefficient (p : Polynomial) (m : Monomial) : Bool :=
  (p.filter (· == m)).length % 2 == 1

/-- Evaluation of a tensor product of dual functionals over F_2. -/
def pairTensor (left right : Polynomial) (terms : List TensorMonomial) : Bool :=
  (terms.filter fun t => coefficient left t.1 && coefficient right t.2).length % 2 == 1

def weight (m : Monomial) : Nat :=
  ((List.range m.length).map fun j => (m[j]?.getD 0) * (2 ^ (j + 1) - 1)).sum

def exponentVectors : Nat → Nat → List Monomial
  | 0, _ => [[]]
  | n + 1, bound => (List.range (bound + 1)).flatMap fun e =>
      (exponentVectors n bound).map (e :: ·)

/-- All dual basis tests in the declared finite degree window. -/
def basis (rank bound : Nat) : List Monomial :=
  (exponentVectors rank bound).filter fun m => weight m ≤ bound

def polynomialInWindow (rank bound : Nat) (p : Polynomial) : Bool :=
  p.all fun m => m.length == rank && decide (weight m ≤ bound)

structure Window where
  rank : Nat
  degree : Nat
  deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson

/-- Equality in the dual of the degree-window Milnor coalgebra. This statement
tests every basis monomial in the window, including omitted output coefficients.
It is a finite-window claim; it does not claim unbounded Steenrod multiplication. -/
def IsMilnorProduct (w : Window) (left right output : Polynomial) : Prop :=
  polynomialInWindow w.rank w.degree left = true ∧
  polynomialInWindow w.rank w.degree right = true ∧
  polynomialInWindow w.rank w.degree output = true ∧
  ∀ m ∈ basis w.rank w.degree,
    coefficient output m = pairTensor left right (coproduct w.rank m)

structure Certificate where
  version : Nat := 1
  window : Window
  /-- Complete ordered expansion table, one row per basis monomial. -/
  expansions : List (List TensorMonomial)
  deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson

def check (w : Window) (left right output : Polynomial) (c : Certificate) : Bool :=
  decide (c.version = 1) && decide (c.window = w) &&
  polynomialInWindow w.rank w.degree left &&
  polynomialInWindow w.rank w.degree right &&
  polynomialInWindow w.rank w.degree output &&
  decide (c.expansions = (basis w.rank w.degree).map (coproduct w.rank)) &&
  ((basis w.rank w.degree).zip c.expansions).all fun row =>
    coefficient output row.1 == pairTensor left right row.2

theorem check_sound (w : Window) (left right output : Polynomial) (c : Certificate)
    (h : check w left right output c = true) : IsMilnorProduct w left right output := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨_, _⟩, hl⟩, hr⟩, ho⟩, he⟩, hp⟩
  refine ⟨hl, hr, ho, ?_⟩
  rw [he] at hp
  intro m hm
  have hz : (m, coproduct w.rank m) ∈
      (basis w.rank w.degree).zip ((basis w.rank w.degree).map (coproduct w.rank)) := by
    rw [List.zip_map_right]
    apply List.mem_map.mpr
    refine ⟨(m, m), ?_, rfl⟩
    change (m, m) ∈ List.zipWith Prod.mk (basis w.rank w.degree) (basis w.rank w.degree)
    rw [List.zipWith_self]
    exact List.mem_map.mpr ⟨m, hm, rfl⟩
  have := List.all_eq_true.mp hp _ hz
  simpa only [beq_iff_eq] using this

def generate (w : Window) : Certificate :=
  ⟨1, w, (basis w.rank w.degree).map (coproduct w.rank)⟩

/-- Row diagnostics refer to the ordered basis, independent of producer labels. -/
def diagnose (w : Window) (left right output : Polynomial) (c : Certificate) : List String := Id.run do
  let mut errors := []
  if c.version != 1 then errors := errors ++ ["unsupported certificate version"]
  if c.window != w then errors := errors ++ ["certificate window does not match goal"]
  if !polynomialInWindow w.rank w.degree left then errors := errors ++ ["left input outside window"]
  if !polynomialInWindow w.rank w.degree right then errors := errors ++ ["right input outside window"]
  if !polynomialInWindow w.rank w.degree output then errors := errors ++ ["output outside window"]
  let bs := basis w.rank w.degree
  if c.expansions.length != bs.length then errors := errors ++ ["incomplete expansion table"]
  for i in List.range bs.length do
    let m := bs[i]!
    if c.expansions[i]? != some (coproduct w.rank m) then
      errors := errors ++ [s!"coproduct mismatch at row {i}: {m}"]
    if coefficient output m != pairTensor left right (coproduct w.rank m) then
      errors := errors ++ [s!"product coefficient mismatch at row {i}: {m}"]
  return errors

open Lean Elab Tactic

syntax "milnor_cert" " using " term : tactic
elab_rules : tactic
  | `(tactic| milnor_cert using $c:term) => do
      evalTactic (← `(tactic| exact MilnorCertificates.check_sound _ _ _ _ $c (by decide)))

end MilnorCertificates
