module

public import KIP126.LinProgram.Certificates.NamedElements.Evaluation
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

@[expose] public section


namespace NamedElementCertificates.ModuleExpressions
open scoped BigOperators

/-- A finite free-module expression; slot i is the polynomial on generator i. -/
abbrev Expression (n : Nat) := Fin n → Polynomial

def add (a b : Expression n) : Expression n := fun i => a i ++ b i
def scale (p : Polynomial) (a : Expression n) : Expression n := fun i => multiply p (a i)
def zero : Expression n := fun _ => []

def combine (relations : List (Expression n)) : List Term → Expression n
  | [] => zero
  | t :: ts => add (scale t.multiplier (relations[t.relation]?.getD zero)) (combine relations ts)

def check (relations : List (Expression n)) (input output : Expression n) (terms : List Term) : Bool :=
  terms.all (fun t => t.relation < relations.length) &&
  decide (∀ i : Fin n, NamedElementCertificates.check []
    (input i ++ output i) (combine relations terms i) [] = true)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def evaluate (v : Nat → R) (generators : Fin n → M) (a : Expression n) : M :=
  ∑ i, NamedElementCertificates.evaluate v (a i) • generators i

theorem evaluate_add (v : Nat → R) (g : Fin n → M) (a b : Expression n) :
    evaluate v g (add a b) = evaluate v g a + evaluate v g b := by
  simp [evaluate, add, evaluate_append, add_smul, Finset.sum_add_distrib]

theorem evaluate_scale (v : Nat → R) (g : Fin n → M) (p : Polynomial) (a : Expression n) :
    evaluate v g (scale p a) = NamedElementCertificates.evaluate v p • evaluate v g a := by
  simp [evaluate, scale, evaluate_multiply, mul_smul, Finset.smul_sum]

theorem evaluate_zero (v : Nat → R) (g : Fin n → M) : evaluate v g zero = 0 := by
  simp [evaluate, zero, NamedElementCertificates.evaluate]

theorem evaluate_combine (v : Nat → R) (g : Fin n → M) (relations : List (Expression n))
    (terms : List Term) (hr : ∀ r ∈ relations, evaluate v g r = 0) :
    evaluate v g (combine relations terms) = 0 := by
  induction terms with
  | nil => exact evaluate_zero v g
  | cons t ts ih =>
    rw [combine, evaluate_add, evaluate_scale, ih]
    have hz : evaluate v g (relations[t.relation]?.getD zero) = 0 := by
      cases he : relations[t.relation]? with
      | none => exact evaluate_zero v g
      | some r => exact hr r (List.mem_of_getElem? he)
    rw [hz, smul_zero, add_zero]

variable [CharP R 2]

/-- Soundness in every module over every commutative characteristic-two ring.
Relations may connect different module generators; they are not assumed zero
componentwise. -/
theorem check_sound_evaluate (v : Nat → R) (g : Fin n → M)
    (relations : List (Expression n)) (input output : Expression n) (terms : List Term)
    (h : check relations input output terms = true)
    (hr : ∀ r ∈ relations, evaluate v g r = 0) : evaluate v g input = evaluate v g output := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  have hc (i : Fin n) : NamedElementCertificates.evaluate v (input i ++ output i) =
      NamedElementCertificates.evaluate v (combine relations terms i) := by
    apply NamedElementCertificates.check_sound_evaluate v [] _ _ [] (h.2 i)
    simp
  have he : evaluate v g (add input output) = evaluate v g (combine relations terms) := by
    unfold evaluate
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun z : R => z • g i) (hc i))
  rw [evaluate_add, evaluate_combine v g relations terms hr] at he
  have hz (x : M) : x + x = 0 := by
    have ht : (1 : R) + 1 = 0 := CharTwo.add_self_eq_zero 1
    have hh := congrArg (fun a : R => a • x) ht
    simpa only [add_smul, one_smul, zero_smul] using hh
  have ht := congrArg (fun x => x + evaluate v g output) he
  simpa only [add_assoc, hz, add_zero, zero_add] using ht

def EvaluationsAgree (v : Nat → R) (g : Fin n → M)
    (relations : List (Expression n)) (input output : Expression n) : Prop :=
  (∀ r ∈ relations, evaluate v g r = 0) → evaluate v g input = evaluate v g output

instance (v : Nat → R) (g : Fin n → M) (relations : List (Expression n))
    (input output : Expression n) :
    LinProgramCertificates.CertificateVerifier (EvaluationsAgree v g relations input output) where
  Cert := List Term
  check := check relations input output
  sound := fun terms h hr => check_sound_evaluate v g relations input output terms h hr

open Lean Elab Tactic
syntax "module_cert" " using " term : tactic
elab_rules : tactic
  | `(tactic| module_cert using $c:term) => do
    evalTactic (← `(tactic|
      exact LinProgramCertificates.CertificateVerifier.sound $c (by
        change ModuleExpressions.check _ _ _ _ = true
        decide)))

end NamedElementCertificates.ModuleExpressions
