import KIP126.LinProgram.Certificates.Milnor.WindowSoundness
import KIP126.LinProgram.Certificates.Milnor.Import
import KIP126.LinProgram.Tactic.LinCert

namespace MilnorCertificates

/-- Equality on every dual monomial of the declared rank, without a degree cutoff. -/
def IsMilnorProductAll (rank : Nat) (left right output : Polynomial) : Prop :=
  (∀ m ∈ left, m.length = rank) ∧
  (∀ m ∈ right, m.length = rank) ∧
  (∀ m ∈ output, m.length = rank) ∧
  ∀ m, m.length = rank →
    coefficient output m = pairTensor left right (coproduct rank m)

structure AllCertificate where
  finite : Certificate
  leftDegree : Nat
  rightDegree : Nat
  deriving Repr, Lean.ToJson, Lean.FromJson

def checkAll (rank : Nat) (left right output : Polynomial) (c : AllCertificate) : Bool :=
  decide (c.finite.window.rank = rank) &&
  left.all (fun m => decide (weight m = c.leftDegree)) &&
  right.all (fun m => decide (weight m = c.rightDegree)) &&
  decide (c.leftDegree + c.rightDegree ≤ c.finite.window.degree) &&
  check c.finite.window left right output c.finite

theorem checkAll_sound (rank : Nat) (left right output : Polynomial) (c : AllCertificate)
    (h : checkAll rank left right output c = true) :
    IsMilnorProductAll rank left right output := by
  simp only [checkAll, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨hrank, hl⟩, hr⟩, hb⟩, hc⟩
  have hs := check_sound _ _ _ _ _ hc
  have lengths (p : Polynomial) (hp : polynomialInWindow c.finite.window.rank
      c.finite.window.degree p = true) : ∀ m ∈ p, m.length = rank := by
    intro m hm
    have hh := List.all_eq_true.mp hp m hm
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
    exact hh.1.trans hrank
  refine ⟨lengths left hs.1, lengths right hs.2.1, lengths output hs.2.2.1, ?_⟩
  intro m hm
  have hh := check_all_monomials c.finite.window left right output c.finite
    c.leftDegree c.rightDegree
    (fun a ha => of_decide_eq_true (List.all_eq_true.mp hl a ha))
    (fun a ha => of_decide_eq_true (List.all_eq_true.mp hr a ha)) hb hc m
    (hm.trans hrank.symm)
  simpa only [hrank] using hh

instance (rank : Nat) (left right output : Polynomial) :
    LinProgramCertificates.CertificateVerifier (IsMilnorProductAll rank left right output) where
  Cert := AllCertificate
  check := checkAll rank left right output
  sound := checkAll_sound rank left right output

def diagnoseAll (rank : Nat) (left right output : Polynomial) (c : AllCertificate) :
    List String :=
  (if c.finite.window.rank != rank then ["rank does not match goal"] else []) ++
  (if !left.all (fun m => decide (weight m = c.leftDegree)) then
    ["left input is not homogeneous in the certified degree"] else []) ++
  (if !right.all (fun m => decide (weight m = c.rightDegree)) then
    ["right input is not homogeneous in the certified degree"] else []) ++
  (if c.leftDegree + c.rightDegree > c.finite.window.degree then
    ["window does not cover the sum of input degrees"] else []) ++
  diagnose c.finite.window left right output c.finite

/-- Reuse the strict C++ bundle importer; homogeneity is checked by checkAll. -/
def Bundle.allCertificate (b : Bundle) (leftDegree rightDegree : Nat) : AllCertificate :=
  ⟨b.certificate, leftDegree, rightDegree⟩

/-- Degree inference proposes data only; the checker checks every input term. -/
def Bundle.inferAllCertificate (b : Bundle) : AllCertificate :=
  b.allCertificate (weight (b.left.headD [])) (weight (b.right.headD []))

open Lean Elab Tactic
syntax "milnor_cert_all" " using " term : tactic
elab_rules : tactic
  | `(tactic| milnor_cert_all using $c:term) => do
      evalTactic (← `(tactic| exact checkAll_sound _ _ _ _ $c (by decide)))

example : IsMilnorProductAll 2 [[1, 0]] [[1, 0]] [] := by
  milnor_cert_all using (⟨generate ⟨2, 2⟩, 1, 1⟩ : AllCertificate)

example : IsMilnorProductAll 2 [[2, 0]] [[1, 0]] [[3, 0], [0, 1]] := by
  lin_cert using (⟨generate ⟨2, 3⟩, 2, 1⟩ : AllCertificate)

-- An insufficient window is rejected even when its finite checks pass.
example : checkAll 1 [[2]] [[2]] [] ⟨generate ⟨1, 2⟩, 2, 2⟩ = false := by decide
example : checkAll 2 [[1, 0]] [[1, 0]] [] ⟨generate ⟨2, 2⟩, 0, 1⟩ = false := by decide

end MilnorCertificates
