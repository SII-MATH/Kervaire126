import KIP126.LinProgram.Certificates.Milnor.IteratedEvaluation
import Mathlib.Data.Finsupp.Basic

namespace MilnorCertificates
open scoped BigOperators

/-- Distinct first coordinates reserve independent polynomial variables for
all three tensor factors. -/
noncomputable def exponentEncoding (slot : Fin 3) (m : Monomial) : (Fin 3 × Nat) →₀ Nat :=
  ∑ j ∈ Finset.range m.length, Finsupp.single (slot,j) (m[j]?.getD 0)

theorem exponentEncoding_apply (slot : Fin 3) (m : Monomial) (j : Nat) :
    exponentEncoding slot m (slot,j) = m[j]?.getD 0 := by
  classical
  simp only [exponentEncoding,Finset.sum_apply',Finsupp.single_apply,Prod.mk.injEq,true_and]
  by_cases hj : j < m.length
  · simp [hj,eq_comm]

  · simp [hj]


theorem exponentEncoding_other (slot other : Fin 3) (m : Monomial) (j : Nat)
    (h : slot ≠ other) : exponentEncoding slot m (other,j) = 0 := by
  classical
  simp [exponentEncoding,Finset.sum_apply',Finsupp.single_apply,h]

noncomputable def tripleEncoding (t : TripleMonomial) : (Fin 3 × Nat) →₀ Nat :=
  exponentEncoding 0 t.1 + exponentEncoding 1 t.2.1 + exponentEncoding 2 t.2.2

theorem tripleEncoding_injective (a b : TripleMonomial)
    (h1 : a.1.length = b.1.length) (h2 : a.2.1.length = b.2.1.length)
    (h3 : a.2.2.length = b.2.2.length)
    (h : tripleEncoding a = tripleEncoding b) : a = b := by
  have hc (slot : Fin 3) (j : Nat) := congrArg (fun e : (Fin 3 × Nat) →₀ Nat => e (slot,j)) h
  have hfirst : a.1 = b.1 := by
    apply List.ext_getElem? 
    intro j
    have hh := hc 0 j
    simp only [tripleEncoding,Finsupp.add_apply,exponentEncoding_apply,
      exponentEncoding_other 1 0 _ _ (by decide),exponentEncoding_other 2 0 _ _ (by decide),add_zero] at hh
    by_cases hj : j < a.1.length
    · have hjb : j < b.1.length := by omega
      simpa [hj,hjb] using hh
    · have hjb : ¬ j < b.1.length := by omega
      simp [hj,hjb]
  have hsecond : a.2.1 = b.2.1 := by
    apply List.ext_getElem?
    intro j
    have hh := hc 1 j
    simp only [tripleEncoding,Finsupp.add_apply,exponentEncoding_apply,
      exponentEncoding_other 0 1 _ _ (by decide),exponentEncoding_other 2 1 _ _ (by decide),add_zero,zero_add] at hh
    by_cases hj : j < a.2.1.length
    · have hjb : j < b.2.1.length := by omega
      simpa [hj,hjb] using hh
    · have hjb : ¬ j < b.2.1.length := by omega
      simp [hj,hjb]
  have hthird : a.2.2 = b.2.2 := by
    apply List.ext_getElem?
    intro j
    have hh := hc 2 j
    simp only [tripleEncoding,Finsupp.add_apply,exponentEncoding_apply,
      exponentEncoding_other 0 2 _ _ (by decide),exponentEncoding_other 1 2 _ _ (by decide),zero_add] at hh
    by_cases hj : j < a.2.2.length
    · have hjb : j < b.2.2.length := by omega
      simpa [hj,hjb] using hh
    · have hjb : ¬ j < b.2.2.length := by omega
      simp [hj,hjb]
  exact Prod.ext hfirst (Prod.ext hsecond hthird)

#print axioms exponentEncoding_apply
#print axioms tripleEncoding_injective
end MilnorCertificates
