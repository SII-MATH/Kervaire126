import KIP126.LinProgram.Certificates.Milnor.ExponentEncoding
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Algebra

namespace MilnorCertificates
open scoped BigOperators
abbrev UniversalRing := MvPolynomial (Fin 3 × Nat) (ZMod 2)

noncomputable instance : CharP UniversalRing 2 :=
  charP_of_injective_ringHom (MvPolynomial.C_injective (Fin 3 × Nat) (ZMod 2)) 2

noncomputable def universalVariable (slot : Fin 3) (j : Nat) : UniversalRing :=
  MvPolynomial.X (slot,j)

theorem universalMonomial (slot : Fin 3) (m : Monomial) :
    monomialValue (universalVariable slot) m =
      MvPolynomial.monomial (exponentEncoding slot m) (1 : ZMod 2) := by
  classical
  unfold monomialValue
  rw [← List.prod_toFinset _ List.nodup_range]
  have hr : (List.range m.length).toFinset = Finset.range m.length := by ext j; simp
  rw [hr]
  change (∏ j ∈ Finset.range m.length, universalVariable slot j ^ (m[j]?.getD 0)) = _
  unfold exponentEncoding
  generalize Finset.range m.length = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha,ih]
    simp only [universalVariable,MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_mul,one_mul]

theorem universalTriple (t : TripleMonomial) :
    monomialValue (universalVariable 0) t.1 * monomialValue (universalVariable 1) t.2.1 *
      monomialValue (universalVariable 2) t.2.2 =
      MvPolynomial.monomial (tripleEncoding t) (1 : ZMod 2) := by
  rw [universalMonomial,universalMonomial,universalMonomial]
  simp only [MvPolynomial.monomial_mul,one_mul,tripleEncoding]

theorem universalTriple_coefficient (p : List TripleMonomial) (t : TripleMonomial)
    (hp : ∀ u ∈ p, u.1.length = t.1.length ∧ u.2.1.length = t.2.1.length ∧
      u.2.2.length = t.2.2.length) :
    MvPolynomial.coeff (tripleEncoding t)
      (tripleValue (universalVariable 0) (universalVariable 1) (universalVariable 2) p) =
      ((p.filter (· == t)).length : ZMod 2) := by
  classical
  induction p with
  | nil => simp [tripleValue]
  | cons u p ih =>
    have hu := hp u (by simp)
    have hps : ∀ v ∈ p, v.1.length = t.1.length ∧ v.2.1.length = t.2.1.length ∧ v.2.2.length = t.2.2.length := fun v hv => hp v (by simp [hv])
    have he : tripleEncoding u = tripleEncoding t ↔ u = t :=
      ⟨tripleEncoding_injective u t hu.1 hu.2.1 hu.2.2,congrArg tripleEncoding⟩
    change MvPolynomial.coeff (tripleEncoding t)
      (monomialValue (universalVariable 0) u.1 * monomialValue (universalVariable 1) u.2.1 *
        monomialValue (universalVariable 2) u.2.2 +
        tripleValue (universalVariable 0) (universalVariable 1) (universalVariable 2) p) = _
    rw [MvPolynomial.coeff_add,universalTriple,MvPolynomial.coeff_monomial,ih hps]
    by_cases hut : u = t
    · simp [hut,add_comm]
    · simp [he,hut]

theorem coproductLeft_arity (rank : Nat) (m : Monomial) (hm : m.length = rank)
    (t : TripleMonomial) (ht : t ∈ coproductLeft rank m) :
    t.1.length = rank ∧ t.2.1.length = rank ∧ t.2.2.length = rank := by
  obtain ⟨u,hu,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
  have hu' := coproduct_homogeneous rank m hm u hu
  have hv' := coproduct_homogeneous rank u.1 hu'.1 v hv
  exact ⟨hv'.1,hv'.2.1,hu'.2.1⟩

theorem coproductRight_arity (rank : Nat) (m : Monomial) (hm : m.length = rank)
    (t : TripleMonomial) (ht : t ∈ coproductRight rank m) :
    t.1.length = rank ∧ t.2.1.length = rank ∧ t.2.2.length = rank := by
  obtain ⟨u,hu,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
  have hu' := coproduct_homogeneous rank m hm u hu
  have hv' := coproduct_homogeneous rank u.2 hu'.2.1 v hv
  exact ⟨hu'.1,hv'.1,hv'.2.1⟩

/-- Coassociativity for every rank and monomial, with equality of every
actual executable parity coefficient, including outside the finite support. -/
theorem coproduct_coassociative (rank : Nat) (m : Monomial) (hm : m.length = rank) :
    CoassociativeAt rank m := by
  intro t
  by_cases ht : t.1.length = rank ∧ t.2.1.length = rank ∧ t.2.2.length = rank
  · have hv := tripleValue_coassociative (universalVariable 0) (universalVariable 1)
      (universalVariable 2) rank m hm
    have hc := congrArg (MvPolynomial.coeff (tripleEncoding t)) hv
    rw [universalTriple_coefficient _ t (fun u hu => by
      have h := coproductLeft_arity rank m hm u hu
      exact ⟨h.1.trans ht.1.symm,h.2.1.trans ht.2.1.symm,h.2.2.trans ht.2.2.symm⟩),
      universalTriple_coefficient _ t (fun u hu => by
      have h := coproductRight_arity rank m hm u hu
      exact ⟨h.1.trans ht.1.symm,h.2.1.trans ht.2.1.symm,h.2.2.trans ht.2.2.symm⟩)] at hc
    have hmod := congrArg ZMod.val hc
    simp only [ZMod.val_natCast] at hmod
    unfold tripleCoefficient
    rw [hmod]
  · rw [tripleCoefficient_absent _ t (fun h => ht (coproductLeft_arity rank m hm t h)),
      tripleCoefficient_absent _ t (fun h => ht (coproductRight_arity rank m hm t h))]

#print axioms universalTriple_coefficient
#print axioms coproduct_coassociative
end MilnorCertificates
