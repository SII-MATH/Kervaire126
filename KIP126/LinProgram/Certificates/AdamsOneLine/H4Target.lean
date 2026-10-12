module

public import KIP126.LinProgram.Certificates.AdamsOneLine.H4Source
public import Mathlib.Algebra.Order.Monoid.Prod

@[expose] public section


/-!
# LinProgram/Certificates/AdamsOneLine/H4Target

Fixed-data certificate in the original complete quotient or module; it supplies no actual-spectrum comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Degree exhaustion for the first nonzero one-line differential target.
This checks all generator degrees in the fixed quotient, and proves its
degree-(3,17) component has at most two elements without treating the CSV
catalogue as a basis or assuming any differential is correct. -/

namespace KIP126.LinE2.OneLine

open KIP126.Core.Algebra

local instance : NeZero RawData.generatorCount := ⟨by decide⟩

set_option maxHeartbeats 2000000

/-- Only these six archived generators can occur in degree (3,17). -/
theorem h0h3SqDegree_support (m : Generator →₀ ℕ)
    (hm : monomialDegree m = (3, 17)) :
    m.support ⊆ ({0, 1, 2, 3, 4, 7} : Finset Generator) := by
  intro i hi
  have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hle : (m i * (generatorDegree i).1, m i * (generatorDegree i).2) ≤
      monomialDegree m := by
    simpa [monomialDegree] using Finsupp.single_le_sum m
      (g := fun j a => (a * (generatorDegree j).1, a * (generatorDegree j).2))
      (by intro j a; exact ⟨Nat.zero_le _, Nat.zero_le _⟩) i
  rw [hm] at hle
  have hs : (generatorDegree i).1 ≤ 3 := by
    calc
      _ = 1 * (generatorDegree i).1 := (one_mul _).symm
      _ ≤ m i * (generatorDegree i).1 := Nat.mul_le_mul_right _ hmi
      _ ≤ 3 := hle.1
  have ht : (generatorDegree i).2 ≤ 17 := by
    calc
      _ = 1 * (generatorDegree i).2 := (one_mul _).symm
      _ ≤ m i * (generatorDegree i).2 := Nat.mul_le_mul_right _ hmi
      _ ≤ 17 := hle.2
  rw [generatorDegree_eq_row] at hs ht
  have h : ∀ j : Fin RawData.generatorCount,
      (RawData.generatorRow j.val).2.1 ≤ 3 →
      (RawData.generatorRow j.val).2.2 ≤ 17 → j.val ∈ [0, 1, 2, 3, 4, 7] := by
    decide +kernel
  simpa [Fin.ext_iff, RawData.generatorCount] using h i hs ht

/-- The only polynomial monomial in this degree is h₀h₃². -/
theorem monomialDegree_h0h3Sq_unique (m : Generator →₀ ℕ)
    (hm : monomialDegree m = (3, 17)) :
    m = Finsupp.single (0 : Generator) 1 + Finsupp.single (3 : Generator) 2 := by
  have hsupp := h0h3SqDegree_support m hm
  have hdegree : monomialDegree m =
      (m 0 + m 1 + m 2 + m 3 + 3 * m 4 + m 7,
        m 0 + 2 * m 1 + 4 * m 2 + 8 * m 3 + 11 * m 4 + 16 * m 7) := by
    unfold monomialDegree
    rw [m.sum_of_support_subset hsupp _ (by intros; simp)]
    simp [generatorDegree_eq_row, RawData.generatorRow, RawData.generatorChunkIndex,
      RawData.generatorChunk0, RawData.generatorCount, Nat.mul_comm, Nat.add_assoc]
  have hs := congrArg Prod.fst (hdegree.symm.trans hm)
  have ht := congrArg Prod.snd (hdegree.symm.trans hm)
  dsimp at hs ht
  have hvalues : m 0 = 1 ∧ m 1 = 0 ∧ m 2 = 0 ∧ m 3 = 2 ∧ m 4 = 0 ∧ m 7 = 0 := by
    omega
  ext i
  by_cases hi : i ∈ m.support
  · have hi' := hsupp hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · have hz := Finsupp.notMem_support_iff.mp hi
    have hi0 : i ≠ (0 : Generator) := by
      intro he
      subst i
      omega
    have hi3 : i ≠ (3 : Generator) := by
      intro he
      subst i
      omega
    simp [hz, Finsupp.single_eq_of_ne hi0, Finsupp.single_eq_of_ne hi3]

private theorem target_monomial :
    MvPolynomial.monomial
      (Finsupp.single (0 : Generator) 1 + Finsupp.single (3 : Generator) 2) (1 : F2) =
      MvPolynomial.X (0 : Generator) * MvPolynomial.X (3 : Generator) ^ 2 := by
  rw [MvPolynomial.X_pow_eq_monomial]
  simp [MvPolynomial.X]

/-- The degree component is spanned by the exact target data element. -/
theorem homogeneousPart_h0h3Sq_eq_span : homogeneousPart 3 17 =
    Submodule.span F2 ({dataH0H3Sq.val} : Set E2) := by
  unfold homogeneousPart
  apply congrArg (Submodule.span F2)
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [monomialDegree_h0h3Sq_unique m hm, target_monomial]
    rw [dataH0H3Sq_val]
    simp only [map_mul, map_pow]
    rfl
  · intro hx
    have hx' : x = dataH0H3Sq.val := hx
    subst x
    refine ⟨Finsupp.single (0 : Generator) 1 + Finsupp.single (3 : Generator) 2, ?_, ?_⟩
    · rw [monomialDegree_add]
      have h0deg : generatorDegree (0 : Generator) = (1, 1) := by
        simp [generatorDegree_eq_row, RawData.generatorRow, RawData.generatorChunkIndex,
          RawData.generatorChunk0, RawData.generatorCount]
      simp [monomialDegree, h0deg, h3Generator_degree]
    · rw [dataH0H3Sq_val, target_monomial]
      simp only [map_mul, map_pow]
      rfl

/-- There are at most two elements in the target component, independently
of archived basis correctness and of actual spectral-sequence differentials. -/
theorem E2At_h0h3Sq_eq_zero_or (x : E2At 3 17) : x = 0 ∨ x = dataH0H3Sq := E2At_eq_zero_or_of_span dataH0H3Sq homogeneousPart_h0h3Sq_eq_span x

end KIP126.LinE2.OneLine
