module

public import KIP126.LinProgram.Certificates.SquareDimension.Generators.Proofs
public import KIP126.LinProgram.Model.Classes.Proofs
public import Mathlib.Algebra.Order.Monoid.Prod

@[expose] public section


/-! Vanishing of the entire native stem-four component below filtration four.
The proof uses the full generator family and the original quotient relation;
it does not assume that the archived basis spans or is independent. -/
namespace KIP126.LinE2.StemFour
open KIP126.Core.Algebra
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
local instance : NeZero RawData.generatorCount := ⟨by decide⟩
attribute [local irreducible] homogeneousPart

/-- Exhaust the entire original generator family, using only its degrees. -/
theorem generator_internal_le_seven (i : Generator) (hi : (generatorDegree i).2 ≤ 7) :
    i.val ∈ [0, 1, 2] := by
  rw [generatorDegree_eq_row] at hi
  have h : ∀ j : Fin RawData.generatorCount,
      (RawData.generatorRow j.val).2.2 ≤ 7 → j.val ∈ [0, 1, 2] := by
    decide +kernel
  exact h i hi

theorem monomial_support (s : ℕ) (hs : s < 4) (m : Generator →₀ ℕ)
    (hm : monomialDegree m = (s, s + 4)) :
    m.support ⊆ ({0, 1, 2} : Finset Generator) := by
  intro i hi
  have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hle : (m i * (generatorDegree i).1, m i * (generatorDegree i).2) ≤
      monomialDegree m := by
    simpa [monomialDegree] using Finsupp.single_le_sum m
      (g := fun j a => (a * (generatorDegree j).1, a * (generatorDegree j).2))
      (by intro j a; exact ⟨Nat.zero_le _, Nat.zero_le _⟩) i
  rw [hm] at hle
  have ht : (generatorDegree i).2 ≤ 7 := by
    have hb : (generatorDegree i).2 ≤ m i * (generatorDegree i).2 := by
      simpa using Nat.mul_le_mul_right (generatorDegree i).2 hmi
    have ht := hle.2
    omega
  simpa [Fin.ext_iff, RawData.generatorCount] using generator_internal_le_seven i ht

/-- There are no monomials for s=0,1. For s=2,3 the only monomial
contains h₁h₂, with h₀ exponent s-2. This classifies all Finsupp monomials. -/
theorem monomial_classification (s : ℕ) (hs : s < 4) (m : Generator →₀ ℕ)
    (hm : monomialDegree m = (s, s + 4)) :
    2 ≤ s ∧ m = Finsupp.single (0 : Generator) (s - 2) +
      Finsupp.single (1 : Generator) 1 + Finsupp.single (2 : Generator) 1 := by
  have hsupp := monomial_support s hs m hm
  have hdegree : monomialDegree m = (m 0 + m 1 + m 2, m 0 + 2 * m 1 + 4 * m 2) := by
    unfold monomialDegree
    rw [m.sum_of_support_subset hsupp _ (by intros; simp)]
    simp [generatorDegree_eq_row, RawData.generatorRow, RawData.generatorChunkIndex,
      RawData.generatorChunk0, RawData.generatorCount, Nat.mul_comm, Nat.add_assoc]
  have hds := congrArg Prod.fst (hdegree.symm.trans hm)
  have hdt := congrArg Prod.snd (hdegree.symm.trans hm)
  dsimp at hds hdt
  have hv : 2 ≤ s ∧ m 0 = s - 2 ∧ m 1 = 1 ∧ m 2 = 1 := by omega
  obtain ⟨hs2, h0, h1, h2⟩ := hv
  refine ⟨hs2, ?_⟩
  ext i
  by_cases hi0 : i = 0
  · subst i
    simp only [Finsupp.add_apply, Finsupp.single_apply, h0]
    norm_num [Fin.ext_iff, RawData.generatorCount]
  by_cases hi1 : i = 1
  · subst i
    simp only [Finsupp.add_apply, Finsupp.single_apply, h1]
    norm_num [Fin.ext_iff, RawData.generatorCount]
  by_cases hi2 : i = 2
  · subst i
    simp only [Finsupp.add_apply, Finsupp.single_apply, h2]
    norm_num [Fin.ext_iff, RawData.generatorCount]
  have hn : i ∉ m.support := by
    intro hi
    have := hsupp hi
    simp [hi0, hi1, hi2] at this
  simp [Finsupp.notMem_support_iff.mp hn, Finsupp.single_eq_of_ne hi0,
    Finsupp.single_eq_of_ne hi1, Finsupp.single_eq_of_ne hi2]

/-- Every monomial in the whole component is zero in the original quotient. -/
theorem monomial_projection_zero (s : ℕ) (hs : s < 4) (m : Generator →₀ ℕ)
    (hm : monomialDegree m = (s, s + 4)) :
    projection (MvPolynomial.monomial m (1 : F2)) = 0 := by
  rw [(monomial_classification s hs m hm).2]
  rw [MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    ← MvPolynomial.X_pow_eq_monomial]
  simp only [pow_one, map_mul, map_pow]
  change (generator (0 : Generator) ^ (s - 2) * h1) * h2 = 0
  rw [mul_assoc, h1_mul_h2_eq_zero, mul_zero]

/-- This is the defining homogeneous submodule, not the archived basis span. -/
theorem homogeneousPart_eq_bot (s : ℕ) (hs : s < 4) :
    homogeneousPart s (s + 4) = ⊥ := by
  apply le_antisymm _ bot_le
  unfold homogeneousPart
  apply Submodule.span_le.mpr
  rintro x ⟨m, hm, rfl⟩
  exact (Submodule.mem_bot F2).mpr (monomial_projection_zero s hs m hm)

theorem component_subsingleton (s : ℕ) (hs : s < 4) :
    Subsingleton (E2At s (s + 4)) := by
  have hz (x : E2At s (s + 4)) : (x : E2) = 0 := by
    have hx : (x : E2) ∈ (⊥ : Submodule F2 E2) :=
      (le_of_eq (homogeneousPart_eq_bot s hs)) x.property
    exact (Submodule.mem_bot F2).mp hx
  exact ⟨fun x y => Subtype.ext ((hz x).trans (hz y).symm)⟩

end KIP126.LinE2.StemFour
