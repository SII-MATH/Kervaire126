import KIP126.LinProgram.Interpretation.Expression.Data
import KIP126.LinProgram.Model.E2.Proofs

set_option maxRecDepth 16384

namespace KIP126.LinE2

-- Keep symbolic degree indices opaque during dependent pattern elaboration.
attribute [local irreducible] generatorDegree definingIdeal

/-- 传给原计算器的表达式与商环解释一致。 -/
theorem Expression.data_eq_interpret {s t : ℕ} (e : Expression s t) :
    e.data = Automation.interpret e.code := by
  induction e with
  | zero => rfl
  | one => rfl
  | gen i =>
    change generator i = (if h : i.val < RawData.generatorCount then generator ⟨i.val, h⟩ else 0)
    rw [dif_pos i.isLt]
  | add a b ha hb => exact congrArg₂ (· + ·) ha hb
  | mul a b ha hb => exact congrArg₂ (· * ·) ha hb

/-- Homogeneity is proved from the quotient operations, independently of
CSV basis correctness and the executable reduction algorithm. -/
theorem Expression.homogeneous {s t : ℕ} (e : Expression s t) :
    e.data ∈ homogeneousPart s t := by
  induction e with
  | zero => exact Submodule.zero_mem _
  | one =>
    apply Submodule.subset_span
    refine ⟨0, ?_, ?_⟩
    · simp only [monomialDegree, Finsupp.sum_zero_index]; rfl
    · change (1 : E2) = projection (MvPolynomial.monomial 0 1)
      rw [← MvPolynomial.C_apply, map_one, map_one]
  | gen i => exact generator_mem i
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | mul a b ha hb => exact multiply_mem ha hb

/-- Transporting the degree annotation does not change the quotient value. -/
theorem Expression.data_cast {d d' : ℕ × ℕ} (h : d = d')
    (e : Expression d.1 d.2) :
    (cast (congrArg (fun b : ℕ × ℕ => Expression b.1 b.2) h) e).data = e.data := by
  cases h
  rfl

end KIP126.LinE2
