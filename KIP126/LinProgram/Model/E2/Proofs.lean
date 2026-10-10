import KIP126.LinProgram.Model.E2.Data

namespace KIP126.LinE2

theorem monomialDegree_add (m n : Generator →₀ ℕ) :
    monomialDegree (m + n) = monomialDegree m + monomialDegree n := by
  unfold monomialDegree
  exact Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])

/-- Homogeneous multiplication is a property of the actual quotient algebra;
it does not depend on the CSV basis certification or the reduction algorithm. -/
theorem multiply_mem {s t s' t' : ℕ} {a b : E2}
    (ha : a ∈ homogeneousPart s t) (hb : b ∈ homogeneousPart s' t') :
    a * b ∈ homogeneousPart (s + s') (t + t') := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨m, hm, rfl⟩ := ha
      obtain ⟨n, hn, rfl⟩ := hb
      apply Submodule.subset_span
      refine ⟨m + n, ?_, ?_⟩
      · simpa [hm, hn] using monomialDegree_add m n
      · simp [← map_mul, MvPolynomial.monomial_mul]
    | zero => simp
    | add b c _ _ hb hc =>
      simpa [mul_add] using (homogeneousPart (s + s') (t + t')).add_mem hb hc
    | smul r b _ hb =>
      simpa [mul_smul_comm] using (homogeneousPart (s + s') (t + t')).smul_mem r hb
  | zero => simp
  | add a c _ _ ha hc =>
    simpa [add_mul] using (homogeneousPart (s + s') (t + t')).add_mem ha hc
  | smul r a _ ha =>
    simpa [smul_mul_assoc] using (homogeneousPart (s + s') (t + t')).smul_mem r ha

/-- Every archived relation holds by construction of the quotient. -/
theorem csv_relation_zero (code : String) (h : code ∈ RawData.relations) :
    projection (relationPolynomial code) = 0 := by
  apply (Ideal.Quotient.eq_zero_iff_mem).2
  exact Ideal.subset_span (Or.inl ⟨code, h, rfl⟩)

theorem h6Generator_degree : generatorDegree h6Generator = (1, 64) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk2, RawData.generatorCount, h6Generator,
    Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

theorem h0Generator_degree : generatorDegree ⟨0, by decide⟩ = (1, 1) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount,
    Array.getElem!_eq_getD]

theorem h1Generator_degree : generatorDegree ⟨1, by decide⟩ = (1, 2) := by
  simp [generatorDegree, RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount,
    Array.getElem!_eq_getD]

theorem h6Generator_name : (RawData.generators[h6Generator.val]!).1 = "h_6" := by
  simp [RawData.generators, RawData.generatorRow,
    RawData.generatorChunkIndex, RawData.generatorChunk2, RawData.generatorCount, h6Generator,
    Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

theorem generator_pow_mem (i : Generator) (n : ℕ) :
    generator i ^ n ∈ homogeneousPart
      (n * (generatorDegree i).1) (n * (generatorDegree i).2) := by
  apply Submodule.subset_span
  refine ⟨Finsupp.single i n, ?_, ?_⟩
  · simp [monomialDegree]
  · simp [generator, ← map_pow, MvPolynomial.X_pow_eq_monomial]

theorem generator_mem (i : Generator) :
    generator i ∈ homogeneousPart (generatorDegree i).1 (generatorDegree i).2 := by
  simpa using generator_pow_mem i 1

end KIP126.LinE2
