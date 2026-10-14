module

public import KIP126.LinProgram.Model.ModulePresentation.Data

@[expose] public section


namespace KIP126.LinModule.Presentation

/-- Every relation of the complete archived presentation vanishes in its quotient. -/
theorem native_relation_zero (n : Nat) (relations : List String) (code : String)
    (h : code ∈ relations) : projection n relations (relationVector n code) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (definingSubmodule n relations)).2
  exact Submodule.subset_span ⟨code, h, rfl⟩

/-- Parsing commutes with the actual module quotient map, for every native word. -/
theorem projection_ofPowers (n : Nat) (relations : List String) (word : List Nat) :
    projection n relations (ofPowers n word) =
      evaluatePowers (generator n relations) word := by
  induction word using ofPowers.induct n with
  | case1 j hj => simp only [ofPowers, evaluatePowers, dif_pos hj, generator]
  | case2 j hj => simp only [ofPowers, evaluatePowers, dif_neg hj, map_zero]
  | case3 i a rest hi ih =>
    simp only [ofPowers, evaluatePowers, dif_pos hi, map_smul, ih]
  | case4 i a rest hi =>
    simp only [ofPowers, evaluatePowers, dif_neg hi, map_zero]
  | case5 => simp only [ofPowers, evaluatePowers, map_zero]

/-- Chunking preserves every original relation; the local row certificate can
be checked without unfolding the entire archived table. -/
theorem relation_mem_of_chunk (chunks : Array (List String)) (i : Nat)
    (hi : i < chunks.size) (code : String) (h : code ∈ chunks[i]) :
    code ∈ chunks.toList.flatten :=
  List.mem_flatten.mpr ⟨chunks[i], Array.getElem_mem_toList hi, h⟩

end KIP126.LinModule.Presentation
