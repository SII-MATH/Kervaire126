module

public import KIP126.LinProgram.Generated.E2
public import KIP126.LinProgram.Certificates.SquareDetection.Parsing

@[expose] public section


/-! Exact archived relation membership. Runtime selection is only a proposal;
the kernel checks a newline decomposition of the original archived string. -/
namespace KIP126.LinE2.RelationCatalogue

theorem rawLine_mem_of_chars (i : Nat) (hi : i < RawData.relationChunks.size)
    (cs : List Char) (h : cs ∈ RawData.relationChunks[i].toList.splitOn '\n') :
    String.ofList cs ∈ RawData.relations := by
  apply List.mem_append_right RawData.firstRelations
  apply List.mem_flatMap.mpr
  refine ⟨RawData.relationChunks[i], Array.getElem_mem_toList hi, ?_⟩
  rw [SquareDetection.splitOn_newline]
  exact List.mem_map_of_mem h

theorem rawLine_mem_of_join (i : Nat) (hi : i < RawData.relationChunks.size)
    (a cs b : List Char)
    (hc : RawData.relationChunks[i] = String.ofList (a ++ '\n' :: (cs ++ '\n' :: b)))
    (hcs : '\n' ∉ cs) :
    String.ofList cs ∈ RawData.relations := by
  apply rawLine_mem_of_chars i hi cs
  rw [hc, String.toList_ofList, List.splitOn_append_cons_self,
    List.splitOn_append_cons_self, List.splitOn_eq_singleton hcs]
  simp

end KIP126.LinE2.RelationCatalogue
