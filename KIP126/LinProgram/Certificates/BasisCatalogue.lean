module

public import KIP126.LinProgram.Model.BasisCatalogue.Data
public import KIP126.LinProgram.Certificates.SquareDetection.Certificate

@[expose] public section

/-! Certify success and row membership for the original strict CSV parser.
These facts do not assert linear independence, spanning, or sphere comparison. -/
namespace KIP126.LinE2.BasisCatalogue
open SquareDetection

def rowValid : List Char → Bool
  | cs => match cs.splitOn '|' with
    | [s,t,i,_] => (charsToNat? s).isSome && (charsToNat? t).isSome && (charsToNat? i).isSome
    | _ => false

def chunkValid (cs : List Char) : Bool := (cs.splitOn '\n').all rowValid

theorem splitOn_pipe (s : String) :
    s.splitOn "|" = (s.toList.splitOn '|').map String.ofList :=
  splitOn_singleton_eq_list s '|'

theorem decode_success (line : String) (h : rowValid line.toList = true) :
    ∃ row, decodeBasisRow line = .ok row := by
  dsimp only [rowValid] at h
  unfold decodeBasisRow
  rw [splitOn_pipe]
  generalize hp : line.toList.splitOn '|' = parts at ⊢
  rw [hp] at h
  rcases parts with _ | ⟨s, _ | ⟨t, _ | ⟨i, _ | ⟨code, _ | ⟨a, as⟩⟩⟩⟩⟩
  all_goals simp only [List.map_cons, List.map_nil] at *
  all_goals try { simp at h }
  change ((charsToNat? s).isSome && (charsToNat? t).isSome &&
    (charsToNat? i).isSome) = true at h
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨s', hs⟩, ⟨t', ht⟩⟩, ⟨i', hi⟩⟩ := h
  refine ⟨⟨s',t',i',String.ofList code⟩, ?_⟩
  simp only [toNat?_eq_chars, String.toList_ofList, hs, ht, hi]
  rfl

def chunksValid (chunks : List String) : Bool := chunks.all (fun s => chunkValid s.toList)

theorem chunkValid_append (a b : List Char)
    (ha : chunkValid a = true) (hb : chunkValid b = true) :
    chunkValid (a ++ '\n' :: b) = true := by
  simp only [chunkValid, List.splitOn_append_cons_self, List.all_append,
    show (a.splitOn '\n').all rowValid = true from ha,
    show (b.splitOn '\n').all rowValid = true from hb, Bool.and_self]

theorem chunkValid_ofList (cs : List Char) (h : chunkValid cs = true) :
    chunkValid (String.ofList cs).toList = true := by rwa [String.toList_ofList]

theorem chunksValid_nil : chunksValid [] = true := rfl

theorem chunksValid_cons (s : String) (ss : List String)
    (hs : chunkValid s.toList = true) (hss : chunksValid ss = true) :
    chunksValid (s :: ss) = true := by
  simp only [chunksValid, List.all_cons] at *
  simp only [hs, hss, Bool.and_self]

theorem chunksValid_append (a b : List String)
    (ha : chunksValid a = true) (hb : chunksValid b = true) :
    chunksValid (a ++ b) = true := by
  simp only [chunksValid, List.all_append] at *
  simp only [ha, hb, Bool.and_self]

theorem decode_list_members (lines : List String)
    (h : ∀ line ∈ lines, ∃ row, decodeBasisRow line = .ok row) :
    ∃ rows, lines.mapM decodeBasisRow = .ok rows ∧
      ∀ line ∈ lines, ∀ row, decodeBasisRow line = .ok row → row ∈ rows := by
  induction lines with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons line lines ih =>
    obtain ⟨row, hr⟩ := h line (by simp)
    obtain ⟨rows, hrs, hmem⟩ := ih (fun line hl => h line (by simp [hl]))
    refine ⟨row :: rows, by simp only [List.mapM_cons, hr, hrs]; rfl, ?_⟩
    intro line' hl row' hr'
    rcases List.mem_cons.mp hl with rfl | hl
    · have heq : row = row' := Except.ok.inj (hr.symm.trans hr')
      simp [heq]
    · exact List.mem_cons_of_mem row (hmem line' hl row' hr')

theorem rawLine_decode_success (h : chunksValid RawData.basisChunks.toList = true)
    (line : String) (hl : line ∈ RawData.basisChunks.toList.flatMap (·.splitOn "\n")) :
    ∃ row, decodeBasisRow line = .ok row := by
  obtain ⟨chunk, hc, hl⟩ := List.mem_flatMap.mp hl
  have hv : chunkValid chunk.toList = true := List.all_eq_true.mp h chunk hc
  rw [SquareDetection.splitOn_newline] at hl
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hl
  apply decode_success
  rw [String.toList_ofList]
  exact List.all_eq_true.mp hv cs hcs

theorem row_mem_of_rawLine (h : chunksValid RawData.basisChunks.toList = true)
    (line : String) (hl : line ∈ RawData.basisChunks.toList.flatMap (·.splitOn "\n"))
    (row : BasisRow) (hr : decodeBasisRow line = .ok row) : row ∈ basisRows := by
  obtain ⟨rows, hp, hm⟩ := decode_list_members _ (rawLine_decode_success h)
  have heq : basisRows = rows := by
    unfold basisRows parseBasisRows
    rw [hp]
    rfl
  rw [heq]
  exact hm line hl row hr

theorem rawLine_mem_of_chars (i : ℕ) (hi : i < RawData.basisChunks.size)
    (cs : List Char) (h : cs ∈ RawData.basisChunks[i].toList.splitOn '\n') :
    String.ofList cs ∈ RawData.basisChunks.toList.flatMap (·.splitOn "\n") := by
  apply List.mem_flatMap.mpr
  refine ⟨RawData.basisChunks[i], Array.getElem_mem_toList hi, ?_⟩
  rw [SquareDetection.splitOn_newline]
  exact List.mem_map_of_mem h

theorem rawLine_mem_of_join (i : ℕ) (hi : i < RawData.basisChunks.size)
    (a cs b : List Char)
    (hc : RawData.basisChunks[i] = String.ofList (a ++ '\n' :: (cs ++ '\n' :: b)))
    (hcs : '\n' ∉ cs) :
    String.ofList cs ∈ RawData.basisChunks.toList.flatMap (·.splitOn "\n") := by
  apply rawLine_mem_of_chars i hi cs
  rw [hc, String.toList_ofList, List.splitOn_append_cons_self,
    List.splitOn_append_cons_self, List.splitOn_eq_singleton hcs]
  simp

end KIP126.LinE2.BasisCatalogue
