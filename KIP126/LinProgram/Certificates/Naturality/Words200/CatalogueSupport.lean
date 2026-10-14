module

public import KIP126.LinProgram.Certificates.Naturality.Words200.Support
public import KIP126.LinProgram.Certificates.BasisCatalogue.Archive

@[expose] public section


/-! Batch the strict row decoder while retaining exact archived-line membership. -/
namespace KIP126.LinModule.NaturalityWords200
open KIP126.LinE2 NativeMapCertificates

theorem basis_member (i : Nat) (hi : i < LinE2.RawData.basisChunks.size)
    (rows : List (List Char))
    (hc : LinE2.RawData.basisChunks[i] = String.ofList (joinRows rows))
    (row : List Char) (hr : row ∈ rows) (hn : '\n' ∉ row)
    (r : BasisRow) (hd : decodeBasisRow (String.ofList row) = .ok r) :
    r ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid _ ?_ r hd
  apply BasisCatalogue.rawLine_mem_of_chars i hi row
  rw [hc, String.toList_ofList]
  exact selected_mem_joinRows rows row hr hn

def basisBindingCheck (rows : Array (List Char)) (b : Nat × BasisRow) : Bool :=
  if h : b.1 < rows.size then
    !((rows[b.1]).contains '\n') && decide (decodeBasisRow (String.ofList rows[b.1]) = .ok b.2)
  else false

theorem basisBindingCheck_sound (i : Nat) (hi : i < LinE2.RawData.basisChunks.size)
    (rows : Array (List Char))
    (hc : LinE2.RawData.basisChunks[i] = String.ofList (joinRows rows.toList))
    (b : Nat × BasisRow) (hb : basisBindingCheck rows b = true) : b.2 ∈ basisRows := by
  unfold basisBindingCheck at hb
  split at hb
  next h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    have hn : '\n' ∉ rows[b.1] := by simpa using hb.1
    exact basis_member i hi rows.toList hc rows[b.1]
      (Array.getElem_mem_toList h) hn b.2 hb.2
  next => simp at hb

theorem basisBindings_mem (i : Nat) (hi : i < LinE2.RawData.basisChunks.size)
    (rows : Array (List Char))
    (hc : LinE2.RawData.basisChunks[i] = String.ofList (joinRows rows.toList))
    (bindings : List (Nat × BasisRow))
    (h : bindings.all (basisBindingCheck rows) = true)
    (b : Nat × BasisRow) (hb : b ∈ bindings) : b.2 ∈ basisRows :=
  basisBindingCheck_sound i hi rows hc b ((List.all_eq_true.mp h) b hb)

end KIP126.LinModule.NaturalityWords200
