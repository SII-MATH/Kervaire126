module

public import KIP126.LinProgram.Certificates.Naturality.BatchMapCertificate
public import KIP126.LinProgram.Certificates.BasisCatalogue.Archive

public meta import KIP126.LinProgram.Generated.E2

@[expose] public section


/-! Shared kernel proofs for blocks of exact native word certificates. A block
contains its finite checked equations and the original target-row membership
proofs. Neither a block nor its union asserts actual Adams comparison. -/
namespace KIP126.LinModule.NaturalityWords200
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
open NaturalityMapCertificate (BasisRecord generatorImage)

/-- Delimiters protect a selected row even when unrelated rows contain newlines.
Only the selected row's lack of newline is needed for exact-line membership. -/
theorem selected_mem_joinRows (rows : List (List Char)) (row : List Char)
    (hr : row ∈ rows) (hn : '\n' ∉ row) :
    row ∈ (joinRows rows).splitOn '\n' := by
  induction rows using joinRows.induct with
  | case1 => simp at hr
  | case2 r =>
    have h : row = r := by simpa using hr
    subst r
    simp only [joinRows, List.splitOn_eq_singleton hn, List.mem_singleton]
  | case3 r s rows ih =>
    rw [joinRows, List.splitOn_append_cons_self]
    rcases List.mem_cons.mp hr with h | h
    · subst r
      simp only [List.splitOn_eq_singleton hn, List.singleton_append, List.mem_cons]
      exact Or.inl True.intro
    · exact List.mem_append_right _ (ih h)

theorem relation_member (i : Nat) (hi : i < LinE2.RawData.relationChunks.size)
    (rows : List (List Char))
    (hc : LinE2.RawData.relationChunks[i] = String.ofList (joinRows rows))
    (row : List Char) (hr : row ∈ rows) (hn : '\n' ∉ row) :
    String.ofList row ∈ LinE2.RawData.relations := by
  apply RelationCatalogue.rawLine_mem_of_chars i hi row
  rw [hc, String.toList_ofList]
  exact selected_mem_joinRows rows row hr hn

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

/-- A complete finite block of already proved native-data equations. -/
structure CertifiedBatch where
  relationCodes : List String
  entries : List Entry
  checks : entries.all (BatchMapCertificate.check relationCodes) = true
  relations_zero : ∀ code ∈ relationCodes, nativeImage code = 0
  targets_mem : ∀ e ∈ entries, ∀ r ∈ e.targets, basisRow r ∈ basisRows

theorem CertifiedBatch.entry_evaluate (b : CertifiedBatch) (e : Entry) (he : e ∈ b.entries) :
    Presentation.evaluatePowers generatorImage (word e) = targetValue e :=
  BatchMapCertificate.check_sound b.relationCodes e
    ((List.all_eq_true.mp b.checks) e he) b.relations_zero

/-- The true full Ceta quotient is used; none of its relations are omitted. -/
theorem CertifiedBatch.entry_desc (b : CertifiedBatch) (e : Entry) (he : e ∈ b.entries)
    (hrel : ∀ code ∈ RawData.Ceta.relations,
      Presentation.evaluateRelation generatorImage code = 0) :
    Presentation.desc generatorImage RawData.Ceta.relations hrel
      (Ceta.monomial e.source.code) = targetValue e :=
  BatchMapCertificate.check_sound_desc b.relationCodes e
    ((List.all_eq_true.mp b.checks) e he) b.relations_zero hrel

end KIP126.LinModule.NaturalityWords200
