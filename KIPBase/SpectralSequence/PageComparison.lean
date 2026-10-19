import KIPBase.SpectralSequence.Basic

/-!
# Abstract page comparison

The two spectral sequences in a comparison need not use the same expression
for their differential degree.  This file transports both differentials to a
common degree and proves the successor-page comparison directly from
`E_{r+1} ≅ H(E_r, d_r)`.
-/

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A comparison of the page-`r` differential complexes at two possibly
different grading indices induces the comparison on page `r+1`.

This is the grading-independent induction step used for the affine
`λ`-Bockstein-to-synthetic-Adams reindexing. -/
noncomputable def SpectralSequence.pageIsoSuccOfComplexIso
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {ι' : Type*} [AddCommGroup ι'] [DecidableEq ι']
    (E : SpectralSequence C ι) (E' : SpectralSequence C ι')
    (r : ℤ) (hr : E.r₀ ≤ r) (hr' : E'.r₀ ≤ r)
    (k : ι) (k' : ι')
    (e : E.pageShortComplex r (k - E.diffDeg r) ≅
      E'.pageShortComplex r (k' - E'.diffDeg r)) :
    E.Page (r + 1) k ≅ E'.Page (r + 1) k' :=
  E.pageHomologyIso r k hr ≪≫
    ShortComplex.homologyMapIso e ≪≫
    (E'.pageHomologyIso r k' hr').symm

/-- The page-`r` differential, transported to a specified common degree. -/
noncomputable def SpectralSequence.pageDiffAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (d : ι)
    (hd : E.diffDeg r = d) (k : ι) :
    E.Page r k ⟶ E.Page r (k + d) :=
  E.d r k ≫ eqToHom (congrArg (fun j => E.Page r j)
    (congrArg (fun x => k + x) hd))

/-- Transporting the differential degree preserves the equation `d² = 0`. -/
theorem SpectralSequence.pageDiffAt_comp
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (d : ι)
    (hd : E.diffDeg r = d) (k : ι) :
    E.pageDiffAt r d hd k ≫ E.pageDiffAt r d hd (k + d) = 0 := by
  subst d
  simpa [SpectralSequence.pageDiffAt] using E.d_comp_d r k

/-- The three-term page complex formed using a specified common differential
degree.  This removes irrelevant transports from page-comparison arguments. -/
noncomputable def SpectralSequence.pageShortComplexAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (d : ι)
    (hd : E.diffDeg r = d) (k : ι) : ShortComplex C :=
  ShortComplex.mk (E.pageDiffAt r d hd k)
    (E.pageDiffAt r d hd (k + d)) (E.pageDiffAt_comp r d hd k)

/-- The normalized page complex agrees with the ordinary page complex. -/
noncomputable def SpectralSequence.pageShortComplexAtIso
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (d : ι)
    (hd : E.diffDeg r = d) (k : ι) :
    E.pageShortComplexAt r d hd k ≅ E.pageShortComplex r k := by
  subst d
  apply eqToIso
  congr 1 <;>
    simp [SpectralSequence.pageShortComplexAt,
      SpectralSequence.pageDiffAt, SpectralSequence.pageShortComplex]

/-- If page-`r` isomorphisms commute with `d_r`, they induce page-`r+1`
isomorphisms.  The proof only uses `E_{r+1} ≅ H(E_r,d_r)`. -/
noncomputable def SpectralSequence.pageIsoSucc
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E E' : SpectralSequence C ι) (r : ℤ)
    (hr : E.r₀ ≤ r) (hr' : E'.r₀ ≤ r)
    (d : ι) (hdeg : E.diffDeg r = d) (hdeg' : E'.diffDeg r = d)
    (e : ∀ k : ι, E.Page r k ≅ E'.Page r k)
    (hcomm : ∀ k : ι,
      (e k).hom ≫ E'.pageDiffAt r d hdeg' k =
        E.pageDiffAt r d hdeg k ≫ (e (k + d)).hom)
    (k : ι) : E.Page (r + 1) k ≅ E'.Page (r + 1) k := by
  let c := k - d
  let S := E.pageShortComplexAt r d hdeg c
  let T := E'.pageShortComplexAt r d hdeg' c
  let φ : S ⟶ T := ShortComplex.homMk
    (e c).hom (e (c + d)).hom (e (c + d + d)).hom
    (hcomm c) (hcomm (c + d))
  haveI : IsIso φ.τ₁ := by
    change IsIso (e c).hom
    infer_instance
  haveI : IsIso φ.τ₂ := by
    change IsIso (e (c + d)).hom
    infer_instance
  haveI : IsIso φ.τ₃ := by
    change IsIso (e (c + d + d)).hom
    infer_instance
  haveI : IsIso φ := by
    apply ShortComplex.isIso_of_isIso φ
  let hIso : S.homology ≅ T.homology :=
    ShortComplex.homologyMapIso (asIso φ)
  let sourcePageIso : E.Page (r + 1) k ≅
      (E.pageShortComplex r c).homology := by
    simpa [c, hdeg] using E.pageHomologyIso r k hr
  let sourceIso : E.Page (r + 1) k ≅ S.homology :=
    sourcePageIso ≪≫ ShortComplex.homologyMapIso
      (E.pageShortComplexAtIso r d hdeg c).symm
  let targetPageIso : E'.Page (r + 1) k ≅
      (E'.pageShortComplex r c).homology := by
    simpa [c, hdeg'] using E'.pageHomologyIso r k hr'
  let targetIso : E'.Page (r + 1) k ≅ T.homology :=
    targetPageIso ≪≫ ShortComplex.homologyMapIso
      (E'.pageShortComplexAtIso r d hdeg' c).symm
  exact sourceIso ≪≫ hIso ≪≫ targetIso.symm

end KIPBase.SpectralSequence
