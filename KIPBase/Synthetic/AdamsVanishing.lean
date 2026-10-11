import KIPBase.Synthetic.Adams

/-!+# Propagation of synthetic Adams vanishing

The support of the second page bounds which differentials can be nonzero.
The argument uses only the nested cycles and boundaries of the existing
spectral sequence, and imposes no boundedness condition on the filtration.
-/

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v

/-- Once a page at an index is zero, every later subquotient there is zero,
including the limiting subquotient. -/
theorem page_isZero_of_le {C : Type*} [Category C] [Abelian C]
    (D : SSData C) {i j : WithTop ℕ} (hij : i ≤ j)
    (hi : IsZero (D.page i)) : IsZero (D.page j) := by
  apply D.page_isZero_of_eq
  apply le_antisymm (D.B_le_Z j)
  calc
    D.Z j ≤ D.Z i := D.Z_anti hij
    _ = D.B i := (D.eq_of_page_isZero i hi).symm
    _ ≤ D.B j := D.B_mono hij

/-- Surjectivity after quotienting by a subgroup already contained in the
source implies surjectivity of the original inclusion. -/
private theorem subobject_eq_of_quotient_epi
    {C : Type*} [Category C] [Abelian C] {V : C}
    (B P Q : Subobject V) (hBP : B ≤ P) (hPQ : P ≤ Q)
    [Epi (Subobject.ofLE P Q hPQ ≫
      cokernel.π (Subobject.ofLE B Q (hBP.trans hPQ)))] : P = Q := by
  let i := Subobject.ofLE P Q hPQ
  let b := Subobject.ofLE B Q (hBP.trans hPQ)
  have hi : Epi i := by
    apply (Preadditive.epi_iff_cancel_zero i).mpr
    intro R g hg
    have hbg : b ≫ g = 0 := by
      change Subobject.ofLE B Q _ ≫ g = 0
      rw [← Subobject.ofLE_comp_ofLE B P Q hBP hPQ, Category.assoc]
      change Subobject.ofLE B P hBP ≫ (i ≫ g) = 0
      rw [hg, comp_zero]
    let q := cokernel.desc b g hbg
    have hq : q = 0 := by
      apply zero_of_epi_comp (i ≫ cokernel.π b)
      rw [Category.assoc, cokernel.π_desc]
      exact hg
    calc
      g = cokernel.π b ≫ q := (cokernel.π_desc b g hbg).symm
      _ = 0 := by rw [hq, comp_zero]
  haveI : Epi (Subobject.ofLE P Q hPQ) := hi
  haveI : IsIso (Subobject.ofLE P Q hPQ) := isIso_of_mono_of_epi _
  exact le_antisymm hPQ
    (Subobject.le_of_comm (inv (Subobject.ofLE P Q hPQ))
      (by simp [Subobject.ofLE_arrow]))

private theorem subquotient_eq_of_eq
    {C : Type*} [Category C] [Abelian C] {V : C}
    {B Z B' Z' : Subobject V} (h : B ≤ Z) (h' : B' ≤ Z')
    (hB : B = B') (hZ : Z = Z') :
    cokernel (Subobject.ofLE B Z h) =
      cokernel (Subobject.ofLE B' Z' h') := by
  subst B'
  subst Z'
  rfl

/-- Canonical isomorphism between two subquotient pages whose boundary and
cycle subobjects agree.  It is built by mapping the two defining arrows, so
it retains functoriality with respect to maps of spectral-sequence data. -/
noncomputable def pageIsoOfSubobjectsEq
    {C : Type*} [Category C] [Abelian C] (D : SSData C)
    (i j : WithTop ℕ) (hB : D.B i = D.B j) (hZ : D.Z i = D.Z j) :
    D.page i ≅ D.page j := by
  let eB := Subobject.isoOfEq (D.B i) (D.B j) hB
  let eZ := Subobject.isoOfEq (D.Z i) (D.Z j) hZ
  exact cokernel.mapIso
    (Subobject.ofLE (D.B i) (D.Z i) (D.B_le_Z i))
    (Subobject.ofLE (D.B j) (D.Z j) (D.B_le_Z j)) eB eZ (by
      apply (cancel_mono (D.Z j).arrow).mp
      simp only [eB, eZ, Category.assoc, Subobject.isoOfEq_hom,
        Subobject.ofLE_arrow])

/-- The preceding page isomorphism sends the source quotient projection to
the target quotient projection after the canonical cycle isomorphism. -/
theorem pageπ_pageIsoOfSubobjectsEq_hom
    {C : Type*} [Category C] [Abelian C] (D : SSData C)
    (i j : WithTop ℕ) (hB : D.B i = D.B j) (hZ : D.Z i = D.Z j) :
    D.pageπ i ≫ (pageIsoOfSubobjectsEq D i j hB hZ).hom =
      (Subobject.isoOfEq (D.Z i) (D.Z j) hZ).hom ≫ D.pageπ j := by
  unfold pageIsoOfSubobjectsEq
  rw [cokernel.mapIso_hom]
  erw [cokernel.π_desc]

/-- Page isomorphisms obtained from equal cycle and boundary subobjects are
natural for the canonical page maps of a spectral-sequence morphism. -/
theorem pageIsoOfSubobjectsEq_naturality
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} (F : SpectralSequenceMorphism E E')
    (k : ι) (i j : WithTop ℕ)
    (hBS : (E.ssData k).B i = (E.ssData k).B j)
    (hZS : (E.ssData k).Z i = (E.ssData k).Z j)
    (hBT : (E'.ssData k).B i = (E'.ssData k).B j)
    (hZT : (E'.ssData k).Z i = (E'.ssData k).Z j) :
    F.toSSDataMorphism.pageMap k i ≫
        (pageIsoOfSubobjectsEq (E'.ssData k) i j hBT hZT).hom =
      (pageIsoOfSubobjectsEq (E.ssData k) i j hBS hZS).hom ≫
        F.toSSDataMorphism.pageMap k j := by
  let eZS := Subobject.isoOfEq
    ((E.ssData k).Z i) ((E.ssData k).Z j) hZS
  let eZT := Subobject.isoOfEq
    ((E'.ssData k).Z i) ((E'.ssData k).Z j) hZT
  have hlift :
      (F.preserves_Z k i).choose ≫ eZT.hom =
        eZS.hom ≫ (F.preserves_Z k j).choose := by
    apply (cancel_mono ((E'.ssData k).Z j).arrow).mp
    simp only [Category.assoc, eZS, eZT, Subobject.isoOfEq_hom,
      Subobject.ofLE_arrow]
    rw [(F.preserves_Z k i).choose_spec,
      (F.preserves_Z k j).choose_spec]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  apply (cancel_epi ((E.ssData k).pageπ i)).mp
  rw [← Category.assoc, F.toSSDataMorphism.pageπ_pageMap]
  rw [← Category.assoc,
    pageπ_pageIsoOfSubobjectsEq_hom (E.ssData k) i j hBS hZS]
  rw [Category.assoc,
    pageπ_pageIsoOfSubobjectsEq_hom (E'.ssData k) i j hBT hZT]
  rw [Category.assoc, F.toSSDataMorphism.pageπ_pageMap]
  simpa only [← Category.assoc] using
    congrArg (fun z => z ≫ (E'.ssData k).pageπ j) hlift

/-- The canonical isomorphism from `E∞` to a finite page whose cycle and
boundary subobjects have already stabilized.  The initial equality only
unfolds the definition of `E∞`; all mathematical content is carried by
`pageIsoOfSubobjectsEq`. -/
noncomputable def eInftyIsoPageOfSubobjectsEq
    {C : Type*} [Category C] [Abelian C] (D : SSData C)
    (n : WithTop ℕ) (hB : D.B ⊤ = D.B n) (hZ : D.Z ⊤ = D.Z n) :
    D.eInfty ≅ D.page n :=
  pageIsoOfSubobjectsEq D ⊤ n hB hZ

/-- The canonical stabilized `E∞` comparison commutes with every
spectral-sequence morphism. -/
theorem eInftyIsoPageOfSubobjectsEq_naturality
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} (F : SpectralSequenceMorphism E E')
    (k : ι) (n : WithTop ℕ)
    (hBS : (E.ssData k).B ⊤ = (E.ssData k).B n)
    (hZS : (E.ssData k).Z ⊤ = (E.ssData k).Z n)
    (hBT : (E'.ssData k).B ⊤ = (E'.ssData k).B n)
    (hZT : (E'.ssData k).Z ⊤ = (E'.ssData k).Z n) :
    F.eInftyMap k ≫
        (eInftyIsoPageOfSubobjectsEq (E'.ssData k) n hBT hZT).hom =
      (eInftyIsoPageOfSubobjectsEq (E.ssData k) n hBS hZS).hom ≫
        F.toSSDataMorphism.pageMap k n := by
  change F.toSSDataMorphism.pageMap k ⊤ ≫ _ = _
  unfold eInftyIsoPageOfSubobjectsEq
  exact pageIsoOfSubobjectsEq_naturality F k ⊤ n
    hBS hZS hBT hZT

/-- If no new boundaries have appeared, the later page embeds in the
initial page by inclusion of cycles and quotienting by the common boundary
subobject. This works for the limiting page as well. -/
noncomputable def pageToInitialOfBoundariesEq
    {C : Type*} [Category C] [Abelian C]
    (D : SSData C) (n : WithTop ℕ) (hB : D.B n = D.B 0) :
    D.page n ⟶ D.page 0 :=
  cokernel.map
    (Subobject.ofLE (D.B n) (D.Z n) (D.B_le_Z n))
    (Subobject.ofLE (D.B 0) (D.Z 0) (D.B_le_Z 0))
    (Subobject.isoOfEq (D.B n) (D.B 0) hB).hom
    (Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le)) (by
      apply (cancel_mono (D.Z 0).arrow).mp
      simp only [Category.assoc, Subobject.ofLE_arrow,
        Subobject.isoOfEq_hom])

/-- The diagonal page inclusion is characterized by the inclusion of its
cycle representatives. -/
theorem pageπ_pageToInitialOfBoundariesEq
    {C : Type*} [Category C] [Abelian C]
    (D : SSData C) (n : WithTop ℕ) (hB : D.B n = D.B 0) :
    D.pageπ n ≫ pageToInitialOfBoundariesEq D n hB =
      Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫ D.pageπ 0 := by
  unfold pageToInitialOfBoundariesEq
  simp [SSData.pageπ, cokernel.map]

private theorem factor_cokernelMap_local
    {C : Type*} [Category C] [Abelian C] {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) =
      cokernel.π (Subobject.ofLE P Q hPQ) ≫
        Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR := by
  simp [Subobject.cokernelMap_ofLE, cokernel.π_desc]

private instance cokernelMap_ofLE_mono_local
    {C : Type*} [Category C] [Abelian C] {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    Mono (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR) := by
  open CategoryTheory.Abelian.Pseudoelement in
  refine mono_of_zero_of_map_zero _ fun a ha => ?_
  obtain ⟨q, hq⟩ :=
    pseudo_surjective_of_epi (cokernel.π (Subobject.ofLE P Q hPQ)) a
  rw [← hq] at ha ⊢
  have ha' : pseudoApply (cokernel.π (Subobject.ofLE P R hPR))
      (pseudoApply (Subobject.ofLE Q R hQR) q) = 0 := by
    have h1 := (Abelian.Pseudoelement.comp_apply
      (Subobject.ofLE Q R hQR) (cokernel.π (Subobject.ofLE P R hPR)) q).symm
    rw [h1, factor_cokernelMap_local P Q R hPQ hQR hPR,
      Abelian.Pseudoelement.comp_apply]
    exact ha
  have hexact : (ShortComplex.mk (Subobject.ofLE P R hPR)
      (cokernel.π (Subobject.ofLE P R hPR))
      (cokernel.condition _)).Exact :=
    ShortComplex.cokernelSequence_exact (Subobject.ofLE P R hPR)
  obtain ⟨p, hp⟩ := pseudo_exact_of_exact hexact _ ha'
  have hp' : pseudoApply (Subobject.ofLE Q R hQR)
      (pseudoApply (Subobject.ofLE P Q hPQ) p) =
      pseudoApply (Subobject.ofLE Q R hQR) q := by
    rw [← Abelian.Pseudoelement.comp_apply, Subobject.ofLE_comp_ofLE]
    exact hp
  have hinj := pseudo_injective_of_mono (Subobject.ofLE Q R hQR) hp'
  rw [← hinj, ← Abelian.Pseudoelement.comp_apply,
    cokernel.condition, Abelian.Pseudoelement.zero_apply]

instance pageToInitialOfBoundariesEq_mono
    {C : Type*} [Category C] [Abelian C]
    (D : SSData C) (n : WithTop ℕ) (hB : D.B n = D.B 0) :
    Mono (pageToInitialOfBoundariesEq D n hB) := by
  let hBZ : D.B 0 ≤ D.Z n := hB ▸ D.B_le_Z n
  let e : D.page n ≅ cokernel (Subobject.ofLE (D.B 0) (D.Z n) hBZ) :=
    cokernel.mapIso
      (Subobject.ofLE (D.B n) (D.Z n) (D.B_le_Z n))
      (Subobject.ofLE (D.B 0) (D.Z n) hBZ)
      (Subobject.isoOfEq (D.B n) (D.B 0) hB)
      (Iso.refl _) (by
        apply (cancel_mono (D.Z n).arrow).mp
        simp only [Category.assoc, Subobject.ofLE_arrow,
          Subobject.isoOfEq_hom, Iso.refl_hom, Category.comp_id])
  let c :=
    Subobject.cokernelMap_ofLE (D.B 0) (D.Z n) (D.Z 0)
      hBZ (D.Z_anti bot_le) (D.B_le_Z 0)
  let m := e.hom ≫ c
  have he : D.pageπ n ≫ e.hom =
      cokernel.π (Subobject.ofLE (D.B 0) (D.Z n) hBZ) := by
    dsimp only [e, SSData.pageπ]
    rw [cokernel.mapIso_hom]
    erw [cokernel.π_desc]
    simp
  have heq : pageToInitialOfBoundariesEq D n hB = m := by
    apply (cancel_epi (D.pageπ n)).mp
    calc
      D.pageπ n ≫ pageToInitialOfBoundariesEq D n hB =
          Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) ≫
            D.pageπ 0 := pageπ_pageToInitialOfBoundariesEq D n hB
      _ = D.pageπ n ≫ m := by
        dsimp only [m, c]
        rw [← Category.assoc, he]
        simp [Subobject.cokernelMap_ofLE, SSData.pageπ]
  rw [heq]
  dsimp only [m]
  let hc : Mono c := by
    dsimp only [c]
    exact cokernelMap_ofLE_mono_local (D.B 0) (D.Z n) (D.Z 0)
      hBZ (D.Z_anti bot_le) (D.B_le_Z 0)
  let hemono : Mono e.hom := by infer_instance
  constructor
  intro Z g h hgh
  have hcomp : (g ≫ e.hom) ≫ c = (h ≫ e.hom) ≫ c := by
    simpa only [Category.assoc] using hgh
  have heq : g ≫ e.hom = h ≫ e.hom :=
    @Mono.right_cancellation C _ _ _ c hc Z _ _ hcomp
  exact @Mono.right_cancellation C _ _ _ e.hom hemono Z _ _ heq

/-- The inclusion of a later page into the initial page is natural for
spectral-sequence morphisms whenever both diagonal boundary towers remain
equal to their initial boundary subobjects. -/
theorem pageToInitialOfBoundariesEq_naturality
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} (F : SpectralSequenceMorphism E E')
    (k : ι) (n : WithTop ℕ)
    (hBS : (E.ssData k).B n = (E.ssData k).B 0)
    (hBT : (E'.ssData k).B n = (E'.ssData k).B 0) :
    F.toSSDataMorphism.pageMap k n ≫
        pageToInitialOfBoundariesEq (E'.ssData k) n hBT =
      pageToInitialOfBoundariesEq (E.ssData k) n hBS ≫
        F.toSSDataMorphism.pageMap k 0 := by
  let iS := Subobject.ofLE ((E.ssData k).Z n) ((E.ssData k).Z 0)
    ((E.ssData k).Z_anti bot_le)
  let iT := Subobject.ofLE ((E'.ssData k).Z n) ((E'.ssData k).Z 0)
    ((E'.ssData k).Z_anti bot_le)
  have hlift : (F.preserves_Z k n).choose ≫ iT =
      iS ≫ (F.preserves_Z k 0).choose := by
    apply (cancel_mono ((E'.ssData k).Z 0).arrow).mp
    simp only [Category.assoc, iS, iT, Subobject.ofLE_arrow]
    rw [(F.preserves_Z k n).choose_spec,
      (F.preserves_Z k 0).choose_spec]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  apply (cancel_epi ((E.ssData k).pageπ n)).mp
  rw [← Category.assoc, F.toSSDataMorphism.pageπ_pageMap]
  rw [Category.assoc,
    pageπ_pageToInitialOfBoundariesEq (E'.ssData k) n hBT]
  rw [← Category.assoc]
  calc
    ((F.preserves_Z k n).choose ≫ iT) ≫ (E'.ssData k).pageπ 0 =
        (iS ≫ (F.preserves_Z k 0).choose) ≫
          (E'.ssData k).pageπ 0 :=
      congrArg (fun z => z ≫ (E'.ssData k).pageπ 0) hlift
    _ = iS ≫ ((F.preserves_Z k 0).choose ≫
          (E'.ssData k).pageπ 0) := Category.assoc _ _ _
    _ = iS ≫ ((E.ssData k).pageπ 0 ≫
          F.toSSDataMorphism.pageMap k 0) := by
      rw [F.toSSDataMorphism.pageπ_pageMap]
    _ = (iS ≫ (E.ssData k).pageπ 0) ≫
          F.toSSDataMorphism.pageMap k 0 := (Category.assoc _ _ _).symm
    _ = ((E.ssData k).pageπ n ≫
          pageToInitialOfBoundariesEq (E.ssData k) n hBS) ≫
          F.toSSDataMorphism.pageMap k 0 := by
      rw [pageπ_pageToInitialOfBoundariesEq]
    _ = (E.ssData k).pageπ n ≫
          (pageToInitialOfBoundariesEq (E.ssData k) n hBS ≫
            F.toSSDataMorphism.pageMap k 0) := Category.assoc _ _ _

/-- If both a later layer and the initial layer equal the limiting
subquotient, the limiting-to-initial isomorphism factors through the later
layer and its canonical inclusion into the initial page. -/
theorem pageIsoOfSubobjectsEq_factor_toInitial
    {C : Type*} [Category C] [Abelian C] (D : SSData C)
    (n : WithTop ℕ)
    (hBn : D.B ⊤ = D.B n) (hZn : D.Z ⊤ = D.Z n)
    (hB0 : D.B ⊤ = D.B 0) (hZ0 : D.Z ⊤ = D.Z 0) :
    (pageIsoOfSubobjectsEq D ⊤ 0 hB0 hZ0).hom =
      (pageIsoOfSubobjectsEq D ⊤ n hBn hZn).hom ≫
        pageToInitialOfBoundariesEq D n (hBn.symm.trans hB0) := by
  have hcycles :
      (Subobject.isoOfEq (D.Z ⊤) (D.Z 0) hZ0).hom =
        (Subobject.isoOfEq (D.Z ⊤) (D.Z n) hZn).hom ≫
          Subobject.ofLE (D.Z n) (D.Z 0) (D.Z_anti bot_le) := by
    apply (cancel_mono (D.Z 0).arrow).mp
    simp only [Category.assoc, Subobject.isoOfEq_hom,
      Subobject.ofLE_arrow]
  apply (cancel_epi (D.pageπ ⊤)).mp
  rw [pageπ_pageIsoOfSubobjectsEq_hom]
  rw [← Category.assoc, pageπ_pageIsoOfSubobjectsEq_hom]
  rw [Category.assoc, pageπ_pageToInitialOfBoundariesEq]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ D.pageπ 0) hcycles

/-- The stabilized `E∞` comparison factors through a later layer and
its canonical inclusion into the initial layer. -/
theorem eInftyIsoPageOfSubobjectsEq_factor_toInitial
    {C : Type*} [Category C] [Abelian C] (D : SSData C)
    (n : WithTop ℕ)
    (hBn : D.B ⊤ = D.B n) (hZn : D.Z ⊤ = D.Z n)
    (hB0 : D.B ⊤ = D.B 0) (hZ0 : D.Z ⊤ = D.Z 0) :
    (eInftyIsoPageOfSubobjectsEq D 0 hB0 hZ0).hom =
      (eInftyIsoPageOfSubobjectsEq D n hBn hZn).hom ≫
        pageToInitialOfBoundariesEq D n (hBn.symm.trans hB0) := by
  unfold eInftyIsoPageOfSubobjectsEq
  exact pageIsoOfSubobjectsEq_factor_toInitial D n hBn hZn hB0 hZ0

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-- The displayed Adams page `n+2` and the underlying subquotient layer
`n` differ only by the convention that the Adams spectral sequence starts
on page two. -/
noncomputable def synAdamsPageNatAddTwoIso (X : Syn) (n : ℕ)
    (k : ℤ × ℤ × ℤ) :
    (SynAdamsSS Syn X).Page ((n + 2 : ℕ) : ℤ) k ≅
      ((SynAdamsSS Syn X).ssData k).page n :=
  eqToIso (by
    simp only [SpectralSequence.Page, synAdamsSS_r0]
    congr 2
    omega)

/-- On displayed page `n+2`, the Adams page map is the canonical map on
the underlying `n`th subquotient, conjugated by the page-numbering
identifications. -/
theorem synAdamsPageMap_natAddTwo {X Y : Syn} (f : X ⟶ Y)
    (n : ℕ) (k : ℤ × ℤ × ℤ) :
    synAdamsPageMap f (((n + 2 : ℕ) : ℤ)) k =
      (synAdamsPageNatAddTwoIso X n k).hom ≫
      (synAdamsSS_functorial f).toSSDataMorphism.pageMap k n ≫
      (synAdamsPageNatAddTwoIso Y n k).inv := by
  unfold synAdamsPageMap SSDataMorphism.pageMapOfEq
    synAdamsPageNatAddTwoIso
  dsimp only
  simp [synAdamsSS_r0]

/-- Vanishing on the second synthetic Adams page persists on every later
page. The proof does not assume degeneration. -/
theorem synAdams_page_isZero_of_e2 (X : Syn) (r : ℤ)
    (k : ℤ × ℤ × ℤ) (h : IsZero ((SynAdamsSS Syn X).Page 2 k)) :
    IsZero ((SynAdamsSS Syn X).Page r k) := by
  apply page_isZero_of_le ((SynAdamsSS Syn X).ssData k)
    (i := (↑(0 : ℕ) : WithTop ℕ)) (by simp)
  simpa only [SpectralSequence.Page, synAdamsSS_r0, sub_self, Int.toNat_zero]
    using h

/-- Second-page vanishing also forces the limiting subquotient to vanish. -/
theorem synAdams_eInfty_isZero_of_e2 (X : Syn) (k : ℤ × ℤ × ℤ)
    (h : IsZero ((SynAdamsSS Syn X).Page 2 k)) :
    IsZero (((SynAdamsSS Syn X).ssData k).eInfty) := by
  apply page_isZero_of_le ((SynAdamsSS Syn X).ssData k)
    (i := (↑(0 : ℕ) : WithTop ℕ)) le_top
  simpa only [SpectralSequence.Page, synAdamsSS_r0, sub_self, Int.toNat_zero]
    using h

/-- If the second page is supported in `0 ≤ t-w < n`, then differentials
with `n ≤ r-1` vanish: either their source or their target is outside
that same strip. This is a support condition, not boundedness of the
Adams filtration `s`. -/
theorem synAdams_d_eq_zero_of_e2_strip (X : Syn) (n : ℕ)
    (hstrip : ∀ s t w : ℤ, t - w < 0 ∨ (n : ℤ) ≤ t - w →
      IsZero ((SynAdamsSS Syn X).Page 2 (s, t, w)))
    (r : ℤ) (hr : (n : ℤ) ≤ r - 1) (k : ℤ × ℤ × ℤ) :
    (SynAdamsSS Syn X).d r k = 0 := by
  rcases k with ⟨s, t, w⟩
  by_cases h : t - w < 0 ∨ (n : ℤ) ≤ t - w
  · exact (synAdams_page_isZero_of_e2 X r (s, t, w)
      (hstrip s t w h)).eq_of_src _ _
  · have htarget : IsZero ((SynAdamsSS Syn X).Page r
        ((s, t, w) + (SynAdamsSS Syn X).diffDeg r)) := by
      rw [synAdamsSS_diffDeg]
      apply synAdams_page_isZero_of_e2
      apply hstrip
      right
      dsimp
      omega
    exact htarget.eq_of_tgt _ _

/-- A strip of width `n` on the second page forces degeneration by page
`max 2 (n+1)`. -/
theorem synAdams_degenerates_of_e2_strip (X : Syn) (n : ℕ)
    (hstrip : ∀ s t w : ℤ, t - w < 0 ∨ (n : ℤ) ≤ t - w →
      IsZero ((SynAdamsSS Syn X).Page 2 (s, t, w))) :
    (SynAdamsSS Syn X).DegeneratesAt (max 2 ((n : ℤ) + 1)) := by
  intro r hr k
  exact synAdams_d_eq_zero_of_e2_strip X n hstrip r (by omega) k

/-- In particular, support on the diagonal `t=w` forces degeneration
from the second page. -/
theorem synAdams_degenerates_of_e2_diagonal (X : Syn)
    (hdiag : ∀ s t w : ℤ, t ≠ w →
      IsZero ((SynAdamsSS Syn X).Page 2 (s, t, w))) :
    (SynAdamsSS Syn X).DegeneratesAt 2 := by
  have hstrip : ∀ s t w : ℤ, t - w < 0 ∨ (1 : ℤ) ≤ t - w →
      IsZero ((SynAdamsSS Syn X).Page 2 (s, t, w)) := by
    intro s t w h
    exact hdiag s t w (by omega)
  simpa using synAdams_degenerates_of_e2_strip X 1 hstrip

/-- A zero outgoing differential leaves the cycle subobject unchanged. -/
private theorem cycles_succ_of_zero
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (hr : E.r₀ ≤ r)
    (k : ι) (hd : E.d r k = 0) :
    (E.ssData k).Z ↑((r - E.r₀).toNat + 1) =
      (E.ssData k).Z ↑(r - E.r₀).toNat := by
  let n := (r - E.r₀).toNat
  let D := E.ssData k
  have hz := E.Z_succ r k hr
  rw [hd, kernelSubobject_zero] at hz
  let i := Subobject.ofLE (D.Z ↑(n + 1)) (D.Z ↑n)
    (D.Z_anti (by exact_mod_cast Nat.le_succ n))
  let p := i ≫ D.pageπ ↑n
  have hp : imageSubobject p = ⊤ := hz.symm
  haveI : IsIso (imageSubobject p).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).mpr hp
  haveI : Epi p := by
    rw [← imageSubobject_arrow_comp p]
    infer_instance
  exact subobject_eq_of_quotient_epi (D.B ↑n) (D.Z ↑(n + 1)) (D.Z ↑n)
    ((D.B_mono (by exact_mod_cast Nat.le_succ n)).trans (D.B_le_Z _))
    (D.Z_anti (by exact_mod_cast Nat.le_succ n))

/-- A zero differential leaves its target boundary subobject unchanged. -/
private theorem boundaries_succ_of_zero
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (hr : E.r₀ ≤ r)
    (k : ι) (hd : E.d r k = 0) :
    (E.ssData (k + E.diffDeg r)).B ↑((r - E.r₀).toNat + 1) =
      (E.ssData (k + E.diffDeg r)).B ↑(r - E.r₀).toNat := by
  let n := (r - E.r₀).toNat
  let D := E.ssData (k + E.diffDeg r)
  have hb := E.B_succ r k hr
  rw [hd, imageSubobject_zero] at hb
  let b := Subobject.ofLE (D.B ↑n) (D.Z ↑n) (D.B_le_Z _)
  let j := Subobject.ofLE (D.B ↑(n + 1)) (D.Z ↑n)
    ((D.B_le_Z _).trans (D.Z_anti (by exact_mod_cast Nat.le_succ n)))
  have hj : j ≫ cokernel.π b = 0 := by
    have hp : imageSubobject (j ≫ cokernel.π b) = ⊥ := hb.symm
    have ha : (imageSubobject (j ≫ cokernel.π b)).arrow = 0 := by
      rw [hp]
      exact Subobject.bot_arrow
    rw [← imageSubobject_arrow_comp (j ≫ cokernel.π b), ha, comp_zero]
  apply le_antisymm _ (D.B_mono (by exact_mod_cast Nat.le_succ n))
  apply Subobject.le_of_comm (Abelian.monoLift b j hj)
  have hcomp := congrArg (fun f => f ≫ (D.Z ↑n).arrow)
    (Abelian.monoLift_comp b j hj)
  simpa only [Category.assoc, b, j, Subobject.ofLE_arrow] using hcomp

/-- Zero outgoing synthetic Adams differential gives equality of successive
cycle subobjects, in the natural-number indexing of `SSData`. -/
theorem synAdams_cycles_succ_of_zero (X : Syn) (n : ℕ)
    (k : ℤ × ℤ × ℤ) (hd : (SynAdamsSS Syn X).d (2 + n) k = 0) :
    ((SynAdamsSS Syn X).ssData k).Z ↑(n + 1) =
      ((SynAdamsSS Syn X).ssData k).Z ↑n := by
  simpa only [synAdamsSS_r0, add_sub_cancel_left, Int.toNat_natCast] using
    cycles_succ_of_zero (SynAdamsSS Syn X) (2 + n)
      (by simp [synAdamsSS_r0]) k hd

/-- Zero incoming synthetic Adams differential gives equality of successive
boundary subobjects. -/
theorem synAdams_boundaries_succ_of_zero (X : Syn) (n : ℕ)
    (k : ℤ × ℤ × ℤ)
    (hd : (SynAdamsSS Syn X).d (2 + n)
      (k - (SynAdamsSS Syn X).diffDeg (2 + n)) = 0) :
    ((SynAdamsSS Syn X).ssData k).B ↑(n + 1) =
      ((SynAdamsSS Syn X).ssData k).B ↑n := by
  have h := boundaries_succ_of_zero (SynAdamsSS Syn X) (2 + n)
    (by simp [synAdamsSS_r0]) _ hd
  simp only [synAdamsSS_r0, add_sub_cancel_left, Int.toNat_natCast] at h
  exact (congrArg (fun j =>
    ((SynAdamsSS Syn X).ssData j).B ↑(n + 1) =
      ((SynAdamsSS Syn X).ssData j).B ↑n)
    (sub_add_cancel k ((SynAdamsSS Syn X).diffDeg (2 + n)))).mp h

/-- Degeneration from page two makes both limiting subobjects equal to
their initial values. Only the existing greatest/least bounds in `SSData`
are used in passing to the limit. -/
theorem synAdams_limit_subobjects_of_degenerates_e2 (X : Syn)
    (hd : (SynAdamsSS Syn X).DegeneratesAt 2) (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn X).ssData k).Z ⊤ =
        ((SynAdamsSS Syn X).ssData k).Z ↑(0 : ℕ) ∧
      ((SynAdamsSS Syn X).ssData k).B ⊤ =
        ((SynAdamsSS Syn X).ssData k).B ↑(0 : ℕ) := by
  let D := (SynAdamsSS Syn X).ssData k
  have hZ : ∀ n : ℕ, D.Z ↑n = D.Z ↑(0 : ℕ) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      exact (synAdams_cycles_succ_of_zero X n k
        (hd (2 + n) (by omega) k)).trans ih
  have hB : ∀ n : ℕ, D.B ↑n = D.B ↑(0 : ℕ) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      exact (synAdams_boundaries_succ_of_zero X n k
        (hd (2 + n) (by omega) _)).trans ih
  constructor
  · exact le_antisymm (D.Z_anti le_top)
      (D.Z_top_greatest _ (fun n => (hZ n).ge))
  · exact le_antisymm (D.B_top_least _ (fun n => (hB n).le))
      (D.B_mono le_top)

/-- Degeneration from an arbitrary meaningful page makes the limiting
cycle and boundary subobjects equal to their values on that page.  This is
the version needed for the finite quotients `X/λ^n`, whose stabilization
page depends on `n`. -/
theorem synAdams_limit_subobjects_of_degenerates (X : Syn) (N : ℤ)
    (hN : 2 ≤ N) (hd : (SynAdamsSS Syn X).DegeneratesAt N)
    (k : ℤ × ℤ × ℤ) :
    let n₀ := (N - 2).toNat
    ((SynAdamsSS Syn X).ssData k).Z ⊤ =
        ((SynAdamsSS Syn X).ssData k).Z (n₀ : WithTop ℕ) ∧
      ((SynAdamsSS Syn X).ssData k).B ⊤ =
        ((SynAdamsSS Syn X).ssData k).B (n₀ : WithTop ℕ) := by
  dsimp only
  let n₀ := (N - 2).toNat
  let D := (SynAdamsSS Syn X).ssData k
  have hn₀ : (n₀ : ℤ) = N - 2 := by
    exact Int.toNat_of_nonneg (by omega)
  have hZtail : ∀ m : ℕ, D.Z (↑(n₀ + m) : WithTop ℕ) = D.Z ↑n₀ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hpage : N ≤ 2 + (n₀ + m : ℕ) := by
        rw [Nat.cast_add, hn₀]
        omega
      have hzero := hd (2 + (n₀ + m : ℕ)) hpage k
      exact (synAdams_cycles_succ_of_zero X (n₀ + m) k hzero).trans ih
  have hBtail : ∀ m : ℕ, D.B (↑(n₀ + m) : WithTop ℕ) = D.B ↑n₀ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hpage : N ≤ 2 + (n₀ + m : ℕ) := by
        rw [Nat.cast_add, hn₀]
        omega
      have hzero := hd (2 + (n₀ + m : ℕ)) hpage
        (k - (SynAdamsSS Syn X).diffDeg (2 + (n₀ + m : ℕ)))
      exact (synAdams_boundaries_succ_of_zero X (n₀ + m) k hzero).trans ih
  constructor
  · apply le_antisymm (D.Z_anti le_top)
    apply D.Z_top_greatest
    intro n
    by_cases hn : n₀ ≤ n
    · have heq : n₀ + (n - n₀) = n := Nat.add_sub_of_le hn
      simpa [heq] using (hZtail (n - n₀)).ge
    · exact D.Z_anti (by
        exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_antisymm
    · apply D.B_top_least
      intro n
      by_cases hn : n₀ ≤ n
      · have heq : n₀ + (n - n₀) = n := Nat.add_sub_of_le hn
        simpa [heq] using (hBtail (n - n₀)).le
      · exact D.B_mono (by
          exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hn))
    · exact D.B_mono le_top

/-- If synthetic Adams degenerates from page `N ≥ 2`, its limiting page is
canonically isomorphic to page `N`.  No boundedness of the Adams filtration
is used. -/
noncomputable def synAdams_eInftyIso_page_of_degenerates (X : Syn)
    (N : ℤ) (hN : 2 ≤ N) (hd : (SynAdamsSS Syn X).DegeneratesAt N)
    (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn X).ssData k).eInfty ≅
      (SynAdamsSS Syn X).Page N k := by
  obtain ⟨hZ, hB⟩ :=
    synAdams_limit_subobjects_of_degenerates X N hN hd k
  let D := (SynAdamsSS Syn X).ssData k
  let n₀ := (N - 2).toNat
  have hindex : (N - (SynAdamsSS Syn X).r₀).toNat = n₀ := by
    rw [synAdamsSS_r0]
  exact pageIsoOfSubobjectsEq D ⊤ n₀ hB hZ ≪≫
    (eqToIso (congrArg (fun n : ℕ => D.page (n : WithTop ℕ)) hindex)).symm

/-- Degeneration from displayed page `n+2` identifies the limiting cycle
subobject with the cycle subobject on underlying layer `n`. -/
theorem synAdams_limit_cycles_natAddTwo (X : Syn) (n : ℕ)
    (hd : (SynAdamsSS Syn X).DegeneratesAt ((n + 2 : ℕ) : ℤ))
    (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn X).ssData k).Z ⊤ =
      ((SynAdamsSS Syn X).ssData k).Z n := by
  obtain ⟨hZ, _⟩ := synAdams_limit_subobjects_of_degenerates X
    ((n + 2 : ℕ) : ℤ) (by omega) hd k
  have hn : ((↑(n + 2) : ℤ) - 2).toNat = n := by omega
  simpa only [hn] using hZ

/-- Degeneration from displayed page `n+2` identifies the limiting
boundary subobject with the boundary subobject on underlying layer `n`. -/
theorem synAdams_limit_boundaries_natAddTwo (X : Syn) (n : ℕ)
    (hd : (SynAdamsSS Syn X).DegeneratesAt ((n + 2 : ℕ) : ℤ))
    (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn X).ssData k).B ⊤ =
      ((SynAdamsSS Syn X).ssData k).B n := by
  obtain ⟨_, hB⟩ := synAdams_limit_subobjects_of_degenerates X
    ((n + 2 : ℕ) : ℤ) (by omega) hd k
  have hn : ((↑(n + 2) : ℤ) - 2).toNat = n := by omega
  simpa only [hn] using hB

/-- Canonical limiting-page comparison at displayed page `n+2`, written
directly in terms of the underlying `n`th subquotient.  This formulation
keeps its naturality visible. -/
noncomputable def synAdams_eInftyIso_page_natAddTwo (X : Syn) (n : ℕ)
    (hd : (SynAdamsSS Syn X).DegeneratesAt ((n + 2 : ℕ) : ℤ))
    (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn X).ssData k).eInfty ≅
      (SynAdamsSS Syn X).Page ((n + 2 : ℕ) : ℤ) k :=
  eInftyIsoPageOfSubobjectsEq ((SynAdamsSS Syn X).ssData k)
      n (synAdams_limit_boundaries_natAddTwo X n hd k)
        (synAdams_limit_cycles_natAddTwo X n hd k) ≪≫
    (synAdamsPageNatAddTwoIso X n k).symm

/-- The canonical limiting-page comparison at `n+2` is natural in the
synthetic spectrum. -/
theorem synAdams_eInftyIso_page_natAddTwo_naturality
    {X Y : Syn} (f : X ⟶ Y) (n : ℕ)
    (hdX : (SynAdamsSS Syn X).DegeneratesAt ((n + 2 : ℕ) : ℤ))
    (hdY : (SynAdamsSS Syn Y).DegeneratesAt ((n + 2 : ℕ) : ℤ))
    (k : ℤ × ℤ × ℤ) :
    (synAdamsSS_functorial f).eInftyMap k ≫
        (synAdams_eInftyIso_page_natAddTwo Y n hdY k).hom =
      (synAdams_eInftyIso_page_natAddTwo X n hdX k).hom ≫
        synAdamsPageMap f ((n + 2 : ℕ) : ℤ) k := by
  unfold synAdams_eInftyIso_page_natAddTwo
  simp only [Iso.trans_hom]
  rw [← Category.assoc,
    eInftyIsoPageOfSubobjectsEq_naturality
    (synAdamsSS_functorial f) k n
    (synAdams_limit_boundaries_natAddTwo X n hdX k)
    (synAdams_limit_cycles_natAddTwo X n hdX k)
    (synAdams_limit_boundaries_natAddTwo Y n hdY k)
    (synAdams_limit_cycles_natAddTwo Y n hdY k)]
  simp only [Category.assoc]
  apply (cancel_epi
    (eInftyIsoPageOfSubobjectsEq ((SynAdamsSS Syn X).ssData k) n
      (synAdams_limit_boundaries_natAddTwo X n hdX k)
      (synAdams_limit_cycles_natAddTwo X n hdX k)).hom).mpr
  rw [synAdamsPageMap_natAddTwo]
  simp

/-- If the boundary subobject has not changed by underlying layer `n`,
the displayed Adams page `n+2` maps canonically into the displayed second
page by inclusion of surviving cycles. -/
noncomputable def synAdams_displayedPageToE2OfBoundariesEq (X : Syn)
    (n : ℕ) (k : ℤ × ℤ × ℤ)
    (hB : ((SynAdamsSS Syn X).ssData k).B n =
      ((SynAdamsSS Syn X).ssData k).B 0) :
    (SynAdamsSS Syn X).Page ((n + 2 : ℕ) : ℤ) k ⟶
      (SynAdamsSS Syn X).Page 2 k :=
  (synAdamsPageNatAddTwoIso X n k).hom ≫
    pageToInitialOfBoundariesEq ((SynAdamsSS Syn X).ssData k) n hB ≫
    (synAdamsPageNatAddTwoIso X 0 k).inv

/-- The displayed later-page inclusion into E₂ is natural whenever the
source and target boundary towers are fixed through that layer. -/
theorem synAdams_displayedPageToE2OfBoundariesEq_naturality
    {X Y : Syn} (f : X ⟶ Y) (n : ℕ) (k : ℤ × ℤ × ℤ)
    (hBX : ((SynAdamsSS Syn X).ssData k).B n =
      ((SynAdamsSS Syn X).ssData k).B 0)
    (hBY : ((SynAdamsSS Syn Y).ssData k).B n =
      ((SynAdamsSS Syn Y).ssData k).B 0) :
    synAdamsPageMap f ((n + 2 : ℕ) : ℤ) k ≫
        synAdams_displayedPageToE2OfBoundariesEq Y n k hBY =
      synAdams_displayedPageToE2OfBoundariesEq X n k hBX ≫
        synAdamsPageMap f 2 k := by
  rw [synAdamsPageMap_natAddTwo]
  rw [show synAdamsPageMap f 2 k =
      (synAdamsPageNatAddTwoIso X 0 k).hom ≫
        (synAdamsSS_functorial f).toSSDataMorphism.pageMap k
          (↑(0 : ℕ) : WithTop ℕ) ≫
        (synAdamsPageNatAddTwoIso Y 0 k).inv by
    simpa using synAdamsPageMap_natAddTwo f 0 k]
  unfold synAdams_displayedPageToE2OfBoundariesEq
  simp only [Category.assoc]
  simp
  rw [pageToInitialOfBoundariesEq_naturality
    (synAdamsSS_functorial f) k n hBX hBY]
  rfl

/-- For a sequence already degenerate at E₂, its limiting-to-E₂
comparison factors through every later displayed page by the canonical
later-page inclusion. -/
theorem synAdams_eInftyIso_page_natAddTwo_factor_toE2 (X : Syn) (n : ℕ)
    (hd0 : (SynAdamsSS Syn X).DegeneratesAt 2)
    (hdn : (SynAdamsSS Syn X).DegeneratesAt ((n + 2 : ℕ) : ℤ))
    (k : ℤ × ℤ × ℤ) :
    (synAdams_eInftyIso_page_natAddTwo X 0 hd0 k).hom =
      (synAdams_eInftyIso_page_natAddTwo X n hdn k).hom ≫
        synAdams_displayedPageToE2OfBoundariesEq X n k
          ((synAdams_limit_boundaries_natAddTwo X n hdn k).symm.trans
            (synAdams_limit_boundaries_natAddTwo X 0 hd0 k)) := by
  unfold synAdams_eInftyIso_page_natAddTwo
    synAdams_displayedPageToE2OfBoundariesEq
  simp only [Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  apply (cancel_mono (synAdamsPageNatAddTwoIso X 0 k).inv).mpr
  convert eInftyIsoPageOfSubobjectsEq_factor_toInitial
    ((SynAdamsSS Syn X).ssData k) n
    (synAdams_limit_boundaries_natAddTwo X n hdn k)
    (synAdams_limit_cycles_natAddTwo X n hdn k)
    (synAdams_limit_boundaries_natAddTwo X 0 hd0 k)
    (synAdams_limit_cycles_natAddTwo X 0 hd0 k) using 1 <;>
      (try rfl) <;> (try simp)

/-- The second page and the limiting page agree when synthetic Adams
degenerates from page two; no bounded filtration is required. -/
noncomputable def synAdams_eInftyIso_e2_of_degenerates (X : Syn)
    (hd : (SynAdamsSS Syn X).DegeneratesAt 2) (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn X).ssData k).eInfty ≅ (SynAdamsSS Syn X).Page 2 k := by
  obtain ⟨hZ, hB⟩ := synAdams_limit_subobjects_of_degenerates_e2 X hd k
  let D := (SynAdamsSS Syn X).ssData k
  have hpage : D.page ⊤ = D.page ↑(0 : ℕ) :=
    subquotient_eq_of_eq (D.B_le_Z ⊤) (D.B_le_Z _) hB hZ
  have hindex : (2 - (SynAdamsSS Syn X).r₀).toNat = 0 := by
    rw [synAdamsSS_r0]
    rfl
  exact eqToIso hpage ≪≫
    (eqToIso (congrArg (fun n : ℕ => D.page ↑n) hindex)).symm

/-- Diagonal support on the second page identifies the limiting page with
that second page, using the proved degeneration and subobject stability. -/
noncomputable def synAdams_eInftyIso_e2_of_diagonal (X : Syn)
    (hdiag : ∀ s t w : ℤ, t ≠ w →
      IsZero ((SynAdamsSS Syn X).Page 2 (s, t, w)))
    (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn X).ssData k).eInfty ≅ (SynAdamsSS Syn X).Page 2 k :=
  synAdams_eInftyIso_e2_of_degenerates X
    (synAdams_degenerates_of_e2_diagonal X hdiag) k

/-- The associated-graded input of an extension spectral sequence can be
identified with the second Adams page whenever its source has diagonal
second-page support. This uses the given convergence structure and requires
no boundedness or separately postulated limiting-page comparison. -/
noncomputable def synAdams_associatedGradedIso_e2_of_diagonal (X : Syn)
    (hdiag : ∀ s t w : ℤ, t ≠ w →
      IsZero ((SynAdamsSS Syn X).Page 2 (s, t, w)))
    {A : ℤ × ℤ → AddCommGrpCat.{0}} {F : Filtration A}
    (conv : Convergence (SynAdamsSS Syn X) A F) (k : ℤ × ℤ × ℤ) :
    F.associatedGraded (conv.reindex k).1 (conv.reindex k).2 ≅
      (SynAdamsSS Syn X).Page 2 k :=
  (conv.iso k).symm ≪≫ synAdams_eInftyIso_e2_of_diagonal X hdiag k

/-- When the page differentials are zero, the successor-page homology
isomorphism identifies that next page with the current page. -/
noncomputable def synAdams_pageSuccIso_of_zero (X : Syn) (r : ℤ)
    (hr : 2 ≤ r) (hd : ∀ k, (SynAdamsSS Syn X).d r k = 0)
    (k : ℤ × ℤ × ℤ) :
    (SynAdamsSS Syn X).Page (r + 1) k ≅ (SynAdamsSS Syn X).Page r k := by
  let E := SynAdamsSS Syn X
  let S := E.pageShortComplex r (k - E.diffDeg r)
  let h := ShortComplex.LeftHomologyData.ofZeros S
    (hd (k - E.diffDeg r)) (hd (k - E.diffDeg r + E.diffDeg r))
  have hmiddle : h.H = E.Page r k := by
    change E.Page r (k - E.diffDeg r + E.diffDeg r) = E.Page r k
    rw [sub_add_cancel]
  exact E.pageHomologyIso r k (by simpa [E, synAdamsSS_r0] using hr) ≪≫
    h.homologyIso ≪≫ eqToIso hmiddle

/-- Iterating the zero-differential homology isomorphisms gives an actual
isomorphism from every later page to the page of degeneration. -/
noncomputable def synAdams_pageIso_of_degenerates (X : Syn) (N : ℤ)
    (hN : 2 ≤ N) (hd : (SynAdamsSS Syn X).DegeneratesAt N)
    (n : ℕ) (k : ℤ × ℤ × ℤ) :
    (SynAdamsSS Syn X).Page (N + n) k ≅ (SynAdamsSS Syn X).Page N k := by
  induction n with
  | zero => exact eqToIso (by simp)
  | succ n ih =>
    have hstep := synAdams_pageSuccIso_of_zero X (N + n) (by omega)
      (hd (N + n) (by omega)) k
    exact eqToIso (by simp only [Nat.cast_succ, add_assoc]) ≪≫ hstep ≪≫ ih

/-- Diagonal second-page support gives explicit isomorphisms of every
meaningful finite page with the second page. -/
noncomputable def synAdams_pageIso_e2_of_diagonal (X : Syn)
    (hdiag : ∀ s t w : ℤ, t ≠ w →
      IsZero ((SynAdamsSS Syn X).Page 2 (s, t, w)))
    (r : ℤ) (hr : 2 ≤ r) (k : ℤ × ℤ × ℤ) :
    (SynAdamsSS Syn X).Page r k ≅ (SynAdamsSS Syn X).Page 2 k := by
  have heq : r = 2 + ((r - 2).toNat : ℤ) := by omega
  exact eqToIso (congrArg (fun j => (SynAdamsSS Syn X).Page j k) heq) ≪≫
    synAdams_pageIso_of_degenerates X 2 (le_refl _)
      (synAdams_degenerates_of_e2_diagonal X hdiag) (r - 2).toNat k

/-! ### Local E₂ detection, without global degeneration -/

/-- E₂ vanishing at all possible incoming sources keeps the boundary
subobject fixed, including at infinity. No condition on outgoing
differentials is needed. -/
theorem synAdams_boundaries_eq_initial_of_e2_incoming (X : Syn)
    (k : ℤ × ℤ × ℤ)
    (hin : ∀ r : ℤ, 2 ≤ r →
      IsZero ((SynAdamsSS Syn X).Page 2
        (k - (SynAdamsSS Syn X).diffDeg r))) :
    ∀ n : WithTop ℕ, ((SynAdamsSS Syn X).ssData k).B n =
      ((SynAdamsSS Syn X).ssData k).B 0 := by
  let D := (SynAdamsSS Syn X).ssData k
  have hfinite : ∀ n : ℕ, D.B ↑n = D.B 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hd : (SynAdamsSS Syn X).d (2 + n)
          (k - (SynAdamsSS Syn X).diffDeg (2 + n)) = 0 :=
        (synAdams_page_isZero_of_e2 X _ _ (hin _ (by omega))).eq_of_src _ _
      exact (synAdams_boundaries_succ_of_zero X n k hd).trans ih
  intro n
  cases n with
  | coe n => exact hfinite n
  | top =>
      exact le_antisymm (D.B_top_least _ (fun n => (hfinite n).le))
        (D.B_mono le_top)

/-- If E₂ vanishes at all possible incoming sources and outgoing targets
of one degree, that degree is already stable at E₂. Other degrees may
have arbitrarily late differentials. -/
noncomputable def synAdams_eInftyIso_e2_of_isolated (X : Syn)
    (k : ℤ × ℤ × ℤ)
    (hin : ∀ r : ℤ, 2 ≤ r →
      IsZero ((SynAdamsSS Syn X).Page 2
        (k - (SynAdamsSS Syn X).diffDeg r)))
    (hout : ∀ r : ℤ, 2 ≤ r →
      IsZero ((SynAdamsSS Syn X).Page 2
        (k + (SynAdamsSS Syn X).diffDeg r))) :
    ((SynAdamsSS Syn X).ssData k).eInfty ≅ (SynAdamsSS Syn X).Page 2 k := by
  let D := (SynAdamsSS Syn X).ssData k
  have hfinite : ∀ n : ℕ, D.Z ↑n = D.Z 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hd : (SynAdamsSS Syn X).d (2 + n) k = 0 :=
        (synAdams_page_isZero_of_e2 X _ _ (hout _ (by omega))).eq_of_tgt _ _
      exact (synAdams_cycles_succ_of_zero X n k hd).trans ih
  have hZ : D.Z ⊤ = D.Z 0 :=
    le_antisymm (D.Z_anti le_top)
      (D.Z_top_greatest _ (fun n => (hfinite n).ge))
  have hB := synAdams_boundaries_eq_initial_of_e2_incoming X k hin ⊤
  have hp : D.page ⊤ = D.page 0 :=
    subquotient_eq_of_eq (D.B_le_Z ⊤) (D.B_le_Z 0) hB hZ
  exact eqToIso hp ≪≫ eqToIso (by
    simp only [SpectralSequence.Page, synAdamsSS_r0, sub_self, Int.toNat_zero]
    rfl)

namespace SynAdamsConvergenceData

variable {X : Syn} (A : SynAdamsConvergenceData X)

/-- Project an actual filtered homotopy class to the associated graded.
This uses the supplied identification with the actual Hom subgroup. -/
noncomputable def homotopyGradedProjection (s : ℤ) (degree : ℤ × ℤ) :
    synAdamsFiltration Syn X degree.1 degree.2 s →+
      ↑(A.filtration.associatedGraded s degree) :=
  (A.filtration.toAssociatedGraded s degree).hom.comp
    (A.filtrationEquiv s degree).symm.toAddMonoidHom

theorem homotopyGradedProjection_surjective (s : ℤ) (degree : ℤ × ℤ) :
    Function.Surjective (A.homotopyGradedProjection s degree) :=
  ((AddCommGrpCat.epi_iff_surjective
    (A.filtration.toAssociatedGraded s degree)).mp inferInstance).comp
      (A.filtrationEquiv s degree).symm.surjective

/-- The subgroup identifications respect the actual inclusion of the next
filtration layer; this follows from their common inclusion into Hom. -/
theorem filtrationEquiv_inclusion (s : ℤ) (degree : ℤ × ℤ)
    (b : ↑(Subobject.underlying.obj (A.filtration.F (s + 1) degree))) :
    (A.filtrationEquiv s degree
      ((Subobject.ofLE _ _ (A.filtration.mono s degree)).hom b)).val =
        (A.filtrationEquiv (s + 1) degree b).val := by
  rw [← A.filtrationEquiv_comm, ← A.filtrationEquiv_comm]
  exact congrArg (A.abutmentEquiv degree)
    (ConcreteCategory.congr_hom (Subobject.ofLE_arrow (A.filtration.mono s degree)) b)

/-- A filtered actual homotopy class has zero graded class exactly when
it belongs to the next actual filtration subgroup. -/
theorem homotopyGradedProjection_eq_zero_iff (s : ℤ) (degree : ℤ × ℤ)
    (a : synAdamsFiltration Syn X degree.1 degree.2 s) :
    A.homotopyGradedProjection s degree a = 0 ↔
      a.val ∈ synAdamsFiltration Syn X degree.1 degree.2 (s + 1) := by
  let i := Subobject.ofLE (A.filtration.F (s + 1) degree)
    (A.filtration.F s degree) (A.filtration.mono s degree)
  let a' := (A.filtrationEquiv s degree).symm a
  have he : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff _).mp he a' ha
    have hv : (A.filtrationEquiv (s + 1) degree b).val = a.val := by
      rw [← A.filtrationEquiv_inclusion s degree b]
      change (A.filtrationEquiv s degree (i.hom b)).val = a.val
      rw [show i.hom b = a' from hb]
      exact congrArg Subtype.val ((A.filtrationEquiv s degree).apply_symm_apply a)
    exact hv ▸ (A.filtrationEquiv (s + 1) degree b).property
  · intro ha
    let b := (A.filtrationEquiv (s + 1) degree).symm ⟨a.val, ha⟩
    have hb : i.hom b = a' := by
      apply (A.filtrationEquiv s degree).injective
      apply Subtype.ext
      rw [A.filtrationEquiv_inclusion]
      simp only [b, a', AddEquiv.apply_symm_apply]
    change (cokernel.π i).hom a' = 0
    rw [← hb]
    exact ConcreteCategory.congr_hom (cokernel.condition i) b

end SynAdamsConvergenceData

end KIPBase.Synthetic
