/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import KIPBase.SpectralSequence.Commutativity

/-!
# 带过滤平移的过滤复形态射

论文中的稳定页映射不是普通的过滤度零态射。若一个底层映射把
`F^s` 送入 `F^(s+a)`，它的首项在关联分次上把过滤次数 `s`
平移到 `s+a`。本文件把这一点实现为到平移过滤复形的普通态射，
从而复用已有的过滤复形谱序列函子性，而不把平移误装成未移位态射。
-/

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- 把过滤复形的过滤指标平移 `a`；新复形的 `F^s` 是原复形的
`F^(s+a)`，底层分次对象和微分保持不变。 -/
def FilteredComplex.shiftFiltration (FC : FilteredComplex C) (a : ℤ) :
    FilteredComplex C where
  A := FC.A
  d := FC.d
  d_comp_d := FC.d_comp_d
  fil s k := FC.fil (s + a) k
  fil_anti s k := by
    rw [show (s + 1) + a = (s + a) + 1 by abel]
    exact FC.fil_anti (s + a) k
  d_preserves_fil s k := FC.d_preserves_fil (s + a) k

/-- 有界过滤在平移后仍然有界。 -/
def FilteredComplex.IsBounded.shiftFiltration
    {FC : FilteredComplex C} (bnd : FC.IsBounded) (a : ℤ) :
    (FC.shiftFiltration a).IsBounded where
  lo k := bnd.lo k - a
  hi k := bnd.hi k - a
  lo_le_hi k := sub_le_sub_right (bnd.lo_le_hi k) a
  boundedBelow k s hs := by
    change FC.fil (s + a) k = ⊤
    exact bnd.boundedBelow k (s + a) (by omega)
  boundedAbove k s hs := by
    change FC.fil (s + a) k = ⊥
    exact bnd.boundedAbove k (s + a) (by omega)

/-- 平移过滤复形的关联分次对象典范同构于原复形在平移后过滤次数的
关联分次对象。这里使用同一过滤层的子对象同构，而不依赖脆弱的定义相等。 -/
noncomputable def FilteredComplex.shiftFiltrationAssocGradedIso
    (FC : FilteredComplex C) (a s k : ℤ) :
    (FC.shiftFiltration a).assocGraded s k ≅ FC.assocGraded (s + a) k := by
  let P := FC.fil ((s + 1) + a) k
  let P' := FC.fil ((s + a) + 1) k
  let Q := FC.fil (s + a) k
  have hP : P = P' := congrArg (fun q => FC.fil q k) (by abel)
  let i := Subobject.ofLE P Q ((FC.shiftFiltration a).fil_anti s k)
  let i' := Subobject.ofLE P' Q (FC.fil_anti (s + a) k)
  exact cokernel.mapIso i i' (Subobject.isoOfEq P P' hP)
    (Iso.refl (Subobject.underlying.obj Q)) (by
      apply (cancel_mono Q.arrow).mp
      simp only [Category.assoc, Subobject.ofLE_arrow, Iso.refl_hom,
        Category.comp_id, Subobject.isoOfEq_hom, i, i'])

/-- 关联分次同构与两边的过滤商投影相容。 -/
theorem FilteredComplex.shiftFiltrationAssocGradedIso_hom
    (FC : FilteredComplex C) (a s k : ℤ) :
    (FC.shiftFiltration a).filToAssocGraded s k ≫
        (FC.shiftFiltrationAssocGradedIso a s k).hom =
      FC.filToAssocGraded (s + a) k := by
  change cokernel.π (Subobject.ofLE (FC.fil ((s + 1) + a) k)
      (FC.fil (s + a) k) _) ≫
      (FC.shiftFiltrationAssocGradedIso a s k).hom =
    cokernel.π (Subobject.ofLE (FC.fil ((s + a) + 1) k)
      (FC.fil (s + a) k) _)
  unfold FilteredComplex.shiftFiltrationAssocGradedIso
  dsimp only
  rw [cokernel.mapIso_hom]
  erw [cokernel.π_desc]
  simp

/- 同构后合成的像子对象等于原像沿同构的推前。 -/
private theorem mapIso_imageSubobject_shift {X Y Z : C}
    (f : X ⟶ Y) (e : Y ≅ Z) :
    (Subobject.map e.hom).obj (imageSubobject f) =
      imageSubobject (f ≫ e.hom) := by
  rw [← Subobject.mk_arrow (imageSubobject f), Subobject.map_mk,
    ← Subobject.mk_arrow (imageSubobject (f ≫ e.hom))]
  exact Subobject.mk_eq_mk_of_comm _ _ (imageSubobjectCompIso f e.hom).symm
    (imageSubobjectCompIso_inv_arrow f e.hom)

/- 后合一个同构不改变核子对象。 -/
private theorem kernelSubobject_eq_of_comp_iso_shift {X Y Z : C}
    (f : X ⟶ Y) (e : Y ≅ Z) :
    kernelSubobject (f ≫ e.hom) = kernelSubobject f :=
  kernelSubobject_comp_mono f e.hom

/- 两个相等子对象的底层箭头余核之间的典范同构。 -/
private noncomputable def cokernelArrowIsoOfEqShift
    {X : C} (P Q : Subobject X) (h : P = Q) :
    cokernel P.arrow ≅ cokernel Q.arrow :=
  cokernel.mapIso P.arrow Q.arrow (Subobject.isoOfEq P Q h) (Iso.refl X) (by
    simp [Subobject.isoOfEq_hom])

/- 上一余核同构与余核投影相容。 -/
private theorem cokernelArrowIsoOfEqShift_hom
    {X : C} (P Q : Subobject X) (h : P = Q) :
    cokernel.π P.arrow ≫ (cokernelArrowIsoOfEqShift P Q h).hom =
      cokernel.π Q.arrow := by
  unfold cokernelArrowIsoOfEqShift
  rw [cokernel.mapIso_hom]
  erw [cokernel.π_desc]
  simp

/-- 平移过滤复形的循环子对象在关联分次同构下恰好对应原复形中
平移后过滤次数的循环子对象。 -/
theorem FilteredComplex.shiftFiltration_cycleSubobject
    (FC : FilteredComplex C) (a s k : ℤ) (r : WithTop ℕ) :
    (Subobject.mapIsoToOrderIso (FC.shiftFiltrationAssocGradedIso a s k))
        ((FC.shiftFiltration a).cycleSubobject s k r) =
      FC.cycleSubobject (s + a) k r := by
  cases r with
  | top =>
      simp only [FilteredComplex.cycleSubobject]
      dsimp only [FilteredComplex.shiftFiltration]
      change (Subobject.map (FC.shiftFiltrationAssocGradedIso a s k).hom).obj
          (imageSubobject
            ((kernelSubobject (((FC.shiftFiltration a).fil s k).arrow ≫
              (FC.shiftFiltration a).d k)).arrow ≫
                (FC.shiftFiltration a).filToAssocGraded s k)) = _
      rw [mapIso_imageSubobject_shift]
      let f := (FC.fil (s + a) k).arrow ≫ FC.d k
      have hcomp :
          ((kernelSubobject f).arrow ≫
              (FC.shiftFiltration a).filToAssocGraded s k) ≫
                (FC.shiftFiltrationAssocGradedIso a s k).hom =
            (kernelSubobject f).arrow ≫
              FC.filToAssocGraded (s + a) k := by
        calc
          ((kernelSubobject f).arrow ≫
              (FC.shiftFiltration a).filToAssocGraded s k) ≫
                (FC.shiftFiltrationAssocGradedIso a s k).hom =
              (kernelSubobject f).arrow ≫
                ((FC.shiftFiltration a).filToAssocGraded s k ≫
                  (FC.shiftFiltrationAssocGradedIso a s k).hom) :=
            Category.assoc _ _ _
          _ = (kernelSubobject f).arrow ≫
              FC.filToAssocGraded (s + a) k := congrArg
            (fun q => (kernelSubobject f).arrow ≫ q)
            (FC.shiftFiltrationAssocGradedIso_hom a s k)
      simpa only [f, FilteredComplex.shiftFiltration] using congrArg
        (fun z : Subobject.underlying.obj (kernelSubobject f) ⟶
          FC.assocGraded (s + a) k => imageSubobject z) hcomp
  | coe n =>
      simp only [FilteredComplex.cycleSubobject]
      dsimp only [FilteredComplex.shiftFiltration]
      let P := FC.fil ((s + (n : ℤ)) + a) (k - 1)
      let Q := FC.fil ((s + a) + (n : ℤ)) (k - 1)
      have hPQ : P = Q := congrArg (fun q => FC.fil q (k - 1)) (by abel)
      let eQ := cokernelArrowIsoOfEqShift P Q hPQ
      let fS := (FC.fil (s + a) k).arrow ≫ FC.d k ≫
          cokernel.π (FC.fil ((s + (n : ℤ)) + a) (k - 1)).arrow
      let fT := (FC.fil (s + a) k).arrow ≫ FC.d k ≫
        cokernel.π (FC.fil ((s + a) + (n : ℤ)) (k - 1)).arrow
      have hf : fS ≫ eQ.hom = fT := by
        dsimp only [fS, fT, eQ, P, Q]
        simpa only [Category.assoc] using congrArg
          (fun q => (FC.fil (s + a) k).arrow ≫ FC.d k ≫ q)
          (cokernelArrowIsoOfEqShift_hom
            (FC.fil ((s + (n : ℤ)) + a) (k - 1))
            (FC.fil ((s + a) + (n : ℤ)) (k - 1)) hPQ)
      change (Subobject.map (FC.shiftFiltrationAssocGradedIso a s k).hom).obj
          (imageSubobject ((kernelSubobject fS).arrow ≫
            (FC.shiftFiltration a).filToAssocGraded s k)) =
        imageSubobject ((kernelSubobject fT).arrow ≫
          FC.filToAssocGraded (s + a) k)
      rw [mapIso_imageSubobject_shift]
      have hker : kernelSubobject fS = kernelSubobject fT := by
        calc
          kernelSubobject fS = kernelSubobject (fS ≫ eQ.hom) :=
            (kernelSubobject_eq_of_comp_iso_shift fS eQ).symm
          _ = kernelSubobject fT := congrArg
            (fun z : Subobject.underlying.obj (FC.fil (s + a) k) ⟶
              cokernel Q.arrow => kernelSubobject z) hf
      have hcomp :
          ((kernelSubobject fS).arrow ≫
              (FC.shiftFiltration a).filToAssocGraded s k) ≫
                (FC.shiftFiltrationAssocGradedIso a s k).hom =
            (kernelSubobject fS).arrow ≫
              FC.filToAssocGraded (s + a) k := by
        calc
          ((kernelSubobject fS).arrow ≫
              (FC.shiftFiltration a).filToAssocGraded s k) ≫
                (FC.shiftFiltrationAssocGradedIso a s k).hom =
              (kernelSubobject fS).arrow ≫
                ((FC.shiftFiltration a).filToAssocGraded s k ≫
                  (FC.shiftFiltrationAssocGradedIso a s k).hom) :=
            Category.assoc _ _ _
          _ = (kernelSubobject fS).arrow ≫
              FC.filToAssocGraded (s + a) k := congrArg
            (fun q => (kernelSubobject fS).arrow ≫ q)
            (FC.shiftFiltrationAssocGradedIso_hom a s k)
      rw [congrArg
        (fun z : Subobject.underlying.obj (kernelSubobject fS) ⟶
          FC.assocGraded (s + a) k => imageSubobject z) hcomp]
      rw [hker]

/-- 平移过滤复形的边缘子对象在关联分次同构下恰好对应原复形中
平移后过滤次数的边缘子对象。 -/
theorem FilteredComplex.shiftFiltration_boundarySubobject
    (FC : FilteredComplex C) (a s k : ℤ) (r : WithTop ℕ) :
    (Subobject.mapIsoToOrderIso (FC.shiftFiltrationAssocGradedIso a s k))
        ((FC.shiftFiltration a).boundarySubobject s k r) =
      FC.boundarySubobject (s + a) k r := by
  cases r with
  | top =>
      simp only [FilteredComplex.boundarySubobject]
      dsimp only [FilteredComplex.shiftFiltration, FilteredComplex.dToK]
      let I := imageSubobject (FC.d k.succ ≫
          eqToHom (congr_arg FC.A (show k + 1 - 1 = k by omega))) ⊓
        FC.fil (s + a) k
      let oI := Subobject.ofLE I (FC.fil (s + a) k) inf_le_right
      change (Subobject.map (FC.shiftFiltrationAssocGradedIso a s k).hom).obj
          (imageSubobject (oI ≫
            (FC.shiftFiltration a).filToAssocGraded s k)) =
        imageSubobject (oI ≫ FC.filToAssocGraded (s + a) k)
      rw [mapIso_imageSubobject_shift]
      have hcomp :
          (oI ≫ (FC.shiftFiltration a).filToAssocGraded s k) ≫
              (FC.shiftFiltrationAssocGradedIso a s k).hom =
            oI ≫ FC.filToAssocGraded (s + a) k := by
        calc
          (oI ≫ (FC.shiftFiltration a).filToAssocGraded s k) ≫
              (FC.shiftFiltrationAssocGradedIso a s k).hom =
              oI ≫ ((FC.shiftFiltration a).filToAssocGraded s k ≫
                (FC.shiftFiltrationAssocGradedIso a s k).hom) :=
            Category.assoc _ _ _
          _ = oI ≫ FC.filToAssocGraded (s + a) k := congrArg
            (fun q => oI ≫ q)
            (FC.shiftFiltrationAssocGradedIso_hom a s k)
      exact congrArg
        (fun z : Subobject.underlying.obj I ⟶ FC.assocGraded (s + a) k =>
          imageSubobject z) hcomp
  | coe n =>
      simp only [FilteredComplex.boundarySubobject]
      dsimp only [FilteredComplex.shiftFiltration, FilteredComplex.dToK]
      let P := FC.fil ((s - (n : ℤ) + 1) + a) (k + 1)
      let Q := FC.fil ((s + a) - (n : ℤ) + 1) (k + 1)
      have hPQ : P = Q := congrArg (fun q => FC.fil q (k + 1)) (by abel)
      let dK := FC.d (k + 1) ≫
        eqToHom (congr_arg FC.A (show k + 1 - 1 = k by omega))
      let gS := P.arrow ≫ dK
      let gT := Q.arrow ≫ dK
      have hg : gS = (Subobject.isoOfEq P Q hPQ).hom ≫ gT := by
        change P.arrow ≫ dK =
          (Subobject.isoOfEq P Q hPQ).hom ≫ (Q.arrow ≫ dK)
        have he : (Subobject.isoOfEq P Q hPQ).hom ≫ Q.arrow = P.arrow := by
          rw [Subobject.isoOfEq_hom, Subobject.ofLE_arrow]
        calc
          P.arrow ≫ dK =
              ((Subobject.isoOfEq P Q hPQ).hom ≫ Q.arrow) ≫ dK :=
            congrArg (fun q => q ≫ dK) he.symm
          _ = (Subobject.isoOfEq P Q hPQ).hom ≫ (Q.arrow ≫ dK) :=
            Category.assoc _ _ _
      have himg : imageSubobject gS = imageSubobject gT := by
        rw [hg, imageSubobject_iso_comp]
      let IS := imageSubobject gS ⊓ FC.fil (s + a) k
      let IT := imageSubobject gT ⊓ FC.fil (s + a) k
      have hI : IS = IT := congrArg
        (fun J : Subobject (FC.A k) => J ⊓ FC.fil (s + a) k) himg
      let oIS := Subobject.ofLE IS (FC.fil (s + a) k) inf_le_right
      let oIT := Subobject.ofLE IT (FC.fil (s + a) k) inf_le_right
      change (Subobject.map (FC.shiftFiltrationAssocGradedIso a s k).hom).obj
          (imageSubobject (oIS ≫
            (FC.shiftFiltration a).filToAssocGraded s k)) =
        imageSubobject (oIT ≫ FC.filToAssocGraded (s + a) k)
      rw [mapIso_imageSubobject_shift]
      have hleft :
          (oIS ≫ (FC.shiftFiltration a).filToAssocGraded s k) ≫
              (FC.shiftFiltrationAssocGradedIso a s k).hom =
            oIS ≫ FC.filToAssocGraded (s + a) k := by
        calc
          (oIS ≫ (FC.shiftFiltration a).filToAssocGraded s k) ≫
              (FC.shiftFiltrationAssocGradedIso a s k).hom =
              oIS ≫ ((FC.shiftFiltration a).filToAssocGraded s k ≫
                (FC.shiftFiltrationAssocGradedIso a s k).hom) :=
            Category.assoc _ _ _
          _ = oIS ≫ FC.filToAssocGraded (s + a) k := congrArg
            (fun q => oIS ≫ q)
            (FC.shiftFiltrationAssocGradedIso_hom a s k)
      calc
        imageSubobject
            ((oIS ≫ (FC.shiftFiltration a).filToAssocGraded s k) ≫
              (FC.shiftFiltrationAssocGradedIso a s k).hom) =
            imageSubobject (oIS ≫ FC.filToAssocGraded (s + a) k) :=
          congrArg
            (fun z : Subobject.underlying.obj IS ⟶
              FC.assocGraded (s + a) k => imageSubobject z) hleft
        _ = imageSubobject (oIT ≫ FC.filToAssocGraded (s + a) k) := by
          let eI := Subobject.isoOfEq IS IT hI
          have ho : oIS = eI.hom ≫ oIT := by
            apply (cancel_mono (FC.fil (s + a) k).arrow).mp
            dsimp only [oIS, oIT, eI]
            rw [Subobject.ofLE_arrow, Category.assoc,
              Subobject.ofLE_arrow, Subobject.isoOfEq_hom,
              Subobject.ofLE_arrow]
          rw [ho, Category.assoc, imageSubobject_iso_comp]

/- 子对象在环境同构下对应时，其箭头后接环境同构会穿过目标子对象。 -/
private theorem subobject_factors_of_mapIso_eq_shift {X Y : C} (e : X ≅ Y)
    (P : Subobject X) (Q : Subobject Y)
    (h : (Subobject.mapIsoToOrderIso e) P = Q) :
    Q.Factors (P.arrow ≫ e.hom) := by
  rw [← h]
  have hm : Subobject.mk (P.arrow ≫ e.hom) =
      (Subobject.mapIsoToOrderIso e) P := by
    calc
      Subobject.mk (P.arrow ≫ e.hom) =
          (Subobject.map e.hom).obj (Subobject.mk P.arrow) :=
        (Subobject.map_mk P.arrow e.hom).symm
      _ = (Subobject.map e.hom).obj P := by rw [Subobject.mk_arrow]
  rw [← hm]
  exact Subobject.mk_factors_self (P.arrow ≫ e.hom)

/-- 平移过滤复形产生的 `SSData` 族。 -/
private noncomputable abbrev FilteredComplex.shiftedSSDataFamily
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (a : ℤ) :
    ℤ × ℤ → SSData C := fun sk =>
  (FC.shiftFiltration a).toSSData (bnd.shiftFiltration a) sk.1 sk.2

/-- 原谱序列按过滤次数平移后的 `SSData` 族。 -/
private noncomputable abbrev FilteredComplex.reindexedSSDataFamily
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (a : ℤ) :
    ℤ × ℤ → SSData C := fun sk =>
  FC.toSSData bnd (sk.1 + a) sk.2

/-- 平移过滤复形的 `SSData` 到原复形重指标 `SSData` 的规范态射。 -/
noncomputable def FilteredComplex.shiftedSSDataForward
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (a : ℤ) :
    SSDataMorphism (ℤ × ℤ) (FC.shiftedSSDataFamily bnd a)
      (FC.reindexedSSDataFamily bnd a) where
  φ := fun sk => FC.shiftFiltrationAssocGradedIso a sk.1 sk.2 |>.hom
  preserves_Z := by
    rintro ⟨s, k⟩ r
    let e := FC.shiftFiltrationAssocGradedIso a s k
    let P := ((FC.shiftFiltration a).toSSData
      (bnd.shiftFiltration a) s k).Z r
    let Q := (FC.toSSData bnd (s + a) k).Z r
    have hmap : (Subobject.mapIsoToOrderIso e) P = Q := by
      exact FC.shiftFiltration_cycleSubobject a s k r
    have hfac : Q.Factors (P.arrow ≫ e.hom) :=
      subobject_factors_of_mapIso_eq_shift e P Q hmap
    exact ⟨Q.factorThru (P.arrow ≫ e.hom) hfac,
      Q.factorThru_arrow _ hfac⟩
  preserves_B := by
    rintro ⟨s, k⟩ r
    let e := FC.shiftFiltrationAssocGradedIso a s k
    let P := ((FC.shiftFiltration a).toSSData
      (bnd.shiftFiltration a) s k).B r
    let Q := (FC.toSSData bnd (s + a) k).B r
    have hmap : (Subobject.mapIsoToOrderIso e) P = Q := by
      exact FC.shiftFiltration_boundarySubobject a s k r
    have hfac : Q.Factors (P.arrow ≫ e.hom) :=
      subobject_factors_of_mapIso_eq_shift e P Q hmap
    exact ⟨Q.factorThru (P.arrow ≫ e.hom) hfac,
      Q.factorThru_arrow _ hfac⟩

/-- 原复形重指标 `SSData` 到平移过滤复形 `SSData` 的逆规范态射。 -/
noncomputable def FilteredComplex.shiftedSSDataBackward
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (a : ℤ) :
    SSDataMorphism (ℤ × ℤ) (FC.reindexedSSDataFamily bnd a)
      (FC.shiftedSSDataFamily bnd a) where
  φ := fun sk => FC.shiftFiltrationAssocGradedIso a sk.1 sk.2 |>.inv
  preserves_Z := by
    rintro ⟨s, k⟩ r
    let e := FC.shiftFiltrationAssocGradedIso a s k
    let P := (FC.toSSData bnd (s + a) k).Z r
    let Q := ((FC.shiftFiltration a).toSSData
      (bnd.shiftFiltration a) s k).Z r
    have hback : (Subobject.mapIsoToOrderIso e.symm) P = Q := by
      change (Subobject.mapIsoToOrderIso e.symm)
          (FC.cycleSubobject (s + a) k r) =
        (FC.shiftFiltration a).cycleSubobject s k r
      rw [← FC.shiftFiltration_cycleSubobject a s k r]
      exact (Subobject.mapIsoToOrderIso e).symm_apply_apply _
    have hfac : Q.Factors (P.arrow ≫ e.inv) :=
      subobject_factors_of_mapIso_eq_shift e.symm P Q hback
    exact ⟨Q.factorThru (P.arrow ≫ e.inv) hfac,
      Q.factorThru_arrow _ hfac⟩
  preserves_B := by
    rintro ⟨s, k⟩ r
    let e := FC.shiftFiltrationAssocGradedIso a s k
    let P := (FC.toSSData bnd (s + a) k).B r
    let Q := ((FC.shiftFiltration a).toSSData
      (bnd.shiftFiltration a) s k).B r
    have hback : (Subobject.mapIsoToOrderIso e.symm) P = Q := by
      change (Subobject.mapIsoToOrderIso e.symm)
          (FC.boundarySubobject (s + a) k r) =
        (FC.shiftFiltration a).boundarySubobject s k r
      rw [← FC.shiftFiltration_boundarySubobject a s k r]
      exact (Subobject.mapIsoToOrderIso e).symm_apply_apply _
    have hfac : Q.Factors (P.arrow ≫ e.inv) :=
      subobject_factors_of_mapIso_eq_shift e.symm P Q hback
    exact ⟨Q.factorThru (P.arrow ≫ e.inv) hfac,
      Q.factorThru_arrow _ hfac⟩

/- `SSData` 族上的恒等态射。 -/
private noncomputable def ssDataMorphismIdShift (D : ℤ × ℤ → SSData C) :
    SSDataMorphism (ℤ × ℤ) D D where
  φ := fun _ => 𝟙 _
  preserves_Z := fun _ _ => ⟨𝟙 _, by simp⟩
  preserves_B := fun _ _ => ⟨𝟙 _, by simp⟩

/-- 平移过滤复形的任意 `Z/B` 页与原复形重指标页之间的规范同构。 -/
noncomputable def FilteredComplex.shiftFiltrationPageIso
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (a : ℤ)
    (sk : ℤ × ℤ) (r : WithTop ℕ) :
    ((FC.shiftedSSDataFamily bnd a) sk).page r ≅
      ((FC.reindexedSSDataFamily bnd a) sk).page r where
  hom := (FC.shiftedSSDataForward bnd a).pageMap sk r
  inv := (FC.shiftedSSDataBackward bnd a).pageMap sk r
  hom_inv_id := by
    rw [← SSDataMorphism.pageMap_eq_comp
      (FC.shiftedSSDataForward bnd a) (FC.shiftedSSDataBackward bnd a)
      (ssDataMorphismIdShift (FC.shiftedSSDataFamily bnd a)) sk r (by
        rcases sk with ⟨s, k⟩
        exact (FC.shiftFiltrationAssocGradedIso a s k).hom_inv_id.symm)]
    exact SSDataMorphism.pageMap_eq_id _ sk r rfl
  inv_hom_id := by
    rw [← SSDataMorphism.pageMap_eq_comp
      (FC.shiftedSSDataBackward bnd a) (FC.shiftedSSDataForward bnd a)
      (ssDataMorphismIdShift (FC.reindexedSSDataFamily bnd a)) sk r (by
        rcases sk with ⟨s, k⟩
        exact (FC.shiftFiltrationAssocGradedIso a s k).inv_hom_id.symm)]
    exact SSDataMorphism.pageMap_eq_id _ sk r rfl

/-- 在整数显示页上，平移过滤复形的页对象规范同构于原谱序列在
过滤次数平移后的页对象。 -/
noncomputable def FilteredComplex.shiftFiltrationSpectralSequencePageIso
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (a r : ℤ)
    (sk : ℤ × ℤ) :
    ((FC.shiftFiltration a).toSpectralSequence
      (bnd.shiftFiltration a)).Page r sk ≅
      (FC.toSpectralSequence bnd).Page r (sk.1 + a, sk.2) := by
  change ((FC.shiftedSSDataFamily bnd a) sk).page
      ((r - 0).toNat : WithTop ℕ) ≅
    ((FC.reindexedSSDataFamily bnd a) sk).page
      ((r - 0).toNat : WithTop ℕ)
  exact FC.shiftFiltrationPageIso bnd a sk ((r - 0).toNat : WithTop ℕ)

/-- 过滤次数平移保持过滤复形谱序列的起始页与微分次数，并满足
仿射重指标所需的次数相容式。 -/
theorem FilteredComplex.shiftFiltration_degree_compat
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (a r : ℤ)
    (sk : ℤ × ℤ) :
    ((sk.1 + a, sk.2) + (FC.toSpectralSequence bnd).diffDeg r) =
      ((sk + ((FC.shiftFiltration a).toSpectralSequence
        (bnd.shiftFiltration a)).diffDeg r).1 + a,
        (sk + ((FC.shiftFiltration a).toSpectralSequence
          (bnd.shiftFiltration a)).diffDeg r).2) := by
  change (sk.1 + a + r, sk.2 + -1) =
    (sk.1 + r + a, sk.2 + -1)
  congr 1 <;> abel

/-- 过滤次数为 `a` 的过滤复形态射。它在底层仍是次数零链映射，
但把源的 `F^s` 送入目标的 `F^(s+a)`。 -/
structure ShiftedFilteredComplexMorphism
    (FC₁ FC₂ : FilteredComplex C) (a : ℤ) where
  /-- 底层分次链映射。 -/
  f : ∀ k, FC₁.A k ⟶ FC₂.A k
  /-- 与复形微分交换。 -/
  comm_d : ∀ k, f k ≫ FC₂.d k = FC₁.d k ≫ f (k - 1)
  /-- 映射把第 `s` 层过滤送入目标的第 `s+a` 层。 -/
  filt_compat : ∀ s k,
    ∃ (φ : Subobject.underlying.obj (FC₁.fil s k) ⟶
        Subobject.underlying.obj (FC₂.fil (s + a) k)),
      φ ≫ (FC₂.fil (s + a) k).arrow = (FC₁.fil s k).arrow ≫ f k

/-- 带过滤平移的态射等价地是到平移过滤复形的普通态射。 -/
def ShiftedFilteredComplexMorphism.toFilteredComplexMorphism
    {FC₁ FC₂ : FilteredComplex C} {a : ℤ}
    (f : ShiftedFilteredComplexMorphism FC₁ FC₂ a) :
    FilteredComplexMorphism FC₁ (FC₂.shiftFiltration a) where
  f := f.f
  comm_d := f.comm_d
  filt_compat := f.filt_compat

/-- 带过滤平移的有界过滤复形态射诱导到平移目标谱序列的态射。
目标过滤复形显式保留在类型中，防止把过滤平移错误地当成恒等重指标。 -/
noncomputable def ShiftedFilteredComplexMorphism.toSpectralSequenceMorphism
    {FC₁ FC₂ : FilteredComplex C} {a : ℤ}
    (f : ShiftedFilteredComplexMorphism FC₁ FC₂ a)
    (bnd₁ : FC₁.IsBounded) (bnd₂ : FC₂.IsBounded) :
    FC₁.toSpectralSequence bnd₁ ⟶
      (FC₂.shiftFiltration a).toSpectralSequence (bnd₂.shiftFiltration a) :=
  FilteredComplexMorphism.toSpectralSequenceMorphism
    (X := ⟨FC₁, bnd₁⟩)
    (Y := ⟨FC₂.shiftFiltration a, bnd₂.shiftFiltration a⟩)
    f.toFilteredComplexMorphism

/-- 带过滤平移的链映射在每个显示页上给出到原目标谱序列重指标页的
规范映射。先使用到平移过滤目标的谱序列态射，再使用逐页平移同构。 -/
noncomputable def ShiftedFilteredComplexMorphism.reindexedPageMap
    {FC₁ FC₂ : FilteredComplex C} {a : ℤ}
    (f : ShiftedFilteredComplexMorphism FC₁ FC₂ a)
    (bnd₁ : FC₁.IsBounded) (bnd₂ : FC₂.IsBounded)
    (r : ℤ) (sk : ℤ × ℤ) :
    (FC₁.toSpectralSequence bnd₁).Page r sk ⟶
      (FC₂.toSpectralSequence bnd₂).Page r (sk.1 + a, sk.2) := by
  let F := f.toSpectralSequenceMorphism bnd₁ bnd₂
  let n : WithTop ℕ := ((r - 0).toNat : ℕ)
  exact F.pageMap sk n ≫
    (FC₂.shiftFiltrationSpectralSequencePageIso bnd₂ a r sk).hom

/-- 交换方块的两条竖边共同具有过滤次数 `a`：左边 `p` 和右边 `q`
分别把各自的第 `s` 层送入第 `s+a` 层。 -/
structure HomotopyCommSquare.FiltrationShiftData
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ E₃ E₄ : SpectralSequence C ι}
    {A₁ A₂ A₃ A₄ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (a : ℤ) : Prop where
  /-- 左竖边把过滤提高 `a`。 -/
  left : ∀ (s : ℤ) (t : ω),
    ∃ φ, φ ≫ (F₃.F (s + a) t).arrow =
      (F₁.F s t).arrow ≫ sq.cmp.aMap t
  /-- 右竖边把过滤提高 `a`。 -/
  right : ∀ (s : ℤ) (t : ω),
    ∃ φ, φ ≫ (F₄.F (s + a) t).arrow =
      (F₂.F s t).arrow ≫ sq.cmq.aMap t

/-- 具有过滤次数 `a` 的交换方块给出从 `f` 的两项过滤复形到
`g` 的平移过滤复形的链映射。次数 `1` 使用 `p`，次数 `0` 使用 `q`。 -/
noncomputable def HomotopyCommSquare.shiftedESSFilteredComplexMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ E₃ E₄ : SpectralSequence C ι}
    {A₁ A₂ A₃ A₄ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (a : ℤ) (ha : sq.FiltrationShiftData a) (t : ω) :
    ShiftedFilteredComplexMorphism (sq.extf.complex t) (sq.extg.complex t) a := by
  let g : FilteredComplexMorphism (sq.extf.complex t) (sq.extg.complex t) :=
    underlyingComplexMorphism
    sq.cmf.aMap sq.cmf.filtration_compat
    sq.cmg.aMap sq.cmg.filtration_compat
    sq.cmp.aMap sq.cmq.aMap (fun t => (sq.abutment_comm t).symm)
    sq.cmp.filtration_compat sq.cmq.filtration_compat t
  refine { f := g.f, comm_d := g.comm_d, filt_compat := ?_ }
  · intro s k
    by_cases h₁ : k = 1
    · subst k
      simpa [g, underlyingComplexMorphism, BoundedExtensionSS.complex, underlyingComplex,
        twoTermFil, twoTermObj] using ha.left s t
    · by_cases h₀ : k = 0
      · subst k
        simpa [g, underlyingComplexMorphism, BoundedExtensionSS.complex, underlyingComplex,
          twoTermFil, twoTermObj] using ha.right s t
      · obtain ⟨φ, hφ⟩ := g.filt_compat s k
        have heq : (sq.extg.complex t).fil s k =
            (sq.extg.complex t).fil (s + a) k := by
          simp [BoundedExtensionSS.complex, underlyingComplex,
            twoTermFil, h₁, h₀]
        refine ⟨φ ≫ Subobject.ofLE _ _ (le_of_eq heq), ?_⟩
        rw [Category.assoc, Subobject.ofLE_arrow]
        exact hφ

/-- 上一条带平移链映射诱导谱序列态射。它是稳定页映射的严格核心。
平移页同构与有限页微分的相容性在 `ShiftedDifferential`
中证明，并在 `Blueprint` 中打包为重指标谱序列态射。 -/
noncomputable def HomotopyCommSquare.shiftedESSSpectralSequenceMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ E₃ E₄ : SpectralSequence C ι}
    {A₁ A₂ A₃ A₄ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (a : ℤ) (ha : sq.FiltrationShiftData a) (t : ω) :
    (sq.extf.complex t).toSpectralSequence (sq.extf.bounded t) ⟶
      ((sq.extg.complex t).shiftFiltration a).toSpectralSequence
        ((sq.extg.bounded t).shiftFiltration a) :=
  (sq.shiftedESSFilteredComplexMorphism a ha t).toSpectralSequenceMorphism
    (sq.extf.bounded t) (sq.extg.bounded t)

/-- 具有过滤次数 `a` 的交换方块在每个页、每个双次数上给出从
`f`-ESS 到原 `g`-ESS 的过滤重指标页映射。目标双次数是
`(s,k) ↦ (s+a,k)`；这一定义已经使用真正的逐页 `Z/B` 同构。 -/
noncomputable def HomotopyCommSquare.shiftedESSReindexedPageMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] {ω : Type w}
    {E₁ E₂ E₃ E₄ : SpectralSequence C ι}
    {A₁ A₂ A₃ A₄ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₃ : Filtration A₃} {F₄ : Filtration A₄}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃} {conv₄ : Convergence E₄ A₄ F₄}
    (sq : HomotopyCommSquare conv₁ conv₂ conv₃ conv₄)
    (a : ℤ) (ha : sq.FiltrationShiftData a) (t : ω)
    (r : ℤ) (sk : ℤ × ℤ) :
    (sq.extf.ess t).Page r sk ⟶
      (sq.extg.ess t).Page r (sk.1 + a, sk.2) := by
  change ((sq.extf.complex t).toSpectralSequence
      (sq.extf.bounded t)).Page r sk ⟶
    ((sq.extg.complex t).toSpectralSequence
      (sq.extg.bounded t)).Page r (sk.1 + a, sk.2)
  exact (sq.shiftedESSFilteredComplexMorphism a ha t).reindexedPageMap
    (sq.extf.bounded t) (sq.extg.bounded t) r sk

end KIPBase.SpectralSequence
