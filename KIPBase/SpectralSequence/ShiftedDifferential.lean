/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import KIPBase.SpectralSequence.ShiftedMorphism

/-!
# 过滤平移与页微分

本文件证明过滤指标平移所得的规范页同构与每个有限页微分相容。
目标过滤指标 `(s+n)+a` 与 `(s+a)+n` 只在算术上相等，
因此证明显式保留了循环子对象、关联分次和页对象上的依赖型搬运。
-/

namespace KIPBase.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem pageπ_transport (D : ℤ → SSData C)
    {q p : ℤ} (h : q = p) (n : WithTop ℕ) :
    (D q).pageπ n ≫ eqToHom (congrArg (fun x => (D x).page n) h) =
      eqToHom (congrArg
        (fun x => Subobject.underlying.obj ((D x).Z n)) h) ≫
        (D p).pageπ n := by
  subst p
  simp

private theorem subobjectArrow_transport (D : ℤ → SSData C)
    {q p : ℤ} (h : q = p) (n : WithTop ℕ) :
    eqToHom (congrArg
        (fun x => Subobject.underlying.obj ((D x).Z n)) h) ≫
        ((D p).Z n).arrow =
      ((D q).Z n).arrow ≫ eqToHom (congrArg (fun x => (D x).V) h) := by
  subst p
  simp

private theorem filToAssocGraded_transport (FC : FilteredComplex C)
    {q p k : ℤ} (h : q = p) :
    FC.filToAssocGraded q k ≫
        eqToHom (congrArg (fun x => FC.assocGraded x k) h) =
      (Subobject.isoOfEq (FC.fil q k) (FC.fil p k)
        (congrArg (fun x => FC.fil x k) h)).hom ≫
        FC.filToAssocGraded p k := by
  subst p
  simp

/-- 过滤平移的规范页同构与每个有限页微分交换。 -/
theorem FilteredComplex.shiftFiltrationPageIso_comm_pageDifferential
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (a s k : ℤ) (n : ℕ) :
    (FC.shiftFiltrationPageIso bnd a (s, k) n).hom ≫
        FC.pageDifferential bnd (s + a) k n =
      (FC.shiftFiltration a).pageDifferential (bnd.shiftFiltration a) s k n ≫
        (FC.shiftFiltrationPageIso bnd a (s + (n : ℤ), k - 1) n).hom ≫
        eqToHom (congrArg
          (fun q : ℤ => (FC.toSSData bnd q (k - 1)).page (n : WithTop ℕ))
          (show (s + (n : ℤ)) + a = (s + a) + (n : ℤ) by abel)) := by
  classical
  let fS := (FC.fil (s + a) k).arrow ≫ FC.d k ≫
    cokernel.π ((FC.fil ((s + (n : ℤ)) + a) (k - 1)).arrow)
  let fT := (FC.fil (s + a) k).arrow ≫ FC.d k ≫
    cokernel.π ((FC.fil ((s + a) + (n : ℤ)) (k - 1)).arrow)
  let KS := kernelSubobject fS
  let KT := kernelSubobject fT
  let πS : Subobject.underlying.obj (FC.fil (s + a) k) ⟶
      (FC.shiftFiltration a).assocGraded s k :=
    (FC.shiftFiltration a).filToAssocGraded s k
  let πT := FC.filToAssocGraded (s + a) k
  let ZS := imageSubobject (KS.arrow ≫ πS)
  let ZT := imageSubobject (KT.arrow ≫ πT)
  let qS := factorThruImageSubobject (KS.arrow ≫ πS)
  let P := FC.fil ((s + (n : ℤ)) + a) (k - 1)
  let Q := FC.fil ((s + a) + (n : ℤ)) (k - 1)
  have hPQ : P = Q := congrArg (fun q => FC.fil q (k - 1)) (by abel)
  let w := (Subobject.isoOfEq P Q hPQ).hom
  have hwspec : w ≫ Q.arrow = P.arrow := by
    dsimp only [w]
    rw [Subobject.isoOfEq_hom]
    exact Subobject.ofLE_arrow _
  let cokT := cokernel.map P.arrow Q.arrow w (𝟙 _) (by
    simpa only [Category.comp_id] using hwspec.symm)
  have hcokT : cokernel.π P.arrow ≫ cokT = cokernel.π Q.arrow := by
    dsimp only [cokT]
    rw [cokernel.π_desc]
    simp
  have hkernel : (𝟙 _) ≫ fT = fS ≫ cokT := by
    dsimp only [fS, fT]
    simp only [Category.id_comp, Category.assoc]
    rw [hcokT]
  let kerMap := kernelSubobjectMap
    (Arrow.homMk (f := Arrow.mk fS) (g := Arrow.mk fT) (𝟙 _) cokT hkernel)
  have hkerMap : kerMap ≫ KT.arrow = KS.arrow := by
    calc
      kerMap ≫ KT.arrow = KS.arrow ≫ (𝟙 _) :=
        kernelSubobjectMap_arrow _
      _ = KS.arrow := Category.comp_id _
  let qT := kerMap ≫ factorThruImageSubobject (KT.arrow ≫ πT)
  let zmapS : Subobject.underlying.obj ZS ⟶ Subobject.underlying.obj ZT :=
    (FC.shiftedSSDataForward bnd a).preserves_Z
      (s, k) (n : WithTop ℕ) |>.choose
  have hqS : qS ≫ ZS.arrow = KS.arrow ≫ πS := by
    exact imageSubobject_arrow_comp _
  have hqT : qT ≫ ZT.arrow = KS.arrow ≫ πT := by
    dsimp only [qT, ZT]
    rw [Category.assoc, imageSubobject_arrow_comp, ← Category.assoc, hkerMap]
  have hπ : πS ≫ (FC.shiftFiltrationAssocGradedIso a s k).hom = πT := by
    exact FC.shiftFiltrationAssocGradedIso_hom a s k
  have hzmapS : qS ≫ zmapS = qT := by
    apply (cancel_mono ZT.arrow).mp
    have hzspec := (FC.shiftedSSDataForward bnd a).preserves_Z
      (s, k) (n : WithTop ℕ) |>.choose_spec
    change zmapS ≫ ZT.arrow = ZS.arrow ≫
      (FC.shiftFiltrationAssocGradedIso a s k).hom at hzspec
    calc
      (qS ≫ zmapS) ≫ ZT.arrow = qS ≫
          (zmapS ≫ ZT.arrow) := Category.assoc _ _ _
      _ = qS ≫ (ZS.arrow ≫
          (FC.shiftFiltrationAssocGradedIso a s k).hom) := by rw [hzspec]
      _ = (qS ≫ ZS.arrow) ≫
          (FC.shiftFiltrationAssocGradedIso a s k).hom :=
        (Category.assoc _ _ _).symm
      _ = (KS.arrow ≫ πS) ≫
          (FC.shiftFiltrationAssocGradedIso a s k).hom := by rw [hqS]
      _ = KS.arrow ≫ (πS ≫
          (FC.shiftFiltrationAssocGradedIso a s k).hom) := Category.assoc _ _ _
      _ = KS.arrow ≫ πT := by
        exact congrArg (fun z => KS.arrow ≫ z) hπ
      _ = qT ≫ ZT.arrow := hqT.symm
  let vS := Abelian.monoLift P.arrow
    (KS.arrow ≫ (FC.fil (s + a) k).arrow ≫ FC.d k)
    (by simpa only [fS, P, Category.assoc] using kernelSubobject_arrow_comp fS)
  have hvS : vS ≫ P.arrow =
      KS.arrow ≫ (FC.fil (s + a) k).arrow ≫ FC.d k :=
    Abelian.monoLift_comp _ _ _
  let vT := vS ≫ w
  have hvT : kerMap ≫ KT.arrow ≫ (FC.fil (s + a) k).arrow ≫ FC.d k =
      vT ≫ Q.arrow := by
    calc
      kerMap ≫ KT.arrow ≫ (FC.fil (s + a) k).arrow ≫ FC.d k =
          KS.arrow ≫ (FC.fil (s + a) k).arrow ≫ FC.d k := by
            simpa only [Category.assoc] using congrArg
              (fun h => h ≫ (FC.fil (s + a) k).arrow ≫ FC.d k) hkerMap
      _ = vS ≫ P.arrow := hvS.symm
      _ = vS ≫ w ≫ Q.arrow := by
            simpa only [Category.assoc] using congrArg (fun h => vS ≫ h) hwspec.symm
      _ = vT ≫ Q.arrow := by simp only [vT, Category.assoc]
  let gS := P.arrow ≫ FC.d (k - 1) ≫
    cokernel.π ((FC.fil (((s + (n : ℤ)) + (n : ℤ)) + a) (k - 1 - 1)).arrow)
  let gT := Q.arrow ≫ FC.d (k - 1) ≫
    cokernel.π ((FC.fil (((s + a) + (n : ℤ)) + (n : ℤ)) (k - 1 - 1)).arrow)
  have hvgS : vS ≫ gS = 0 := by
    dsimp only [gS]
    calc
      vS ≫ P.arrow ≫ FC.d (k - 1) ≫
          cokernel.π ((FC.fil (((s + (n : ℤ)) + (n : ℤ)) + a)
            (k - 1 - 1)).arrow) =
        (KS.arrow ≫ (FC.fil (s + a) k).arrow ≫ FC.d k) ≫
          FC.d (k - 1) ≫
          cokernel.π ((FC.fil (((s + (n : ℤ)) + (n : ℤ)) + a)
            (k - 1 - 1)).arrow) := by
              simpa only [Category.assoc] using congrArg
                (fun h => h ≫ FC.d (k - 1) ≫
                  cokernel.π ((FC.fil (((s + (n : ℤ)) + (n : ℤ)) + a)
                    (k - 1 - 1)).arrow)) hvS
      _ = 0 := by
        simpa only [Category.assoc, comp_zero, zero_comp] using congrArg
          (fun h => KS.arrow ≫ (FC.fil (s + a) k).arrow ≫ h ≫
            cokernel.π ((FC.fil (((s + (n : ℤ)) + (n : ℤ)) + a)
              (k - 1 - 1)).arrow)) (FC.d_comp_d k)
  have hvgT : vT ≫ gT = 0 := by
    dsimp only [gT]
    calc
      vT ≫ Q.arrow ≫ FC.d (k - 1) ≫
          cokernel.π ((FC.fil (((s + a) + (n : ℤ)) + (n : ℤ))
            (k - 1 - 1)).arrow) =
        (kerMap ≫ KT.arrow ≫ (FC.fil (s + a) k).arrow ≫ FC.d k) ≫
          FC.d (k - 1) ≫
          cokernel.π ((FC.fil (((s + a) + (n : ℤ)) + (n : ℤ))
            (k - 1 - 1)).arrow) := by
              simpa only [Category.assoc] using congrArg
                (fun h => h ≫ FC.d (k - 1) ≫
                  cokernel.π ((FC.fil (((s + a) + (n : ℤ)) + (n : ℤ))
                    (k - 1 - 1)).arrow)) hvT.symm
      _ = 0 := by
        simpa only [Category.assoc, comp_zero, zero_comp] using congrArg
          (fun h => kerMap ≫ KT.arrow ≫ (FC.fil (s + a) k).arrow ≫ h ≫
            cokernel.π ((FC.fil (((s + a) + (n : ℤ)) + (n : ℤ))
              (k - 1 - 1)).arrow)) (FC.d_comp_d k)
  let KS' := kernelSubobject gS
  let KT' := kernelSubobject gT
  let πS' : Subobject.underlying.obj P ⟶
      (FC.shiftFiltration a).assocGraded (s + (n : ℤ)) (k - 1) :=
    (FC.shiftFiltration a).filToAssocGraded (s + (n : ℤ)) (k - 1)
  let πT' : Subobject.underlying.obj Q ⟶
      FC.assocGraded ((s + a) + (n : ℤ)) (k - 1) :=
    FC.filToAssocGraded ((s + a) + (n : ℤ)) (k - 1)
  let qS' := factorThruKernelSubobject gS vS hvgS ≫
    factorThruImageSubobject (KS'.arrow ≫ πS')
  let qT' := factorThruKernelSubobject gT vT hvgT ≫
    factorThruImageSubobject (KT'.arrow ≫ πT')
  let ZS' := imageSubobject (KS'.arrow ≫ πS')
  let ZT' := imageSubobject (KT'.arrow ≫ πT')
  have hqS' : qS' ≫ ZS'.arrow = vS ≫ πS' := by
    dsimp only [qS', ZS']
    rw [Category.assoc, imageSubobject_arrow_comp, ← Category.assoc,
      factorThruKernelSubobject_comp_arrow]
  have hqT' : qT' ≫ ZT'.arrow = vT ≫ πT' := by
    dsimp only [qT', ZT']
    rw [Category.assoc, imageSubobject_arrow_comp, ← Category.assoc,
      factorThruKernelSubobject_comp_arrow]
  let D : ℤ → SSData C := fun q => FC.toSSData bnd q (k - 1)
  have hidx : (s + (n : ℤ)) + a = (s + a) + (n : ℤ) := by abel
  let eV : FC.assocGraded ((s + (n : ℤ)) + a) (k - 1) ⟶
      FC.assocGraded ((s + a) + (n : ℤ)) (k - 1) :=
    eqToHom (congrArg (fun x => FC.assocGraded x (k - 1)) hidx)
  let zmapShift : Subobject.underlying.obj ZS' ⟶
      Subobject.underlying.obj ((D ((s + (n : ℤ)) + a)).Z (n : WithTop ℕ)) :=
    (FC.shiftedSSDataForward bnd a).preserves_Z
      (s + (n : ℤ), k - 1) (n : WithTop ℕ) |>.choose
  let zTransport :
      Subobject.underlying.obj ((D ((s + (n : ℤ)) + a)).Z (n : WithTop ℕ)) ⟶
        Subobject.underlying.obj ((D ((s + a) + (n : ℤ))).Z (n : WithTop ℕ)) :=
    eqToHom (congrArg
      (fun x => Subobject.underlying.obj ((D x).Z (n : WithTop ℕ))) hidx)
  let zmapT : Subobject.underlying.obj ZS' ⟶ Subobject.underlying.obj ZT' :=
    zmapShift ≫ zTransport
  have hzShift : zmapShift ≫
      ((D ((s + (n : ℤ)) + a)).Z (n : WithTop ℕ)).arrow =
        ZS'.arrow ≫
          (FC.shiftFiltrationAssocGradedIso a (s + (n : ℤ)) (k - 1)).hom := by
    exact (FC.shiftedSSDataForward bnd a).preserves_Z
      (s + (n : ℤ), k - 1) (n : WithTop ℕ) |>.choose_spec
  have hzTransport : zTransport ≫ ZT'.arrow =
      ((D ((s + (n : ℤ)) + a)).Z (n : WithTop ℕ)).arrow ≫
        eV := by
    exact subobjectArrow_transport D hidx (n : WithTop ℕ)
  have hπS' : πS' ≫
      (FC.shiftFiltrationAssocGradedIso a (s + (n : ℤ)) (k - 1)).hom =
        FC.filToAssocGraded ((s + (n : ℤ)) + a) (k - 1) := by
    exact FC.shiftFiltrationAssocGradedIso_hom a (s + (n : ℤ)) (k - 1)
  have hπTransport :
      FC.filToAssocGraded ((s + (n : ℤ)) + a) (k - 1) ≫
          eV =
        w ≫ πT' := by
    exact filToAssocGraded_transport FC hidx
  have hzmapT : qS' ≫ zmapT = qT' := by
    apply (cancel_mono ZT'.arrow).mp
    calc
      (qS' ≫ zmapT) ≫ ZT'.arrow =
          qS' ≫ zmapShift ≫ (zTransport ≫ ZT'.arrow) := by
            simp only [zmapT, Category.assoc]
      _ = qS' ≫ zmapShift ≫
          (((D ((s + (n : ℤ)) + a)).Z (n : WithTop ℕ)).arrow ≫
            eV) := by
              exact congrArg (fun h => qS' ≫ zmapShift ≫ h) hzTransport
      _ = qS' ≫ (zmapShift ≫
          ((D ((s + (n : ℤ)) + a)).Z (n : WithTop ℕ)).arrow) ≫
            eV := by
              simp only [Category.assoc]
      _ = qS' ≫ (ZS'.arrow ≫
          (FC.shiftFiltrationAssocGradedIso a (s + (n : ℤ)) (k - 1)).hom) ≫
            eV := by
              exact congrArg
                (fun h => qS' ≫ h ≫ eV)
                hzShift
      _ = (qS' ≫ ZS'.arrow) ≫
          (FC.shiftFiltrationAssocGradedIso a (s + (n : ℤ)) (k - 1)).hom ≫
            eV := by
              simp only [Category.assoc]
      _ = (vS ≫ πS') ≫
          (FC.shiftFiltrationAssocGradedIso a (s + (n : ℤ)) (k - 1)).hom ≫
            eV := by rw [hqS']
      _ = vS ≫ (πS' ≫
          (FC.shiftFiltrationAssocGradedIso a (s + (n : ℤ)) (k - 1)).hom) ≫
            eV := by
              simp only [Category.assoc]
      _ = vS ≫ FC.filToAssocGraded ((s + (n : ℤ)) + a) (k - 1) ≫
            eV := by
              exact congrArg
                (fun h => vS ≫ h ≫ eV)
                hπS'
      _ = vS ≫ w ≫ πT' := by
            simpa only [Category.assoc] using
              congrArg (fun h => vS ≫ h) hπTransport
      _ = vT ≫ πT' := by
            simp only [vT, Category.assoc]
      _ = qT' ≫ ZT'.arrow := hqT'.symm
  haveI : Epi (((FC.shiftFiltration a).toSSData
      (bnd.shiftFiltration a) s k).pageπ (n : WithTop ℕ)) := by
    unfold SSData.pageπ
    infer_instance
  apply (cancel_epi (((FC.shiftFiltration a).toSSData
    (bnd.shiftFiltration a) s k).pageπ (n : WithTop ℕ))).mp
  apply (cancel_epi qS).mp
  have hT := FC.pageDifferential_on_kernel bnd (s + a) k n
    kerMap vT hvT hvgT
  have hS := (FC.shiftFiltration a).pageDifferential_on_kernel
    (bnd.shiftFiltration a) s k n
    (𝟙 (Subobject.underlying.obj KS)) vS
    (by
      simpa only [FilteredComplex.shiftFiltration, Category.id_comp, fS, P] using
        hvS.symm) hvgS
  let pSSource : Subobject.underlying.obj ZS ⟶
      ((FC.shiftFiltration a).toSSData
        (bnd.shiftFiltration a) s k).page (n : WithTop ℕ) :=
    ((FC.shiftFiltration a).toSSData
      (bnd.shiftFiltration a) s k).pageπ (n : WithTop ℕ)
  let pTSource : Subobject.underlying.obj ZT ⟶
      (FC.toSSData bnd (s + a) k).page (n : WithTop ℕ) :=
    (FC.toSSData bnd (s + a) k).pageπ (n : WithTop ℕ)
  let pSTarget : Subobject.underlying.obj ZS' ⟶
      ((FC.shiftFiltration a).toSSData
        (bnd.shiftFiltration a) (s + (n : ℤ)) (k - 1)).page
          (n : WithTop ℕ) :=
    ((FC.shiftFiltration a).toSSData
      (bnd.shiftFiltration a) (s + (n : ℤ)) (k - 1)).pageπ
        (n : WithTop ℕ)
  let pQTarget : Subobject.underlying.obj ZT' ⟶
      (D ((s + a) + (n : ℤ))).page (n : WithTop ℕ) :=
    (D ((s + a) + (n : ℤ))).pageπ (n : WithTop ℕ)
  let pTarget : Subobject.underlying.obj
      ((D ((s + (n : ℤ)) + a)).Z (n : WithTop ℕ)) ⟶
      (D ((s + (n : ℤ)) + a)).page (n : WithTop ℕ) :=
    (D ((s + (n : ℤ)) + a)).pageπ (n : WithTop ℕ)
  let eIsoS := (FC.shiftFiltrationPageIso bnd a (s, k) n).hom
  let eIsoT := (FC.shiftFiltrationPageIso bnd a
    (s + (n : ℤ), k - 1) n).hom
  let dS := (FC.shiftFiltration a).pageDifferential
    (bnd.shiftFiltration a) s k n
  let dT := FC.pageDifferential bnd (s + a) k n
  change qT ≫ pTSource ≫ dT = qT' ≫ pQTarget at hT
  change ((𝟙 (Subobject.underlying.obj KS)) ≫ qS) ≫ pSSource ≫ dS =
    qS' ≫ pSTarget at hS
  simp only [Category.id_comp] at hS
  have hPageS := (FC.shiftedSSDataForward bnd a).pageπ_pageMap
    (s, k) (n : WithTop ℕ)
  have hPageT := (FC.shiftedSSDataForward bnd a).pageπ_pageMap
    (s + (n : ℤ), k - 1) (n : WithTop ℕ)
  have hPageTransport := pageπ_transport D hidx (n : WithTop ℕ)
  let ePage := eqToHom (congrArg
    (fun x => (D x).page (n : WithTop ℕ)) hidx)
  change pSSource ≫ eIsoS = zmapS ≫ pTSource at hPageS
  change pSTarget ≫ eIsoT = zmapShift ≫ pTarget at hPageT
  change pTarget ≫ ePage = zTransport ≫ pQTarget at hPageTransport
  change qS ≫ pSSource ≫ eIsoS ≫ dT =
    qS ≫ pSSource ≫ dS ≫ eIsoT ≫ ePage
  calc
    qS ≫ pSSource ≫ eIsoS ≫ dT =
      qS ≫ zmapS ≫ pTSource ≫ dT := by
        simpa only [Category.assoc] using congrArg (fun h => qS ≫ h ≫ dT) hPageS
    _ = qT ≫ pTSource ≫ dT := by
      simpa only [Category.assoc] using congrArg
        (fun h => h ≫ pTSource ≫ dT) hzmapS
    _ = qT' ≫ pQTarget := hT
    _ = qS' ≫ zmapT ≫ pQTarget := by
      simpa only [Category.assoc] using congrArg (fun h => h ≫ pQTarget) hzmapT.symm
    _ = qS' ≫ zmapShift ≫ zTransport ≫ pQTarget := by
      simp only [zmapT, Category.assoc]
    _ = qS' ≫ zmapShift ≫ pTarget ≫ ePage := by
      simpa only [Category.assoc] using congrArg
        (fun h => qS' ≫ zmapShift ≫ h) hPageTransport.symm
    _ = qS' ≫ pSTarget ≫ eIsoT ≫ ePage := by
      simpa only [Category.assoc] using congrArg (fun h => qS' ≫ h ≫ ePage) hPageT.symm
    _ = qS ≫ pSSource ≫ dS ≫ eIsoT ≫ ePage := by
      simpa only [Category.assoc] using congrArg (fun h => h ≫ eIsoT ≫ ePage) hS.symm

end KIPBase.SpectralSequence
