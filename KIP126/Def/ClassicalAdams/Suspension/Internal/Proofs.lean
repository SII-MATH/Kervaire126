module

public import KIP126.Def.ClassicalAdams.Suspension.Internal.Data
public import KIP126.Def.ClassicalAdams.Suspension.Predicates
public import KIP126.Def.ClassicalAdams.Suspension.Pages.Proofs
public import KIP126.Def.SpectralSequence.Computation.Morphism.Proofs

@[expose] public section


/-!
# Internal naturality of actual Adams desuspension

The cycle and boundary maps define one ambient morphism. Its canonical
quotient maps agree with the actual page desuspension. A single desuspension
anticommutes with the differential; two cancel the signs and preserve the
full common-representative differential relation. No separate differential
compatibility is assumed.
-/
namespace KIP126.Classical.Adams.Suspension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
  KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {X : C}
  (S : TowerComparison H X)

private theorem submodule_lift_exists {R : Type*} [Ring R] {M N : ModuleCat.{v} R}
    (U : Submodule R M) (V : Submodule R N) (g : M →ₗ[R] N)
    (hg : ∀ a ∈ U, g a ∈ V) :
    ∃ lift : Subobject.underlying.obj ((ModuleCat.subobjectModule M).symm U) ⟶
        Subobject.underlying.obj ((ModuleCat.subobjectModule N).symm V),
      lift ≫ ((ModuleCat.subobjectModule N).symm V).arrow =
        ((ModuleCat.subobjectModule M).symm U).arrow ≫ ModuleCat.ofHom g := by
  let l := (g.comp U.subtype).codRestrict V (fun a => hg a a.property)
  refine ⟨(submoduleUnderlyingIso U).hom ≫ ModuleCat.ofHom l ≫
    (submoduleUnderlyingIso V).inv, ?_⟩
  apply (cancel_epi (submoduleUnderlyingIso U).inv).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change ModuleCat.ofHom l ≫ (Subobject.underlyingIso (ModuleCat.ofHom V.subtype)).inv ≫
      (Subobject.mk (ModuleCat.ofHom V.subtype)).arrow =
    (Subobject.underlyingIso (ModuleCat.ofHom U.subtype)).inv ≫
      (Subobject.mk (ModuleCat.ofHom U.subtype)).arrow ≫ ModuleCat.ofHom g
  rw [Subobject.underlyingIso_arrow, Subobject.underlyingIso_arrow_assoc]
  rfl

/-- The actual desuspension preserves both complete subobject towers,
including their infinite levels. The ambient map is fixed by the layer map. -/
theorem TowerComparison.desuspendSSDataMorphism_exists :
    ∃ F : SSDataMorphism (ℤ × ℤ)
        (fun p : ℤ × ℤ => adamsTowerSSData H.unit (X⟦(1 : ℤ)⟧) p.1 p.2)
        (fun p : ℤ × ℤ => adamsTowerSSData H.unit X p.1 (p.2 - 1)),
      ∀ p, F.φ p = ModuleCat.ofHom (S.desuspendCycles 2 (Nat.le_succ 1) p.1 p.2) := by
  refine ⟨{ φ := fun p => ModuleCat.ofHom (S.desuspendCycles 2 (Nat.le_succ 1) p.1 p.2)
            preserves_Z := ?_
            preserves_B := ?_ }, fun _ => rfl⟩
  · intro p r
    exact submodule_lift_exists _ _ _
      (fun _ ha => S.desuspendCycles_mem_cycleSubmodule p.1 p.2 r ha)
  · intro p r
    exact submodule_lift_exists _ _ _
      (fun _ ha => S.desuspendCycles_mem_boundarySubmodule p.1 p.2 r ha)

theorem TowerComparison.desuspendSSDataMorphism_page_comparison
    (F : SSDataMorphism (ℤ × ℤ)
      (fun p : ℤ × ℤ => adamsTowerSSData H.unit (X⟦(1 : ℤ)⟧) p.1 p.2)
      (fun p : ℤ × ℤ => adamsTowerSSData H.unit X p.1 (p.2 - 1)))
    (hF : ∀ p, F.φ p = ModuleCat.ofHom (S.desuspendCycles 2 (Nat.le_succ 1) p.1 p.2))
    (p : ℤ × ℤ) (m : ℕ) :
    F.pageMap p (m : WithTop ℕ) ≫ (adamsTowerSSDataPageIso H.unit X p.1 (p.2 - 1) m).hom =
      (adamsTowerSSDataPageIso H.unit (X⟦(1 : ℤ)⟧) p.1 p.2 m).hom ≫
        ModuleCat.ofHom (S.desuspendPage (m+2) (by omega) p.1 p.2) := by
  let U := adamsFiniteCycleSubmodule H.unit (X⟦(1 : ℤ)⟧) p.1 p.2 m
  let V := adamsFiniteCycleSubmodule H.unit X p.1 (p.2 - 1) m
  let eU := submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient H.unit (X⟦(1 : ℤ)⟧) p.1 p.2)) U
  let eV := submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient H.unit X p.1 (p.2 - 1))) V
  let g := ((S.desuspendCycles 2 (Nat.le_succ 1) p.1 p.2).comp U.subtype).codRestrict V
    (fun a => S.desuspendFirstPage_mem_cycles (m+2) (by omega) p.1 p.2 a.property)
  letI : Mono (ModuleCat.ofHom U.subtype) :=
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  letI : Mono (ModuleCat.ofHom V.subtype) :=
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have hc : eU.inv ≫ F.cycleMap p (m : WithTop ℕ) = ModuleCat.ofHom g ≫ eV.inv := by
    apply (cancel_mono (((adamsTowerSSData H.unit X p.1 (p.2 - 1)).Z (m : WithTop ℕ)).arrow)).mp
    have h := F.cycleMap_arrow p (m : WithTop ℕ)
    rw [hF] at h
    have hu : eU.inv ≫ ((adamsTowerSSData H.unit (X⟦(1 : ℤ)⟧) p.1 p.2).Z (m : WithTop ℕ)).arrow =
        ModuleCat.ofHom U.subtype := Subobject.underlyingIso_arrow _
    have hv : eV.inv ≫ ((adamsTowerSSData H.unit X p.1 (p.2 - 1)).Z (m : WithTop ℕ)).arrow =
        ModuleCat.ofHom V.subtype := Subobject.underlyingIso_arrow _
    calc
      _ = eU.inv ≫ ((adamsTowerSSData H.unit (X⟦(1 : ℤ)⟧) p.1 p.2).Z (m : WithTop ℕ)).arrow ≫
          ModuleCat.ofHom (S.desuspendCycles 2 (Nat.le_succ 1) p.1 p.2) := by
        rw [Category.assoc, h]
      _ = ModuleCat.ofHom U.subtype ≫ ModuleCat.ofHom
          (S.desuspendCycles 2 (Nat.le_succ 1) p.1 p.2) := by rw [← Category.assoc, hu]
      _ = ModuleCat.ofHom g ≫ ModuleCat.ofHom V.subtype := rfl
      _ = _ := by rw [Category.assoc, hv]
  letI : Epi ((adamsTowerSSData H.unit (X⟦(1 : ℤ)⟧) p.1 p.2).pageπ (m : WithTop ℕ)) :=
    inferInstanceAs (Epi (CategoryTheory.Limits.cokernel.π _))
  apply (cancel_epi ((adamsTowerSSData H.unit (X⟦(1 : ℤ)⟧) p.1 p.2).pageπ (m : WithTop ℕ))).mp
  apply (cancel_epi eU.inv).mp
  rw [F.pageπ_pageMap_assoc p (m : WithTop ℕ), ← Category.assoc eU.inv, hc]
  simp only [Category.assoc]
  rw [adamsTowerSSDataPageIso_π]
  have hp := congrArg (fun k => k ≫ ModuleCat.ofHom
    (S.desuspendPage (m+2) (by omega) p.1 p.2))
    (adamsTowerSSDataPageIso_π H.unit (X⟦(1 : ℤ)⟧) p.1 p.2 m)
  have he : ModuleCat.ofHom g ≫ ModuleCat.ofHom
      ((adamsCycleBoundaries H.unit X (m+2) (by omega) p.1 (p.2 - 1)).mkQ.comp
        (adamsFiniteCycleEquiv H.unit X p.1 (p.2 - 1) m).toLinearMap) =
      ModuleCat.ofHom ((adamsCycleBoundaries H.unit (X⟦(1 : ℤ)⟧) (m+2) (by omega) p.1 p.2).mkQ.comp
        (adamsFiniteCycleEquiv H.unit (X⟦(1 : ℤ)⟧) p.1 p.2 m).toLinearMap) ≫
      ModuleCat.ofHom (S.desuspendPage (m+2) (by omega) p.1 p.2) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply congrArg (adamsCycleBoundaries H.unit X (m+2) (by omega) p.1 (p.2 - 1)).mkQ
    apply Subtype.ext
    rfl
  exact he.trans (by simpa only [Category.assoc] using hp.symm)

/-- The ambient morphism induces exactly the actual suspension quotient map. -/
theorem TowerComparison.desuspendSSDataMorphism_pageMap
    (F : SSDataMorphism (ℤ × ℤ)
      (fun p : ℤ × ℤ => adamsTowerSSData H.unit (X⟦(1 : ℤ)⟧) p.1 p.2)
      (fun p : ℤ × ℤ => adamsTowerSSData H.unit X p.1 (p.2 - 1)))
    (hF : ∀ p, F.φ p = ModuleCat.ofHom (S.desuspendCycles 2 (Nat.le_succ 1) p.1 p.2))
    (r : ℤ) (p : ℤ × ℤ) :
    F.pageMap p (↑(r - 2).toNat : WithTop ℕ) = S.desuspendInternalPage r p := by
  apply (cancel_mono (adamsTowerSSDataPageIso H.unit X p.1 (p.2 - 1) (r-2).toNat).hom).mp
  simpa only [TowerComparison.desuspendInternalPage, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using
    S.desuspendSSDataMorphism_page_comparison F hF p (r-2).toNat

/-- The actual internal map sends each raw second-cycle quotient to the
quotient of its specified first-page desuspension. -/
theorem TowerComparison.desuspendInternalPage_classOfSecondCycle (s t : ℤ)
    (a : adamsCycles H.unit (X⟦(1 : ℤ)⟧) 2 (Nat.le_succ 1) s t) :
    S.desuspendInternalPage 2 (s,t) (classOfSecondCycle H (X⟦(1 : ℤ)⟧) s t a) =
      classOfSecondCycle H X s (t-1) (S.desuspendCycles 2 (Nat.le_succ 1) s t a) := by
  change (adamsTowerSSDataPageIso H.unit X s (t-1) 0).toLinearEquiv.symm
    (S.desuspendPage 2 (Nat.le_succ 1) s t
      ((adamsTowerSSDataPageIso H.unit (X⟦(1 : ℤ)⟧) s t 0).toLinearEquiv
        ((adamsTowerSSDataPageIso H.unit (X⟦(1 : ℤ)⟧) s t 0).toLinearEquiv.symm
          ((adamsCycleBoundaries H.unit (X⟦(1 : ℤ)⟧) 2 (Nat.le_succ 1) s t).mkQ a)))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The existing representative relation identifies the actual internal
page map; no independently chosen E₂ function is involved. -/
theorem TowerComparison.DesuspendsClass.internalPage_eq {s t : ℤ}
    {sx : PageRepresentatives.Ambient H (X⟦(1 : ℤ)⟧) (s,t)}
    {x : PageRepresentatives.Ambient H X (s,t-1)}
    (h : S.DesuspendsClass s t sx x) : S.desuspendInternalPage 2 (s,t) sx = x := by
  obtain ⟨a, b, rfl, rfl, hab⟩ := h
  rw [S.desuspendInternalPage_classOfSecondCycle]
  apply congrArg (classOfSecondCycle H X s (t-1))
  exact Subtype.ext hab

private theorem pageIso_transport (n : ℕ) (s : ℤ) {t t' : ℤ} (h : t = t') :
    eqToHom (congrArg (fun k => (adamsTowerSSData H.unit X s k).page (n : WithTop ℕ)) h) ≫
        (adamsTowerSSDataPageIso H.unit X s t' n).hom =
      (adamsTowerSSDataPageIso H.unit X s t n).hom ≫
        eqToHom (congrArg (fun k => ModuleCat.of ℤ (adamsPage H.unit X (n+2) (by omega) s k)) h) := by
  subst t'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem rawPage_transport_apply (n : ℕ) (s : ℤ) {t t' : ℤ} (h : t = t')
    (a : adamsPage H.unit X (n+2) (by omega) s t) :
    (eqToHom (congrArg (fun k => ModuleCat.of ℤ (adamsPage H.unit X (n+2) (by omega) s k)) h)).hom a =
      Eq.mp (congrArg (adamsPage H.unit X (n+2) (by omega) s) h) a := by
  subst t'
  rfl

/-- The actual raw signed differential law transported through the canonical
internal-page quotient isomorphisms. -/
theorem TowerComparison.desuspendInternalPage_internalD (r : ℤ) (s t : ℤ) :
    S.desuspendInternalPage r (s,t) ≫
      adamsTowerInternalD H.unit X (r-2).toNat s (t-1) =
    -(adamsTowerInternalD H.unit (X⟦(1 : ℤ)⟧) (r-2).toNat s t ≫
      S.desuspendInternalPage r
        (s+((r-2).toNat+2:ℕ), t+((r-2).toNat+2:ℕ)-1) ≫
      eqToHom (congrArg
        (fun k => (adamsTowerSSData H.unit X (s+((r-2).toNat+2:ℕ)) k).page
          ((r-2).toNat : WithTop ℕ))
        (show (t+((r-2).toNat+2:ℕ)-1)-1=(t-1)+((r-2).toNat+2:ℕ)-1 by omega))) := by
  apply (cancel_mono (adamsTowerSSDataPageIso H.unit X
    (s+((r-2).toNat+2:ℕ)) ((t-1)+((r-2).toNat+2:ℕ)-1) (r-2).toNat).hom).mp
  simp only [Preadditive.neg_comp, Category.assoc]
  rw [adamsTowerInternalD_comparison]
  rw [pageIso_transport (H := H) (X := X) (r-2).toNat (s+((r-2).toNat+2:ℕ))
    (show (t+((r-2).toNat+2:ℕ)-1)-1=(t-1)+((r-2).toNat+2:ℕ)-1 by omega)]
  simp only [TowerComparison.desuspendInternalPage, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [adamsTowerInternalD, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Preadditive.comp_neg]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change adamsDifferential H.unit X ((r-2).toNat+2) (by omega) s (t-1)
      (S.desuspendPage ((r-2).toNat+2) (by omega) s t a) = _
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rw [rawPage_transport_apply (H := H) (X := X) (r-2).toNat
    (s+((r-2).toNat+2:ℕ))
    (show (t+((r-2).toNat+2:ℕ)-1)-1=(t-1)+((r-2).toNat+2:ℕ)-1 by omega)]
  exact (neg_eq_iff_eq_neg.mpr (S.desuspendPage_differential ((r-2).toNat+2) (by omega) s t a)).symm

private theorem TowerComparison.desuspendInternalPage_transport (r : ℤ)
    (p q : ℤ × ℤ) (h : p = q) {Z : ModuleCat.{v} ℤ}
    (hp : (adamsTowerInternalSpectralSequence H.unit X).Page r (p.1,p.2-1) = Z)
    (hq : (adamsTowerInternalSpectralSequence H.unit X).Page r (q.1,q.2-1) = Z) :
    S.desuspendInternalPage r p ≫ eqToHom hp =
      eqToHom (congrArg ((adamsTowerInternalSpectralSequence H.unit (X⟦(1 : ℤ)⟧)).Page r) h) ≫
        S.desuspendInternalPage r q ≫ eqToHom hq := by
  subst q
  simp only [eqToHom_refl, Category.id_comp]

attribute [local irreducible] adamsTowerSSData

/-- One actual desuspension anticommutes with the internal differential at
every integer page and bidegree, with the target reindexing explicit. -/
theorem TowerComparison.desuspendInternalPage_d (r : ℤ) (p : ℤ × ℤ) :
    S.desuspendInternalPage r p ≫
      (adamsTowerInternalSpectralSequence H.unit X).d r (p.1,p.2-1) =
    -((adamsTowerInternalSpectralSequence H.unit (X⟦(1 : ℤ)⟧)).d r p ≫
      S.desuspendInternalPage r (p+(r,r-1)) ≫
      eqToHom (congrArg ((adamsTowerInternalSpectralSequence H.unit X).Page r)
        (show ((p+(r,r-1)).1,(p+(r,r-1)).2-1)=(p.1,p.2-1)+(r,r-1) by
          apply Prod.ext
          · rfl
          · dsimp
            omega))) := by
  change S.desuspendInternalPage r p ≫ (adamsTowerPreSS H.unit X).d r (p.1,p.2-1) =
    -((adamsTowerPreSS H.unit (X⟦(1 : ℤ)⟧)).d r p ≫
      S.desuspendInternalPage r (p+(r,r-1)) ≫ _)
  by_cases hr : 2 ≤ r
  · rw [adamsTowerPreSS_d_eq H.unit X _ _ hr,
      adamsTowerPreSS_d_eq H.unit (X⟦(1 : ℤ)⟧) _ _ hr]
    rw [← Category.assoc, S.desuspendInternalPage_internalD]
    simp only [Preadditive.neg_comp, Category.assoc, eqToHom_trans]
    congr 1
    congr 1
    have he : (p.1+((r-2).toNat+2:ℕ), p.2+((r-2).toNat+2:ℕ)-1) =
        p+(r,r-1) := by
      have hn : (((r-2).toNat+2:ℕ):ℤ) = r := by omega
      ext <;> dsimp <;> omega
    exact S.desuspendInternalPage_transport r _ _ he _ _
  · have hx : (adamsTowerPreSS H.unit X).d r (p.1,p.2-1) = 0 := dif_neg hr
    have hy : (adamsTowerPreSS H.unit (X⟦(1 : ℤ)⟧)).d r p = 0 := dif_neg hr
    simp only [hx, hy, Limits.comp_zero, Limits.zero_comp, neg_zero]

/-- Common representatives are preserved by the actual internal map on all
pages. Its ambient morphism is constructed from the fixed tower comparison. -/
theorem TowerComparison.desuspendInternalPage_representsOnPage
    {r : ℤ} {p : ℤ × ℤ}
    {x : (adamsTowerInternalSpectralSequence H.unit (X⟦(1 : ℤ)⟧)).Page 2 p}
    {y : (adamsTowerInternalSpectralSequence H.unit (X⟦(1 : ℤ)⟧)).Page r p}
    (h : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit (X⟦(1 : ℤ)⟧))
      r p x y) :
    RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit X) r (p.1,p.2-1)
      (S.desuspendInternalPage 2 p x) (S.desuspendInternalPage r p y) := by
  obtain ⟨F, hF⟩ := S.desuspendSSDataMorphism_exists
  have hf := F.representsOnPage_reindexed
    (E := adamsTowerInternalSpectralSequence H.unit (X⟦(1 : ℤ)⟧))
    (E' := adamsTowerInternalSpectralSequence H.unit X)
    (τ := fun p => (p.1,p.2-1)) rfl h
  simp only [eqToHom_refl, Category.comp_id] at hf
  change RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit X) r (p.1,p.2-1)
    (F.pageMap p (↑(2-2 : ℤ).toNat : WithTop ℕ) x)
    (F.pageMap p (↑(r-2).toNat : WithTop ℕ) y) at hf
  rw [S.desuspendSSDataMorphism_pageMap F hF 2 p,
    S.desuspendSSDataMorphism_pageMap F hF r p] at hf
  exact hf

/-- The composite ambient map induces the two actual desuspensions on every
finite internal page. No independent quotient map is chosen. -/
theorem TowerComparison.desuspendTwiceSSDataMorphism_exists
    (S' : TowerComparison H (X⟦(1 : ℤ)⟧)) :
    ∃ F : SSDataMorphism (ℤ × ℤ)
        (fun p : ℤ × ℤ => adamsTowerSSData H.unit ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧) p.1 p.2)
        (fun p : ℤ × ℤ => adamsTowerSSData H.unit X p.1 (p.2 - 1 - 1)),
      ∀ (r : ℤ) (p : ℤ × ℤ), F.pageMap p (↑(r-2).toNat : WithTop ℕ) =
        S.desuspendTwiceInternalPage S' r p := by
  obtain ⟨F, hF⟩ := S.desuspendSSDataMorphism_exists
  obtain ⟨F', hF'⟩ := S'.desuspendSSDataMorphism_exists
  let G : SSDataMorphism (ℤ × ℤ)
      (fun p : ℤ × ℤ => adamsTowerSSData H.unit (X⟦(1 : ℤ)⟧) p.1 (p.2-1))
      (fun p : ℤ × ℤ => adamsTowerSSData H.unit X p.1 (p.2-1-1)) :=
    { φ := fun p => F.φ (p.1,p.2-1)
      preserves_Z := fun p n => F.preserves_Z (p.1,p.2-1) n
      preserves_B := fun p n => F.preserves_B (p.1,p.2-1) n }
  refine ⟨F'.comp G, ?_⟩
  intro r p
  rw [SSDataMorphism.pageMap_comp]
  change F'.pageMap p (↑(r-2).toNat : WithTop ℕ) ≫
    F.pageMap (p.1,p.2-1) (↑(r-2).toNat : WithTop ℕ) = _
  rw [S'.desuspendSSDataMorphism_pageMap F' hF' r p,
    S.desuspendSSDataMorphism_pageMap F hF r (p.1,p.2-1)]
  rfl

private theorem desuspendInternalPage_d_to
    (r : ℤ) (p q : ℤ × ℤ) (hpq : p+(r,r-1)=q) :
    S.desuspendInternalPage r p ≫
        (adamsTowerInternalSpectralSequence H.unit X).d r (p.1,p.2-1) ≫
        eqToHom (congrArg ((adamsTowerInternalSpectralSequence H.unit X).Page r)
          (show (p.1,p.2-1)+(r,r-1) = (q.1,q.2-1) by
            rw [← hpq]; ext <;> dsimp; omega)) =
      -(((adamsTowerInternalSpectralSequence H.unit (X⟦(1 : ℤ)⟧)).d r p ≫
          eqToHom (congrArg
            ((adamsTowerInternalSpectralSequence H.unit (X⟦(1 : ℤ)⟧)).Page r) hpq)) ≫
        S.desuspendInternalPage r q) := by
  rw [← Category.assoc, S.desuspendInternalPage_d, Preadditive.neg_comp, Category.assoc, Category.assoc]
  subst q
  simp

/-- The two actual suspension signs cancel in the composed internal map. -/
theorem TowerComparison.desuspendTwiceInternalPage_d
    (S' : TowerComparison H (X⟦(1 : ℤ)⟧))
    (r : ℤ) (p : ℤ × ℤ) :
    S.desuspendTwiceInternalPage S' r p ≫
        (adamsTowerInternalSpectralSequence H.unit X).d r (p.1,p.2-1-1) =
      (adamsTowerInternalSpectralSequence H.unit ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)).d r p ≫
        S.desuspendTwiceInternalPage S' r (p+(r,r-1)) ≫
        eqToHom (congrArg ((adamsTowerInternalSpectralSequence H.unit X).Page r)
          (show ((p+(r,r-1)).1,(p+(r,r-1)).2-1-1) = (p.1,p.2-1-1)+(r,r-1) by
            ext <;> dsimp; omega)) := by
  let q := p+(r,r-1)
  have hmiddle : (p.1,p.2-1)+(r,r-1) = (q.1,q.2-1) := by
    ext <;> dsimp [q]; omega
  have hfinal : (p.1,p.2-1-1)+(r,r-1) = (q.1,q.2-1-1) := by
    ext <;> dsimp [q]; omega
  apply (cancel_mono (eqToHom (congrArg
    ((adamsTowerInternalSpectralSequence H.unit X).Page r) hfinal))).mp
  simp only [TowerComparison.desuspendTwiceInternalPage, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [desuspendInternalPage_d_to S r (p.1,p.2-1) (q.1,q.2-1) hmiddle, Preadditive.comp_neg]
  rw [← Category.assoc _ _ (S.desuspendInternalPage r (q.1,q.2-1)),
    ← Category.assoc _ _ (S.desuspendInternalPage r (q.1,q.2-1)),
    desuspendInternalPage_d_to S' r p q rfl]
  simp only [eqToHom_refl, Category.comp_id, Preadditive.neg_comp, neg_neg,
    Category.assoc]
  rfl

/-- Two actual desuspensions preserve the complete internal differential
relation. The commutation law is derived from the two signed tower laws. -/
theorem TowerComparison.desuspendTwiceInternalPage_hasDifferential
    (S' : TowerComparison H (X⟦(1 : ℤ)⟧)) {r : ℤ} {p q : ℤ × ℤ}
    {x : (adamsTowerInternalSpectralSequence H.unit ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)).Page 2 p}
    {y : (adamsTowerInternalSpectralSequence H.unit ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)).Page 2 q}
    (h : HasDifferential
      (adamsTowerInternalSpectralSequence H.unit ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)) r p q x y) :
    HasDifferential (adamsTowerInternalSpectralSequence H.unit X) r
      (p.1,p.2-1-1) (q.1,q.2-1-1)
      (S.desuspendTwiceInternalPage S' 2 p x) (S.desuspendTwiceInternalPage S' 2 q y) := by
  obtain ⟨F, hF⟩ := S.desuspendTwiceSSDataMorphism_exists S'
  have hdegree : ∀ (r : ℤ) (p : ℤ × ℤ),
      ((p+(r,r-1)).1,(p+(r,r-1)).2-1-1) = (p.1,p.2-1-1)+(r,r-1) := by
    intro r p
    ext <;> dsimp; omega
  have hf := F.hasDifferential_reindexed
    (E := adamsTowerInternalSpectralSequence H.unit ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧))
    (E' := adamsTowerInternalSpectralSequence H.unit X)
    (τ := fun p => (p.1,p.2-1-1)) rfl hdegree (by
      dsimp only
      intro r p
      change F.pageMap p (↑(r-2).toNat : WithTop ℕ) ≫
          (adamsTowerInternalSpectralSequence H.unit X).d r (p.1,p.2-1-1) =
        (adamsTowerInternalSpectralSequence H.unit ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)).d r p ≫
          F.pageMap (p+(r,r-1)) (↑(r-2).toNat : WithTop ℕ) ≫ _
      rw [hF r p, hF r (p+(r,r-1))]
      exact S.desuspendTwiceInternalPage_d S' r p) h
  simp only [eqToHom_refl, Category.comp_id] at hf
  change HasDifferential (adamsTowerInternalSpectralSequence H.unit X) r
    (p.1,p.2-1-1) (q.1,q.2-1-1)
    (F.pageMap p (↑(2-2 : ℤ).toNat : WithTop ℕ) x)
    (F.pageMap q (↑(2-2 : ℤ).toNat : WithTop ℕ) y) at hf
  rw [hF 2 p, hF 2 q] at hf
  exact hf

/-- The original two-step representative relations transfer differentials
in all pages and degrees, using only the two actual tower comparisons.
No independent differential-compatibility proposition is required. -/
theorem TowerComparison.hasDifferential_desuspendTwice
    (S' : TowerComparison H (X⟦(1 : ℤ)⟧))
    {r s t u v : ℤ}
    {sx : PageRepresentatives.Ambient H ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧) (s,t)}
    {sy : PageRepresentatives.Ambient H ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧) (u,v)}
    {x1 : PageRepresentatives.Ambient H (X⟦(1 : ℤ)⟧) (s,t-1)}
    {y1 : PageRepresentatives.Ambient H (X⟦(1 : ℤ)⟧) (u,v-1)}
    {x : PageRepresentatives.Ambient H X (s,t-1-1)}
    {y : PageRepresentatives.Ambient H X (u,v-1-1)}
    (hsx : S'.DesuspendsClass s t sx x1)
    (hsy : S'.DesuspendsClass u v sy y1)
    (hx : S.DesuspendsClass s (t-1) x1 x)
    (hy : S.DesuspendsClass u (v-1) y1 y)
    (h : HasDifferential
      (adamsTowerInternalSpectralSequence H.unit ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧))
      r (s,t) (u,v) sx sy) :
    HasDifferential (adamsTowerInternalSpectralSequence H.unit X)
      r (s,t-1-1) (u,v-1-1) x y := by
  have hf := S.desuspendTwiceInternalPage_hasDifferential S' h
  simpa only [TowerComparison.desuspendTwiceInternalPage, ModuleCat.comp_apply,
    hsx.internalPage_eq, hsy.internalPage_eq, hx.internalPage_eq, hy.internalPage_eq] using hf

end
end KIP126.Classical.Adams.Suspension
