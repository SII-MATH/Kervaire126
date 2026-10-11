import KIP126.Def.SpectralSequence.Basic.Category.Proofs
import KIP126.Def.Kervaire.Route.Tools.PageExtensionStretching.Predicates
import KIP126.Def.Kervaire.Route.Tools.Inputs.Data
import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs

/-! Reusable paper-rule proof and explicit unfinished obligations.
No computation delivery or selected stage witness is a premise. The theorem
retains the displayed mathematical comparison premises on the same model; source-to-model assembly remains in Interface. Existing public theorem
names are retained for compatibility. The remaining proof gaps certify no log rows. -/
namespace KIP126.Main.Solution.Tools

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Kervaire.Route KIP126.Classical.Adams
open KIP126.Literature.Route

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

open CategoryTheory.Limits KIP126.Core.SpectralSequence
open KIP126.Synthetic.SpectralSequence KIP126.Synthetic.PageExtension

open KIP126.Algebra KIP126.Classical.Adams.PageRepresentatives

set_option maxHeartbeats 1600000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A zero-length finite extension stretches because its actual E∞ equation
restricts along ρ, whose target map is injective in the common finite window. -/
private theorem finite_extension_zero_stretches
    (synthetic : SyntheticInputs D) (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (rEarlier rLater : ℕ) (s t : ℤ)
    (x : Ambient H (X.obj D.auxiliary) (s,t))
    (y : Ambient H (Y.obj D.auxiliary) (s+0,t+0))
    (hr : 2 ≤ rEarlier) (hle : rEarlier ≤ rLater)
    (hn : (normalizedExponent H f : ℤ) ≤ 0)
    (hx : IsCycle H (X.obj D.auxiliary) ((rLater:ℤ)-1) (s,t) x)
    (hy : IsCycle H (Y.obj D.auxiliary) ((rLater:ℤ)-1-0+normalizedExponent H f)
      (s+0,t+0) y)
    (W : FiniteExtensionWitness D X Y f rEarlier 0 s t x y) :
    FiniteExtension D X Y f rLater 0 s t x y := by
  have extension_zero_iff (D : Model H M Syn)
      (A B : SyntheticObject) (g : A.obj D.nu D.auxiliary ⟶ B.obj D.nu D.auxiliary)
      (p : ℤ × ℤ) (s : ℤ)
      (x : ((D.family.obj (A.obj D.nu D.auxiliary)).sequence.ssData (s, p.1+s, p.2)).eInfty)
      (y : ((D.family.obj (B.obj D.nu D.auxiliary)).sequence.ssData (s, p.1+s, p.2)).eInfty) :
      ExtensionEquation g (D.convergence A) (D.convergence B) p s 0 x
        (by simpa only [add_zero] using y) ↔
        (D.family.functor.map g).eInftyMap (s, p.1+s, p.2) x = y := by
    have elementMap_comp {A B : ModuleCat.{v} ℤ} (x : A) (f : A ⟶ B) :
        elementMap x ≫ f = elementMap (f x) := by
      ext a
      simp [elementMap]
    have strict_fiber_elements (FC : FilteredComplex (ModuleCat.{v} ℤ))
        (n s k : ℤ) (x : FC.assocGraded s k) (y : FC.assocGraded (s+n) (k-1)) :
        Nonempty (FilteredComplex.Solutions.Fiber FC n s k (elementMap x) (elementMap y)) ↔
          ∃ (a : (Subobject.underlying.obj (FC.fil s k) : ModuleCat.{v} ℤ))
            (b : (Subobject.underlying.obj (FC.fil (s+n) (k-1)) : ModuleCat.{v} ℤ)),
            FC.filToAssocGraded s k a=x ∧ FC.filToAssocGraded (s+n) (k-1) b=y ∧
            FC.d k ((FC.fil s k).arrow a)=(FC.fil (s+n) (k-1)).arrow b := by
      constructor
      · rintro ⟨W⟩
        obtain ⟨hx,hy,he⟩ := (FilteredComplex.Solutions.mem_fiber_iff W.val).mp W.property
        refine ⟨W.val.1.hom (ULift.up 1),W.val.2.hom (ULift.up 1),?_,?_,?_⟩
        · have hh := congrArg (fun f => f.hom (ULift.up (1:ℤ))) hx
          simpa [FilteredComplex.IsLift,elementMap] using hh
        · have hh := congrArg (fun f => f.hom (ULift.up (1:ℤ))) hy
          simpa [FilteredComplex.IsLift,elementMap] using hh
        · exact congrArg (fun f => f.hom (ULift.up (1:ℤ))) he
      · rintro ⟨a,b,ha,hb,he⟩
        refine ⟨⟨(elementMap a,elementMap b),(FilteredComplex.Solutions.mem_fiber_iff _).mpr ⟨?_,?_,?_⟩⟩⟩
        · change elementMap a ≫ FC.filToAssocGraded s k=elementMap x
          rw [elementMap_comp,ha]
        · change elementMap b ≫ FC.filToAssocGraded (s+n) (k-1)=elementMap y
          rw [elementMap_comp,hb]
        · rw [←Category.assoc,elementMap_comp,elementMap_comp,elementMap_comp,he]
    have actual_extension_zero_comparison
        (A B : SyntheticObject) (g : A.obj D.nu D.auxiliary ⟶ B.obj D.nu D.auxiliary)
        (p : ℤ×ℤ) (s : ℤ) :
        (extensionSourceIso (nuCoefficientUnit H.unit D.nu) g (D.convergence A) p s).hom ≫
          (extensionComplex (nuCoefficientUnit H.unit D.nu) g p).assocGradedDiff s 1 =
        (D.family.functor.map g).eInftyMap (s,p.1+s,p.2) ≫
          (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p s).hom := by
      obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural A B g
      have hc := c.iso_compat (s,p.1+s,p.2)
      simp only [KIP126.Core.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,TowerConvergence.toSynthetic,
        SyntheticAdamsConvergence.toConvergence] at hc
      rw [hce] at hc
      have hd : (extensionComplex (nuCoefficientUnit H.unit D.nu) g p).assocGradedDiff s 1 =
          Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s p := by
        haveI : Epi ((towerFiltration (nuCoefficientUnit H.unit D.nu)
          (A.obj D.nu D.auxiliary)).toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
        apply (cancel_epi ((towerFiltration (nuCoefficientUnit H.unit D.nu)
          (A.obj D.nu D.auxiliary)).toAssociatedGraded s p)).mp
        change _ ≫ (underlyingComplex (syntheticHomotopyMap g) (homotopyMap_filtration_compatible (nuCoefficientUnit H.unit D.nu) g) p).assocGradedDiff s 1 = _
        rw [underlyingComplex_assocGradedDiff_compat_one]
        have hq : (towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.auxiliary)).toAssociatedGraded s p ≫
            Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s p =
            (c.filtration_compat s p).choose ≫ (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.auxiliary)).toAssociatedGraded s p := by
          exact cokernel.π_desc _ _ _
        rw [hq]
        congr 1
        apply (cancel_mono ((towerFiltration (nuCoefficientUnit H.unit D.nu)
          (B.obj D.nu D.auxiliary)).F s p).arrow).mp
        rw [(homotopyMap_filtration_compatible (nuCoefficientUnit H.unit D.nu) g s p).choose_spec]
        let k := (c.filtration_compat s p).choose
        have hk : k ≫ ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.auxiliary)).F s p).arrow =
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.auxiliary)).F s p).arrow ≫ c.aMap p :=
          (c.filtration_compat s p).choose_spec
        change k ≫
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.auxiliary)).F s p).arrow =
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.auxiliary)).F s p).arrow ≫ c.aMap p at hk
        rw [hca] at hk
        exact hk.symm
      rw [hd]
      have transport {ι : Type} (P Q : ι → ModuleCat.{v} ℤ) (F : ∀i, P i ⟶ Q i)
          {i j : ι} (h : i=j) {U V : ModuleCat.{v} ℤ} (a : U ⟶ P i) (b : V ⟶ Q i)
          (g : U ⟶ V) (he : g≫b=a≫F i) :
          (a≫eqToHom (congrArg P h))≫F j=g≫(b≫eqToHom (congrArg Q h)) := by
        subst j
        simpa only [eqToHom_refl,Category.comp_id] using he.symm
      exact transport (ι:=ℤ×ℤ) (i:=(p.1+s-s,p.2)) (j:=p)
        (fun m => (towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.auxiliary)).associatedGraded s m)
        (fun m => (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.auxiliary)).associatedGraded s m)
        (fun m => Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s m)
        (show (p.1+s-s,p.2)=p by ext <;> simp)
        ((D.convergence A).identification (s,p.1+s,p.2)).hom
        ((D.convergence B).identification (s,p.1+s,p.2)).hom
        ((D.family.functor.map g).eInftyMap (s,p.1+s,p.2)) hc
    let FC := extensionComplex (nuCoefficientUnit H.unit D.nu) g p
    let xx := (extensionSourceIso (nuCoefficientUnit H.unit D.nu) g (D.convergence A) p s).hom x
    let yy := (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p s).hom y
    have hcomp := ConcreteCategory.congr_hom (actual_extension_zero_comparison A B g p s) x
    have transport_zero (u : ℤ) (hu : u = s)
        (y' : ((D.family.obj (B.obj D.nu D.auxiliary)).sequence.ssData (u, p.1+u, p.2)).eInfty)
        (hy : HEq y' y) :
        (∃ (a : (Subobject.underlying.obj (FC.fil s 1) : ModuleCat.{v} ℤ))
          (b : (Subobject.underlying.obj (FC.fil u 0) : ModuleCat.{v} ℤ)),
          FC.filToAssocGraded s 1 a = xx ∧ FC.filToAssocGraded u 0 b =
            (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p u).hom y' ∧
          FC.d 1 ((FC.fil s 1).arrow a) = (FC.fil u 0).arrow b) ↔
        (∃ (a : (Subobject.underlying.obj (FC.fil s 1) : ModuleCat.{v} ℤ))
          (b : (Subobject.underlying.obj (FC.fil s 0) : ModuleCat.{v} ℤ)),
          FC.filToAssocGraded s 1 a = xx ∧ FC.filToAssocGraded s 0 b = yy ∧
          FC.d 1 ((FC.fil s 1).arrow a) = (FC.fil s 0).arrow b) := by
      subst u
      cases hy
      rfl
    simp only [ExtensionEquation]
    rw [strict_fiber_elements]
    refine (and_congr Iff.rfl (transport_zero (s+0) (add_zero s)
      (by simpa only [add_zero] using y) (by change HEq (cast _ y) y; exact cast_heq _ _))).trans ?_
    constructor
    · rintro ⟨_, a, b, ha, hb, hd⟩
      have hdiff : FC.filDiff s 1 a = b := by
        apply (ModuleCat.mono_iff_injective (FC.fil s 0).arrow).mp inferInstance
        have hpres := ConcreteCategory.congr_hom (FC.differential_preserves s 1).choose_spec a
        exact hpres.trans hd
      have hgraded := ConcreteCategory.congr_hom (FC.assocGradedDiff_compat s 1) a
      change FC.assocGradedDiff s 1 (FC.filToAssocGraded s 1 a) =
        FC.filToAssocGraded s 0 (FC.filDiff s 1 a) at hgraded
      rw [ha, hdiff, hb] at hgraded
      apply (ModuleCat.mono_iff_injective
        (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p s).hom).mp inferInstance
      exact hcomp.symm.trans hgraded
    · intro hxy
      refine ⟨le_refl _, ?_⟩
      haveI : Epi (FC.filToAssocGraded s 1) := inferInstanceAs (Epi (cokernel.π _))
      obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (FC.filToAssocGraded s 1)).mp inferInstance xx
      refine ⟨a, FC.filDiff s 1 a, ha, ?_, ?_⟩
      · have hgraded := ConcreteCategory.congr_hom (FC.assocGradedDiff_compat s 1) a
        change FC.assocGradedDiff s 1 (FC.filToAssocGraded s 1 a) =
          FC.filToAssocGraded s 0 (FC.filDiff s 1 a) at hgraded
        rw [ha] at hgraded
        apply hgraded.symm.trans
        apply hcomp.trans
        change (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p s).hom
          ((D.family.functor.map g).eInftyMap (s,p.1+s,p.2) x) = yy
        exact congrArg (fun z => (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g (D.convergence B) p s).hom z) hxy
      · exact (ConcreteCategory.congr_hom (FC.differential_preserves s 1).choose_spec a).symm


  have family_map_data (D : Model H M Syn)  {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
    let F := (D.family.functor.map f).toSSDataMorphism
    let PX := (D.family.functor.obj X).ssData i
    let PY := (D.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(r-(D.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(r-(D.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
    have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D.family.firstPage X]
    have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D.family.firstPage Y]
    have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
        (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
        (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
        eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
      subst n
      subst m
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _
  have family_page_comp (D : Model H M Syn)  {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
    rw [family_map_data D,family_map_data D,family_map_data D,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
  have family_infinity_representative_map (D : Model H M Syn)
      {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
      (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
      (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
      HasInfinityRepresentative (D.family.obj Y) 2 i
        (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
    obtain ⟨hr,z,hz,he⟩ := hy
    change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
      (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
    let F := (D.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · rw [family_map_data D]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
        (((D.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [←F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
        rw [he])
  have page_regrade (D : Model H M Syn) {A B : Syn} (f : A ⟶ B) {i j : Tridegree}
      (h : i = j) (z : (D.family.obj A).E₂ i) :
      regradeE2 h (familyPageMap D.family f 2 i z) =
        familyPageMap D.family f 2 j (regradeE2 h z) := by
    subst j
    rfl

  have finite_source_rho (D : Model H M Syn) (X Y : ClassicalObject)
      (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
      (i j : ℕ) (hij : i ≤ j) (s t : ℤ) (x : E2 H (X.obj D.auxiliary) s t) :
      familyPageMap D.family
        ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.auxiliary)).rho i j hij) 2
        (s, (t-s)+s, t+normalizedExponent H f)
        (finiteSourceForExtension D X Y f j s t x) =
          finiteSourceForExtension D X Y f i s t x := by
    unfold finiteSourceForExtension
    rw [← page_regrade D]
    congr 1
    unfold finiteNuLabel
    have hc := congrArg (fun g => familyPageMap D.family g 2
      (s,t,t+(normalizedExponent H f : ℤ)-(0:ℕ)))
      ((D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.auxiliary)).rho_quotient hij)
    rw [← family_page_comp D] at hc
    exact ConcreteCategory.congr_hom hc ((D.nuE2 X _ s t 0) x)

  have finite_target_rho (D : Model H M Syn) (X Y : ClassicalObject)
      (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
      (i j : ℕ) (hij : i ≤ j) (n s t : ℤ)
      (hn : (normalizedExponent H f : ℤ) ≤ n)
      (y : E2 H (Y.obj D.auxiliary) (s+n) (t+n)) :
      familyPageMap D.family ((D.quotientTower (D.nu.functor.obj (Y.obj D.auxiliary))).rho i j hij) 2
        (s+n, (t-s)+(s+n), t+normalizedExponent H f)
        (finiteTargetForExtension D X Y f j n s t hn y) =
          finiteTargetForExtension D X Y f i n s t hn y := by
    unfold finiteTargetForExtension
    rw [← page_regrade D]
    congr 1
    unfold finiteTargetLabel
    have hc := congrArg (fun g => familyPageMap D.family g 2
      (s+n,t+n,t+n-(n-normalizedExponent H f).toNat))
      ((D.quotientTower (D.nu.functor.obj (Y.obj D.auxiliary))).rho_quotient hij)
    rw [← family_page_comp D] at hc
    exact ConcreteCategory.congr_hom hc (targetNuLabel D Y (s+n) (t+n) _ y)


  have zero_shift_source_exists (D : Model H M Syn)
      (BHS : EInftyInput D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (x : E2 H (X.obj D.auxiliary) s t)
      (hx : x ∈ cycles H (X.obj D.auxiliary) q (s, t)) :
      ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.shift (0, 0) (.nu X))).obj
          D.nu D.auxiliary)).sequence.ssData (s, t, t-(0:ℕ))).eInfty,
        HasInfinityRepresentative _ 2 (s, t, t-(0:ℕ))
          (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D X q 0 s t 0 x) e := by
    have zero_shift_quotient_label
        (X : ClassicalObject) (q : ℕ) (x : E2 H (X.obj D.auxiliary) s t) :
        familyPageMap D.family
          (XModLambdaN.map (show (SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj (X.obj D.auxiliary)) ⟶ D.nu.functor.obj (X.obj D.auxiliary) from SyntheticCategory.biShift_zero.hom.app _) q)
          2 (s,t,t-(0:ℕ))
          (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D X q 0 s t 0 x) =
        (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D X q s t 0 x) := by
      simp only [finiteNuLabel, finiteTargetLabel, targetNuLabel, SyntheticObject.obj]
      have cast_page {A B : Syn} (f : A ⟶ B) {i j : Tridegree}
          (h : i = j) (z : (D.family.obj A).E₂ i) :
          (congrArg (fun k => ((D.family.obj B).E₂ k : Type v)) h).mp
            (familyPageMap D.family f 2 i z) =
          familyPageMap D.family f 2 j
            ((congrArg (fun k => ((D.family.obj A).E₂ k : Type v)) h).mp z) := by
        subst j
        rfl
      have hc := cast_page
        (XModLambdaN.incl ((SyntheticCategory.biShift (0,0)).obj
          (D.nu.functor.obj (X.obj D.auxiliary))) q)
        (show (s,t,t+0-(0:ℕ)) = (s,t,t-(0:ℕ)) by simp) ((D.nuE2 X 0 s t 0) x)
      rw [hc]
      have hn := congrArg (fun f => familyPageMap D.family f 2 (s,t,t-(0:ℕ)))
        (XModLambdaN.incl_naturality (SyntheticCategory.biShift_zero.hom.app
          (D.nu.functor.obj (X.obj D.auxiliary))) q)
      rw [← family_page_comp D, ← family_page_comp D] at hn
      exact (ConcreteCategory.congr_hom hn _).symm
    have zero_shift_quotient_label_inverse
        (X : ClassicalObject) (q : ℕ) (x : E2 H (X.obj D.auxiliary) s t) :
        familyPageMap D.family
          (XModLambdaN.map (show D.nu.functor.obj (X.obj D.auxiliary) ⟶ (SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj (X.obj D.auxiliary)) from SyntheticCategory.biShift_zero.inv.app _) q)
          2 (s,t,t-(0:ℕ))
          (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D X q s t 0 x) =
        (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D X q 0 s t 0 x) := by
      let A := D.nu.functor.obj (X.obj D.auxiliary)
      let f := XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) q
      let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app A) q
      have hfg : f≫g=𝟙 _ := by
        dsimp only [f,g]
        rw [←D.quotientFunctoriality.map_comp,Iso.hom_inv_id_app,D.quotientFunctoriality.map_id]
      rw [←zero_shift_quotient_label  X q x]
      change familyPageMap D.family g 2 (s,t,t-(0:ℕ))
        (familyPageMap D.family f 2 (s,t,t-(0:ℕ)) _) = _
      rw [←ConcreteCategory.comp_apply]
      rw [family_page_comp D  f g 2 (s,t,t-(0:ℕ)),hfg,family_map_data D,D.family.functor.map_id]
      exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
        (D.family.functor.obj (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj A) q)).ssData (s,t,t-(0:ℕ))
        ↑(2-2:ℤ).toNat) _
    have zero_shift_finite_infinity_exists
        (BHS : EInftyInput D) (X : ClassicalObject) (q : ℕ) (hq : 0<q)
        (x : E2 H (X.obj D.auxiliary) s t)
        (hx : x∈PageRepresentatives.cycles H (X.obj D.auxiliary) q (s,t)) :
        ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.shift (0,0) (.nu X))).obj D.nu D.auxiliary)).sequence.ssData (s,t,t-(0:ℕ))).eInfty,
          HasInfinityRepresentative _ 2 (s,t,t-(0:ℕ))
            (by simpa only [add_zero,SyntheticObject.obj,SyntheticAdamsSS.E₂] using finiteNuLabel D X q 0 s t 0 x) e := by
      let P := BHS.presentation.finiteWindow (X.obj D.auxiliary) q hq (s,t) (t-(0:ℕ)) (by constructor <;> omega)
      let c : PageRepresentatives.cycles H (X.obj D.auxiliary) ((q:ℤ)-t+(t-(0:ℕ))) (s,t) :=
        ⟨x,by simpa only [Nat.cast_zero,sub_zero,sub_add_cancel] using hx⟩
      let en := P.symm (NestedQuotient.projection _ _ c)
      have hen : HasInfinityRepresentative (D.family.nuQuotient D.nu (X.obj D.auxiliary) q)
          2 (s,t,t-(0:ℕ)) (by simpa only [SyntheticObject.obj,SyntheticAdamsSS.E₂,SyntheticAdamsFamily.nuQuotient,SyntheticAdamsFamily.quotient] using finiteTargetLabel D X q s t 0 x) en := by
        exact (BHS.labels.1 X q hq (s,t) 0 hq c en).mpr (P.apply_symm_apply _)
      let g := XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app (D.nu.functor.obj (X.obj D.auxiliary))) q
      refine ⟨(D.family.functor.map g).eInftyMap (s,t,t-(0:ℕ)) en,?_⟩
      have he := family_infinity_representative_map D  g (s,t,t-(0:ℕ)) _ en hen
      dsimp only [g,id] at he
      have hl := zero_shift_quotient_label_inverse  X q x
      have hrepl := congrArg (fun z => HasInfinityRepresentative
        (D.family.obj ((SyntheticObject.quotient q (.shift (0,0) (.nu X))).obj D.nu D.auxiliary))
        2 (s,t,t-(0:ℕ)) z ((D.family.functor.map g).eInftyMap (s,t,t-(0:ℕ)) en)) hl
      exact hrepl.mp he
    exact zero_shift_finite_infinity_exists BHS X q hq x hx


  have infinity_representative_regrade
      {A : SyntheticAdamsSS.{v}} {i j : Tridegree} (h : i = j)
      (x : A.E₂ i) (e : (A.sequence.ssData i).eInfty)
      (he : HasInfinityRepresentative A 2 i x e) :
      HasInfinityRepresentative A 2 j (regradeE2 h x)
        ((eqToHom (congrArg (fun p => (A.sequence.ssData p).eInfty) h)) e) := by
    subst j
    exact he

  have zero_shift_source_raw (D : Model H M Syn)
      (BHS : EInftyInput D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (x : E2 H (X.obj D.auxiliary) s t)
      (hx : x ∈ cycles H (X.obj D.auxiliary) q (s, t)) :
      ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.shift (0, 0) (.nu X))).obj
          D.nu D.auxiliary)).sequence.ssData (s, t, t+0-(0:ℕ))).eInfty,
        HasInfinityRepresentative _ 2 (s, t, t+0-(0:ℕ))
          (finiteNuLabel D X q 0 s t 0 x) e := by
    have backward_transport {A : SyntheticAdamsSS.{v}} {i j : Tridegree}
        (h : i=j) (x : A.E₂ i)
        (hx : ∃ e : (A.sequence.ssData j).eInfty,
          HasInfinityRepresentative A 2 j
            ((congrArg (fun k => (A.E₂ k : Type v)) h).mp x) e) :
        ∃ e : (A.sequence.ssData i).eInfty, HasInfinityRepresentative A 2 i x e := by
      subst j
      exact hx
    exact backward_transport (show (s,t,t+0-(0:ℕ))=(s,t,t-(0:ℕ)) by simp)
      (finiteNuLabel D X q 0 s t 0 x) (zero_shift_source_exists D BHS X q hq s t x hx)

  have zero_source_for_extension_exists (D : Model H M Syn)
      (BHS : EInftyInput D) (X Y : ClassicalObject)
      (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
      (hf : normalizedExponent H f=0)
      (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (x : E2 H (X.obj D.auxiliary) s t)
      (hx : x ∈ cycles H (X.obj D.auxiliary) q (s, t)) :
      ∃ z : ((D.family.obj ((SyntheticObject.quotient q
          (extensionSourceObject D X Y f)).obj D.nu D.auxiliary)).sequence.ssData
          (s,(t-s)+s,t+normalizedExponent H f)).eInfty,
        HasInfinityRepresentative _ 2 (s,(t-s)+s,t+normalizedExponent H f)
          (finiteSourceForExtension D X Y f q s t x) z := by
    have source_exists (e : ℕ) (he : e=0) :
        ∃ z : ((D.family.obj ((SyntheticObject.quotient q
            (.shift (0,(e:ℤ)) (.nu X))).obj D.nu D.auxiliary)).sequence.ssData
            (s,(t-s)+s,t+e)).eInfty,
          HasInfinityRepresentative _ 2 (s,(t-s)+s,t+e)
            (regradeE2 (by simp) (finiteNuLabel D X q e s t 0 x)) z := by
      subst e
      obtain ⟨z,hz⟩ := zero_shift_source_raw D BHS X q hq s t x hx
      exact ⟨_,infinity_representative_regrade (by simp) _ z hz⟩
    exact source_exists _ hf


  have finite_target_infinity_exists (D : Model H M Syn)
      (synthetic : SyntheticInputs D) (X Y : ClassicalObject)
      (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
      (q : ℕ) (hq : 0 < q) (n s t : ℤ)
      (hn : (normalizedExponent H f : ℤ) ≤ n)
      (hk : n - normalizedExponent H f < q)
      (y : E2 H (Y.obj D.auxiliary) (s + n) (t + n))
      (hy : y ∈ cycles H (Y.obj D.auxiliary)
        ((q : ℤ) - n + normalizedExponent H f) (s + n, t + n)) :
      ∃ e : ((D.family.obj ((SyntheticObject.quotient q (.nu Y)).obj
          D.nu D.auxiliary)).sequence.ssData
            (s + n, (t - s) + (s + n), t + normalizedExponent H f)).eInfty,
        HasInfinityRepresentative _ 2 _ (finiteTargetForExtension D X Y f q n s t hn y) e := by
    let k := (n - normalizedExponent H f).toNat
    have hkZ : (k : ℤ) = n - normalizedExponent H f := Int.toNat_of_nonneg (by omega)
    have hkq : k < q := by omega
    let p : ℤ × ℤ := (s + n, t + n)
    let P := synthetic.eInfty.presentation.finiteWindow
      (Y.obj D.auxiliary) q hq p (p.2 - k) (by constructor <;> omega)
    let c : cycles H (Y.obj D.auxiliary) ((q : ℤ) - p.2 + (p.2 - k)) p :=
      ⟨y, by
        have heq : (q : ℤ) - p.2 + (p.2 - k) = (q : ℤ) - n + normalizedExponent H f := by omega
        simpa only [heq] using hy⟩
    let e := P.symm (NestedQuotient.projection _ _ c)
    have he : HasInfinityRepresentative (D.family.nuQuotient D.nu (Y.obj D.auxiliary) q)
        2 (p.1, p.2, p.2 - k) (finiteTargetLabel D Y q p.1 p.2 k y) e :=
      (synthetic.eInfty.labels.1 Y q hq p k hkq c e).mpr (P.apply_symm_apply _)
    have hi : (p.1, p.2, p.2 - k) =
        (s + n, (t - s) + (s + n), t + normalizedExponent H f) := by
      dsimp only [p]
      apply Prod.ext
      · rfl
      · apply Prod.ext <;> dsimp only [Prod.fst, Prod.snd] <;> omega
    refine ⟨(eqToHom (congrArg (fun p =>
      ((D.family.nuQuotient D.nu (Y.obj D.auxiliary) q).sequence.ssData p).eInfty) hi)) e, ?_⟩
    exact infinity_representative_regrade hi _ _ he


  have rho_injective (D : Model H M Syn) (synthetic : SyntheticInputs D)
      (Y : ClassicalObject) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j)
      (p : ℤ × ℤ) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < i) :
      Function.Injective (((D.family.functor.map
        ((D.quotientTower (D.nu.functor.obj (Y.obj D.auxiliary))).rho i j hij)).eInftyMap
          (p.1,p.2,w)).hom) := by
    intro a b hab
    apply (synthetic.eInfty.presentation.finiteWindow (Y.obj D.auxiliary) j (by omega)
      p w (by constructor <;> omega)).injective
    have hcycles : cycles H (Y.obj D.auxiliary) ((j:ℤ)-p.2+w) p ≤
        cycles H (Y.obj D.auxiliary) ((i:ℤ)-p.2+w) p :=
      cycles_antitone H (Y.obj D.auxiliary) p (by omega)
    apply NestedQuotient.cycle_map_injective hcycles
    change quotientMap H (Y.obj D.auxiliary) (by omega) (le_refl _) p _ =
      quotientMap H (Y.obj D.auxiliary) (by omega) (le_refl _) p _
    rw [← synthetic.eInfty.maps.rho_finite (Y.obj D.auxiliary) i j hi hij p w hw a,
      ← synthetic.eInfty.maps.rho_finite (Y.obj D.auxiliary) i j hi hij p w hw b, hab]

  have he : normalizedExponent H f = 0 := by omega
  have hq : 0 < rLater-1 := by omega
  have hi : 0 < rEarlier-1 := by omega
  have hij : rEarlier-1 ≤ rLater-1 := by omega
  obtain ⟨xx,hxx⟩ := zero_source_for_extension_exists D synthetic.eInfty X Y f he
    (rLater-1) hq s t x (by
      simpa only [Nat.cast_sub (show 1≤rLater by omega),Nat.cast_one] using hx.2)
  obtain ⟨yy,hyy⟩ := finite_target_infinity_exists D synthetic X Y f
    (rLater-1) hq 0 s t hn (by omega) y (by
      simpa only [Nat.cast_sub (show 1≤rLater by omega),Nat.cast_one] using hy.2)
  let a := (D.quotientTower ((extensionSourceObject D X Y f).obj D.nu D.auxiliary)).rho
    (rEarlier-1) (rLater-1) hij
  let b := (D.quotientTower (D.nu.functor.obj (Y.obj D.auxiliary))).rho
    (rEarlier-1) (rLater-1) hij
  have hsource : (D.family.functor.map a).eInftyMap
      (s,(t-s)+s,t+normalizedExponent H f) xx = W.source := by
    have hh := family_infinity_representative_map D a _ _ xx hxx
    rw [finite_source_rho D] at hh
    exact hh.unique W.source_rep
  have htarget : (D.family.functor.map b).eInftyMap
      (s+0,(t-s)+(s+0),t+normalizedExponent H f) yy = W.target := by
    have hh := family_infinity_representative_map D b _ _ yy hyy
    rw [finite_target_rho D] at hh
    exact hh.unique W.target_rep
  let yy0 : ((D.family.obj ((SyntheticObject.quotient (rLater-1) (.nu Y)).obj
        D.nu D.auxiliary)).sequence.ssData
          (s,(t-s)+s,t+normalizedExponent H f)).eInfty := by
    simpa only [add_zero] using yy
  let wy0 : ((D.family.obj ((SyntheticObject.quotient (rEarlier-1) (.nu Y)).obj
        D.nu D.auxiliary)).sequence.ssData
          (s,(t-s)+s,t+normalizedExponent H f)).eInfty := by
    simpa only [add_zero] using W.target
  have hearly : (D.family.functor.map (finiteExtensionMap D X Y f (rEarlier-1))).eInftyMap
      (s,(t-s)+s,t+normalizedExponent H f) W.source = wy0 := by
    have hcast : (by simpa only [add_zero] using wy0 :
        ((D.family.obj ((SyntheticObject.quotient (rEarlier-1) (.nu Y)).obj
          D.nu D.auxiliary)).sequence.ssData
            (s+0,(t-s)+(s+0),t+normalizedExponent H f)).eInfty) = W.target := by
      change cast _ (cast _ W.target) = W.target
      exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
    have hh := extension_zero_iff D
      (.quotient (rEarlier-1) (extensionSourceObject D X Y f)) (.quotient (rEarlier-1) (.nu Y))
      (finiteExtensionMap D X Y f (rEarlier-1)) (t-s,t+normalizedExponent H f) s W.source wy0
    rw [hcast] at hh
    exact hh.mp W.equation
  have htarget0 : (D.family.functor.map b).eInftyMap
      (s,(t-s)+s,t+normalizedExponent H f) yy0 = wy0 := by
    have cast_infty {A B : Syn} (g : A ⟶ B) {i j : Tridegree}
        (h : i=j) (z : ((D.family.obj A).sequence.ssData i).eInfty) :
        (congrArg (fun k => (((D.family.obj B).sequence.ssData k).eInfty : Type v)) h).mp
          ((D.family.functor.map g).eInftyMap i z) =
        (D.family.functor.map g).eInftyMap j
          ((congrArg (fun k => (((D.family.obj A).sequence.ssData k).eInfty : Type v)) h).mp z) := by
      subst j
      rfl
    have hh := cast_infty b
      (show (s+0,(t-s)+(s+0),t+normalizedExponent H f)=
        (s,(t-s)+s,t+normalizedExponent H f) by simp) yy
    rw [htarget] at hh
    exact hh.symm
  have hsquare : a ≫ finiteExtensionMap D X Y f (rEarlier-1) =
      finiteExtensionMap D X Y f (rLater-1) ≫ b :=
    (D.comparisonCompatible.quotient_naturality (D.normalizedMap X Y f).map).rho_naturality hij
  have infinity_comp {A B C : Syn} (g : A ⟶ B) (h : B ⟶ C) (i : Tridegree) :
      (D.family.functor.map (g ≫ h)).eInftyMap i =
        (D.family.functor.map g).eInftyMap i ≫ (D.family.functor.map h).eInftyMap i := by
    rw [Functor.map_comp]
    exact SpectralSequenceMorphism.eInftyMap_comp _ _ _
  have hsquare' := congrArg (fun g => (D.family.functor.map g).eInftyMap
      (s,(t-s)+s,t+normalizedExponent H f)) hsquare
  rw [infinity_comp, infinity_comp] at hsquare'
  have hlater : (D.family.functor.map (finiteExtensionMap D X Y f (rLater-1))).eInftyMap
      (s,(t-s)+s,t+normalizedExponent H f) xx = yy0 := by
    apply rho_injective D synthetic Y (rEarlier-1) (rLater-1) hi hij
      (s,(t-s)+s) (t+normalizedExponent H f) (by dsimp only [Prod.snd]; constructor <;> omega)
    have hh := ConcreteCategory.congr_hom hsquare' xx
    change (D.family.functor.map (finiteExtensionMap D X Y f (rEarlier-1))).eInftyMap _
      ((D.family.functor.map a).eInftyMap _ xx) =
      (D.family.functor.map b).eInftyMap _
        ((D.family.functor.map (finiteExtensionMap D X Y f (rLater-1))).eInftyMap _ xx) at hh
    rw [hsource,hearly] at hh
    exact hh.symm.trans htarget0.symm
  refine ⟨{
    page_ge_two := by omega
    length_lower := hn
    length_upper := by omega
    source_cycle := hx
    target_cycle := hy
    source := xx
    target := yy
    source_rep := hxx
    target_rep := hyy
    equation := ?_}⟩
  have hh := (extension_zero_iff D
    (.quotient (rLater-1) (extensionSourceObject D X Y f)) (.quotient (rLater-1) (.nu Y))
    (finiteExtensionMap D X Y f (rLater-1)) (t-s,t+normalizedExponent H f) s xx yy0).mpr hlater
  have hcast : (by simpa only [add_zero] using yy0 :
      ((D.family.obj ((SyntheticObject.quotient (rLater-1) (.nu Y)).obj
        D.nu D.auxiliary)).sequence.ssData
          (s+0,(t-s)+(s+0),t+normalizedExponent H f)).eInfty) = yy := by
    change cast _ (cast _ yy) = yy
    exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
  rw [hcast] at hh
  exact hh


/-- The finite sufficient-condition form of MainPaper Proposition `prop:dec738d3`
and Corollary `cor:dfc6043e`. This asserts neither an infinite lift nor compatibility
of arbitrarily chosen lifts; the later-page cycle conditions remain explicit. -/
theorem finitePageExtensionStretching (synthetic : SyntheticInputs D)
    (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) :
    KIP126.Kervaire.Route.Tools.FinitePageExtensionStretchingLaw D X Y f := by
  intro rEarlier rLater n s t x y hr hle hn hnUpper hx hy hW hcross
  by_cases hsame : rEarlier = rLater
  · subst rLater
    exact hW
  by_cases hnZero : n = 0
  · subst n
    obtain ⟨W⟩ := hW
    exact finite_extension_zero_stretches D synthetic X Y f rEarlier rLater s t
      x y hr hle hn hx hy W
  have hLater : rEarlier < rLater := by omega
  have hnPositive : 0 < n := by omega
  -- Remaining obligation from MainPaper `prop:dec738d3`: for strictly increasing finite pages
  -- and positive extension length, correct an actual later-page source lift
  -- through the finite filtration. A failed correction must yield precisely
  -- the nonliftable essential crossing ruled out by hcross.
  sorry

end KIP126.Main.Solution.Tools
