import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.FirstQuotient.Predicates
import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Proofs

/-! The first-quotient comparison, pinned to realization and actual tower
arrows. Realization of nu X/lambda itself is zero, so applying realization
directly to its homotopy class CANNOT define its classical E2 label.
Instead the label uses the actual quotient projection on Adams pages,
the actual realization map on the unquotiented tower, and the J/cofiber
image of a lift in the quotient tower. Equality remains in E-infinity;
there is no unwarranted equality between independently chosen E2 lifts.
-/
namespace KIP126.Comparison.ClassicalSynthetic.RealizationTower
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

variable [D.recovery.realization.Monoidal] [D.recovery.realization.Additive]
local instance fqProofRealizationShift : D.recovery.realization.CommShift ℤ := D.realizationShift
variable (bases : WeightBases D) (B : NuE2Binding D bases)

omit [D.recovery.realization.Monoidal] [D.recovery.realization.Additive] in
open KIP126.Core.SpectralSequence in
set_option backward.isDefEq.respectTransparency false in
private theorem actualDetection_iff (Z : SyntheticObject) (s t w : ℤ)
    (x : (D.family.obj (Z.obj D.nu D.auxiliary)).E₂ (s,t,w))
    (α : BiHom (t-s) w (Z.obj D.nu D.auxiliary)) :
    Detects (D.convergence Z) (s,t,w) x α ↔
    ∃ (r : TowerDetection.InfiniteRepresentative (nuCoefficientUnit H.unit D.nu)
        ((SyntheticCategory.biShift (0,-w)).obj (Z.obj D.nu D.auxiliary)) (s,t))
      (b : HomotopyGroup (t-s) (adamsTowerAt (nuCoefficientUnit H.unit D.nu)
        ((SyntheticCategory.biShift (0,-w)).obj (Z.obj D.nu D.auxiliary)) s))
      (j : TowerDetection.InfiniteRepresentative (nuCoefficientUnit H.unit D.nu)
        ((SyntheticCategory.biShift (0,-w)).obj (Z.obj D.nu D.auxiliary)) (s,t)),
      infiniteE2 _ _ (s,t) r = (D.towerPresentation.forward (Z.obj D.nu D.auxiliary) w).pageMap (s,t) 0 x ∧
      TowerDetection.infiniteRepresentativeE1 _ _ (s,t) j = adamsJ _ _ s t b ∧
      infiniteClass _ _ (s,t) r = infiniteClass _ _ (s,t) j ∧
      inducedMap (adamsTowerMap _ _ 0 s.toNat (Nat.zero_le _)) (t-s) b =
        weightHomotopyMap (t-s) w (Z.obj D.nu D.auxiliary) α := by
  let U := nuCoefficientUnit H.unit D.nu
  let Q := Z.obj D.nu D.auxiliary
  let Y := (SyntheticCategory.biShift (0,-w)).obj Q
  let E := (D.family.obj Q).sequence.ssData (s,t,w)
  let F := D.towerPresentation.forward Q w
  let I := D.towerPresentation.inverse Q w
  have hFI : F.comp I = SSDataMorphism.id (fun p : ℤ × ℤ => (D.family.obj Q).sequence.ssData (p.1,p.2,w)) := by
    apply SSDataMorphism.ext
    funext p
    exact D.towerPresentation.left_inv Q w p
  have hIF : I.comp F = SSDataMorphism.id (weightTower U Q w).ssData := by
    apply SSDataMorphism.ext
    funext p
    exact D.towerPresentation.right_inv Q w p
  have hpage (r : WithTop ℕ) : F.pageMap (s,t) r ≫ I.pageMap (s,t) r = 𝟙 _ := by
    rw [← SSDataMorphism.pageMap_comp, hFI, SSDataMorphism.pageMap_id]
  have hcycle (z : TowerDetection.InfiniteRepresentative U Y (s,t)) :
      F.cycleMap (s,t) ⊤ (I.cycleMap (s,t) ⊤ z) = z := by
    have h := congrArg (fun f => f.cycleMap (s,t) ⊤) hIF
    simp only [SSDataMorphism.cycleMap_comp] at h
    erw [SSDataMorphism.cycleMap_id] at h
    exact congrArg (fun f => f.hom z) h
  have hp {A A' : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
      (f : SSDataMorphism (ℤ × ℤ) A A')
      (z : (Subobject.underlying.obj ((A (s,t)).Z ⊤) : ModuleCat ℤ)) :
      (Subobject.ofLE _ _ ((A' (s,t)).Z_anti le_top) ≫ (A' (s,t)).pageπ 0)
        (f.cycleMap (s,t) ⊤ z) =
      f.pageMap (s,t) 0 ((Subobject.ofLE _ _ ((A (s,t)).Z_anti le_top) ≫ (A (s,t)).pageπ 0) z) := by
    have h : f.cycleMap (s,t) ⊤ ≫ Subobject.ofLE _ _ ((A' (s,t)).Z_anti le_top) ≫ (A' (s,t)).pageπ 0 =
        Subobject.ofLE _ _ ((A (s,t)).Z_anti le_top) ≫ (A (s,t)).pageπ 0 ≫ f.pageMap (s,t) 0 := by
      rw [← SSDataMorphism.cycleMap_ofLE_assoc f (s,t) (show (0 : WithTop ℕ) ≤ ⊤ from le_top), ← SSDataMorphism.pageπ_pageMap]
    exact congrArg (fun g => g.hom z) h
  have hi {A A' : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
      (f : SSDataMorphism (ℤ × ℤ) A A')
      (z : (Subobject.underlying.obj ((A (s,t)).Z ⊤) : ModuleCat ℤ)) :
      (A' (s,t)).pageπ ⊤ (f.cycleMap (s,t) ⊤ z) = f.pageMap (s,t) ⊤ ((A (s,t)).pageπ ⊤ z) :=
    (congrArg (fun g => g.hom z) (f.pageπ_pageMap (s,t) ⊤)).symm
  constructor
  · rintro ⟨e, ⟨_, z, hz, he⟩, a, ha, hae⟩
    have hm : α ∈ towerFiltrationSubmodule U Q s (t-s,w) := by
      have h : α ∈ (ModuleCat.subobjectModule _) ((towerFiltration U Q).F s (t-s,w)) := ⟨a,ha⟩
      simpa only [towerFiltration, OrderIso.apply_symm_apply] using h
    have hm' := ((D.convergence_canonical Z).1 s (t-s) w α).mp hm
    obtain ⟨b,hb⟩ := hm'
    obtain ⟨j,hj⟩ := exists_weightLiftRepresentative U D.towerPresentation Q (s,t,w) b
    have hc := (D.convergence_canonical Z).2 (s,t,w) b j hj a (by rw [ha]; exact hb.symm)
    have heq : E.pageπ ⊤ z = E.pageπ ⊤ j := by
      apply (ModuleCat.mono_iff_injective ((D.convergence Z).identification (s,t,w)).hom).mp inferInstance
      rw [he,hae,hc]
    refine ⟨F.cycleMap (s,t) ⊤ z, b, F.cycleMap (s,t) ⊤ j, ?_, hj, ?_, hb⟩
    · change _ = F.pageMap (s,t) 0 x
      change E.pageπ ⊤ z = e at he
      change (Subobject.ofLE _ _ (E.Z_anti le_top) ≫ E.pageπ 0) z = x at hz
      exact (hp F z).trans (congrArg (F.pageMap (s,t) 0) hz)
    · exact (hi F z).trans ((congrArg (F.pageMap (s,t) ⊤) heq).trans (hi F j).symm)
  · rintro ⟨r,b,j,hr,hj,hrj,hb⟩
    have hm' : weightHomotopyMap (t-s) w Q α ∈ TowerDetection.filtrationSubmodule U Y s (t-s) := ⟨b,hb⟩
    have hm := ((D.convergence_canonical Z).1 s (t-s) w α).mpr hm'
    have hmem : α ∈ (ModuleCat.subobjectModule _) ((towerFiltration U Q).F s (t-s,w)) := by
      simpa only [towerFiltration,OrderIso.apply_symm_apply] using hm
    obtain ⟨a,ha⟩ := hmem
    let r' := I.cycleMap (s,t) ⊤ r
    let j' := I.cycleMap (s,t) ⊤ j
    have hj' : familyInfiniteRepresentativeE1 U D.towerPresentation Q (s,t,w) j' = adamsJ U Y s t b := by
      change TowerDetection.infiniteRepresentativeE1 U Y (s,t) (F.cycleMap (s,t) ⊤ (I.cycleMap (s,t) ⊤ j)) = _
      rw [hcycle]
      exact hj
    have hc := (D.convergence_canonical Z).2 (s,t,w) b j' hj' a (by rw [ha]; exact hb.symm)
    have heq : E.pageπ ⊤ r' = E.pageπ ⊤ j' :=
      (hi I r).trans ((congrArg (I.pageMap (s,t) ⊤) hrj).trans (hi I j).symm)
    refine ⟨E.pageπ ⊤ r', ⟨by decide, r', ?_, rfl⟩, a, ha, ?_⟩
    · change (Subobject.ofLE _ _ (E.Z_anti le_top) ≫ E.pageπ 0) r' = x
      rw [show (Subobject.ofLE _ _ (E.Z_anti le_top) ≫ E.pageπ 0) r' = I.pageMap (s,t) 0 (infiniteE2 U Y (s,t) r) from hp I r]
      rw [hr]
      exact congrArg (fun f => f.hom x) (hpage 0)
    · rw [heq]
      exact hc
omit [D.recovery.realization.Monoidal] [D.recovery.realization.Additive] in
open KIP126.Core.SpectralSequence in
set_option backward.isDefEq.respectTransparency false in
private theorem familyPageMap_e2 {A A' : Syn} (f : A ⟶ A') (i : Tridegree) :
    familyPageMap D.family f 2 i = (D.family.functor.map f).toSSDataMorphism.pageMap i 0 := by
  have hlevel : (↑(2 - (D.family.functor.obj A).r₀).toNat : WithTop ℕ) = 0 := by
    rw [D.family.firstPage]
    rfl
  have hn {E E' : Tridegree → SSData (ModuleCat.{v} ℤ)}
      (g : SSDataMorphism Tridegree E E') (r : WithTop ℕ) (hr : r=0) :
      eqToHom (congrArg (fun r => (E i).page r) hr.symm) ≫ g.pageMap i r ≫
        eqToHom (congrArg (fun r => (E' i).page r) hr) = g.pageMap i 0 := by
    subst r
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  simp only [familyPageMap, SpectralSequenceMorphism.pageMap, PreSSMorphism.pageMap,
    SpectralSequenceMorphism.toPreSSMorphism, SSDataMorphism.pageMapAt,
    Category.assoc, eqToHom_trans]
  exact hn (D.family.functor.map f).toSSDataMorphism _ hlevel

/-- The route's nu_first_quotient condition gives a family representative.
Naturality of the SAME tower presentation transports the actual quotient
map; canonical convergence transports the actual tower lift and J image.
NuE2Binding fixes its classical label through realization. -/
theorem firstQuotientBinding_of_nuE2 : FirstQuotientBinding D bases B := by
  exact (open KIP126.Core.SpectralSequence in by
    set_option backward.isDefEq.respectTransparency false in
      intro X a s t x
      let A := (SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.auxiliary))
      let ν : E2 H (X.obj D.auxiliary) s t ≃ₗ[ℤ] (D.family.obj A).E₂ (s,t,t+a) := by
        exact (D.nuE2 X a s t 0).trans
          (LinearEquiv.cast (R := ℤ) (M := fun w : ℤ => ↥((D.family.obj A).E₂ (s,t,w)))
            (by simp : t+a-(0 : ℕ)=t+a))
      let F := D.towerPresentation.forward A (t+a)
      let α := (D.firstQuotient (X.obj D.auxiliary) a s t).symm x
      have hd := D.comparisonCompatible.nu_first_quotient X a s t x
      change Detects (D.convergence (.quotient 1 (.shift (0,a) (.nu X)))) (s,t,t+a)
        (familyPageMap D.family (XModLambdaN.incl A 1) 2 (s,t,t+a) (ν x)) α at hd
      obtain ⟨r,b,j,hr,hj,hclass,hproj⟩ :=
        (actualDetection_iff D (.quotient 1 (.shift (0,a) (.nu X))) s t (t+a) _ α).mp hd
      refine ⟨F.pageMap (s,t) 0 (ν x), ?_, r,b,j,?_,hj,hclass,hproj⟩
      · have ht {w w' : ℤ} (h : w=w') (y : (D.family.obj A).E₂ (s,t,w)) :
            internalE2Map (B.tower X a w') (s,t)
              ((D.towerPresentation.forward A w').pageMap (s,t) 0
                (LinearEquiv.cast (R := ℤ) (M := fun w : ℤ => ↥((D.family.obj A).E₂ (s,t,w))) h y)) =
            internalE2Map (B.tower X a w) (s,t)
              ((D.towerPresentation.forward A w).pageMap (s,t) 0 y) := by
          subst w'
          rfl
        exact (ht (by simp : t+a-(0 : ℕ)=t+a) ((D.nuE2 X a s t 0) x)).trans
          (B.label X a s t 0 x)
      · apply hr.trans
        rw [familyPageMap_e2]
        exact congrArg (fun f => f.hom (ν x))
          (D.towerPresentation.natural_e2 (XModLambdaN.incl A 1) (t+a) (s,t)))

/-- The remaining higher-filtration ambiguity is eliminated exactly by
the BHS p=1 single-filtration range, not by strengthening detection to an
unconditional equality of arbitrary representatives. -/
theorem actualFirstQuotientLabel_unique (X : ClassicalObject) (a s t : ℤ)
    (hzero : FirstQuotientNextFiltrationZero D X a s t)
    (x : E2 H (X.obj D.auxiliary) s t)
    (α β : BiHom (t-s) (t+a) (firstQuotientObject D X a))
    (hα : ActualFirstQuotientLabel D bases B X a s t x α)
    (hβ : ActualFirstQuotientLabel D bases B X a s t x β) : α = β := by
  exact (open KIP126.Core.SpectralSequence in by
    set_option backward.isDefEq.respectTransparency false in
      let A := (SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.auxiliary))
      let ν : E2 H (X.obj D.auxiliary) s t ≃ₗ[ℤ] (D.family.obj A).E₂ (s,t,t+a) :=
        (D.nuE2 X a s t 0).trans
          (LinearEquiv.cast (R := ℤ) (M := fun w : ℤ => ↥((D.family.obj A).E₂ (s,t,w)))
            (by simp : t+a-(0 : ℕ)=t+a))
      let F := D.towerPresentation.forward A (t+a)
      let I := D.towerPresentation.inverse A (t+a)
      have hlabel (y : E2 H (X.obj D.auxiliary) s t) :
          internalE2Map (B.tower X a (t+a)) (s,t) (F.pageMap (s,t) 0 (ν y)) = y := by
        have ht {w w' : ℤ} (h : w=w') (y : (D.family.obj A).E₂ (s,t,w)) :
            internalE2Map (B.tower X a w') (s,t)
              ((D.towerPresentation.forward A w').pageMap (s,t) 0
                (LinearEquiv.cast (R := ℤ) (M := fun w : ℤ => ↥((D.family.obj A).E₂ (s,t,w))) h y)) =
            internalE2Map (B.tower X a w) (s,t)
              ((D.towerPresentation.forward A w).pageMap (s,t) 0 y) := by
          subst w'
          rfl
        exact (ht (by simp : t+a-(0 : ℕ)=t+a) ((D.nuE2 X a s t 0) y)).trans
          (B.label X a s t 0 y)
      have hIF : I.comp F = SSDataMorphism.id (weightTower (nuCoefficientUnit H.unit D.nu) A (t+a)).ssData := by
        apply SSDataMorphism.ext
        funext p
        exact D.towerPresentation.right_inv A (t+a) p
      have hround (z : (weightTower (nuCoefficientUnit H.unit D.nu) A (t+a)).Page 2 (s,t)) :
          F.pageMap (s,t) 0 (I.pageMap (s,t) 0 z) = z := by
        have h := congrArg (fun f => f.pageMap (s,t) 0) hIF
        simp only [SSDataMorphism.pageMap_comp] at h
        erw [SSDataMorphism.pageMap_id] at h
        exact congrArg (fun f => f.hom z) h
      have hdetect (γ : BiHom (t-s) (t+a) (firstQuotientObject D X a))
          (hγ : ActualFirstQuotientLabel D bases B X a s t x γ) :
          Detects (D.convergence (.quotient 1 (.shift (0,a) (.nu X)))) (s,t,t+a)
            (familyPageMap D.family (XModLambdaN.incl A 1) 2 (s,t,t+a) (ν x)) γ := by
        obtain ⟨z,hz,r,b,j,hr,hj,hrj,hb⟩ := hγ
        have hy := hlabel (ν.symm (I.pageMap (s,t) 0 z))
        rw [LinearEquiv.apply_symm_apply,hround] at hy
        have hyx := hy.symm.trans hz
        have hz' : z = F.pageMap (s,t) 0 (ν x) := by
          calc
            z = F.pageMap (s,t) 0 (I.pageMap (s,t) 0 z) := (hround z).symm
            _ = F.pageMap (s,t) 0 (ν (ν.symm (I.pageMap (s,t) 0 z))) :=
              congrArg (F.pageMap (s,t) 0) (ν.apply_symm_apply _).symm
            _ = F.pageMap (s,t) 0 (ν x) := by rw [hyx]
        apply (actualDetection_iff D (.quotient 1 (.shift (0,a) (.nu X))) s t (t+a) _ γ).mpr
        refine ⟨r,b,j,?_,hj,hrj,hb⟩
        rw [hz'] at hr
        apply hr.trans
        rw [familyPageMap_e2]
        exact (congrArg (fun f => f.hom (ν x))
          (D.towerPresentation.natural_e2 (XModLambdaN.incl A 1) (t+a) (s,t))).symm
      exact detects_unique_of_next_filtration_zero
        (D.convergence (.quotient 1 (.shift (0,a) (.nu X)))) (s,t,t+a) hzero
        _ α β (hdetect α hα) (hdetect β hβ))

end
end KIP126.Comparison.ClassicalSynthetic.RealizationTower
