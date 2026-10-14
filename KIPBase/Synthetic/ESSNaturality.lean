import KIPBase.Synthetic.ExtensionSS

/-!
# Naturality of the canonical boundary ESS

Finite cycle and boundary arguments apply to unbounded filtrations. This
module provides the needed functorial construction outside the read-only
SpectralSequence directory, then applies it to actual lambda cofiber maps.
-/

namespace KIPBase.Synthetic.ESSNaturality

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem imageSubobjectMap_of_kernel_cokernel_square
    {A B A' B' V V' : C} {f : A ⟶ B} {f' : A' ⟶ B'}
    {left : A ⟶ A'} {right : B ⟶ B'}
    {p : A ⟶ V} {p' : A' ⟶ V'} {q : V ⟶ V'}
    (h : left ≫ f' = f ≫ right) (hp : left ≫ p' = p ≫ q) :
    ∃ k : Subobject.underlying.obj (imageSubobject ((kernelSubobject f).arrow ≫ p)) ⟶
      Subobject.underlying.obj (imageSubobject ((kernelSubobject f').arrow ≫ p')),
      k ≫ (imageSubobject ((kernelSubobject f').arrow ≫ p')).arrow =
        (imageSubobject ((kernelSubobject f).arrow ≫ p)).arrow ≫ q := by
  let a := kernelSubobjectMap (Arrow.homMk' left right h)
  have ha : a ≫ ((kernelSubobject f').arrow ≫ p') =
      ((kernelSubobject f).arrow ≫ p) ≫ q := by
    rw [← Category.assoc, kernelSubobjectMap_arrow]
    change ((kernelSubobject f).arrow ≫ left) ≫ p' = _
    rw [Category.assoc, hp, Category.assoc]
  exact ⟨imageSubobjectMap (Arrow.homMk' a q ha), imageSubobjectMap_arrow _⟩

theorem finiteCycles
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ) :
    ∃ (lift : Subobject.underlying.obj
          (X.cycleSubobject s k (n : WithTop ℕ)) ⟶
        Subobject.underlying.obj
          (Y.cycleSubobject s k (n : WithTop ℕ))),
      lift ≫ (Y.cycleSubobject s k (n : WithTop ℕ)).arrow =
        (X.cycleSubobject s k (n : WithTop ℕ)).arrow ≫
          g.assocGradedMap s k := by
  set u := (g.filt_compat s k).choose
  have hu := (g.filt_compat s k).choose_spec
  set πX := X.filToAssocGraded s k
  set πY := Y.filToAssocGraded s k
  have hπ : u ≫ πY = πX ≫ g.assocGradedMap s k := by
    unfold FilteredComplexMorphism.assocGradedMap πX πY
      FilteredComplex.filToAssocGraded
    exact (cokernel.π_desc _ _ _).symm
  set w := (g.filt_compat (s + ↑n) (k - 1)).choose
  have hw := (g.filt_compat (s + ↑n) (k - 1)).choose_spec
  set q := cokernel.map ((X.fil (s + ↑n) (k - 1)).arrow)
    ((Y.fil (s + ↑n) (k - 1)).arrow) w (g.f (k - 1)) hw.symm
  have hq : cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow) ≫ q =
      g.f (k - 1) ≫
        cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow) := by
    unfold q
    exact cokernel.π_desc _ _ _
  have hsquare : u ≫
      ((Y.fil s k).arrow ≫ Y.d k ≫
        cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow)) =
    ((X.fil s k).arrow ≫ X.d k ≫
        cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow)) ≫ q := by
    calc
      u ≫ (Y.fil s k).arrow ≫ Y.d k ≫
          cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow) =
        (X.fil s k).arrow ≫ g.f k ≫ Y.d k ≫
          cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow) := by
            rw [← Category.assoc, hu]
            simp only [Category.assoc]
      _ = (X.fil s k).arrow ≫ X.d k ≫ g.f (k - 1) ≫
          cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow) := by
            simpa only [Category.assoc] using congrArg
              (fun z => (X.fil s k).arrow ≫ z ≫
                cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow))
              (g.comm_d k)
      _ = (X.fil s k).arrow ≫ X.d k ≫
          cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow) ≫ q := by
            rw [hq]
      _ = ((X.fil s k).arrow ≫ X.d k ≫
          cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow)) ≫ q := by
            simp only [Category.assoc]
  change ∃ lift, lift ≫
      (imageSubobject
        ((kernelSubobject ((Y.fil s k).arrow ≫ Y.d k ≫
          cokernel.π ((Y.fil (s + ↑n) (k - 1)).arrow))).arrow ≫ πY)).arrow =
    (imageSubobject
      ((kernelSubobject ((X.fil s k).arrow ≫ X.d k ≫
        cokernel.π ((X.fil (s + ↑n) (k - 1)).arrow))).arrow ≫ πX)).arrow ≫
      g.assocGradedMap s k
  exact imageSubobjectMap_of_kernel_cokernel_square hsquare hπ

/-- 过滤复形态射把任意有限边缘层映入对应的有限边缘层。这里同样不需要有界性。 -/
theorem finiteBoundaries
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ) :
    ∃ (lift : Subobject.underlying.obj
          (X.boundarySubobject s k (n : WithTop ℕ)) ⟶
        Subobject.underlying.obj
          (Y.boundarySubobject s k (n : WithTop ℕ))),
      lift ≫ (Y.boundarySubobject s k (n : WithTop ℕ)).arrow =
        (X.boundarySubobject s k (n : WithTop ℕ)).arrow ≫
          g.assocGradedMap s k := by
  set u := (g.filt_compat s k).choose
  have hu := (g.filt_compat s k).choose_spec
  set πX := X.filToAssocGraded s k
  set πY := Y.filToAssocGraded s k
  have hπ : u ≫ πY = πX ≫ g.assocGradedMap s k := by
    unfold FilteredComplexMorphism.assocGradedMap πX πY
      FilteredComplex.filToAssocGraded
    exact (cokernel.π_desc _ _ _).symm
  have hd : g.f (k + 1) ≫ Y.dToK k = X.dToK k ≫ g.f k := by
    let e : k + 1 - 1 = k := by omega
    have ht : g.f (k + 1 - 1) ≫ eqToHom (congrArg Y.A e) =
        eqToHom (congrArg X.A e) ≫ g.f k :=
      eqToHom_naturality (fun j => g.f j) e
    unfold FilteredComplex.dToK
    rw [← Category.assoc, g.comm_d (k + 1), Category.assoc, ht]
    simp only [Category.assoc]
  let a : ℤ := s - (n : ℤ) + 1
  let q := (g.filt_compat a (k + 1)).choose
  have hq := (g.filt_compat a (k + 1)).choose_spec
  have hgen : q ≫ ((Y.fil a (k + 1)).arrow ≫ Y.dToK k) =
      ((X.fil a (k + 1)).arrow ≫ X.dToK k) ≫ g.f k := by
    rw [← Category.assoc, hq, Category.assoc, hd]
    simp only [Category.assoc]
  let imgX := imageSubobject ((X.fil a (k + 1)).arrow ≫ X.dToK k)
  let imgY := imageSubobject ((Y.fil a (k + 1)).arrow ≫ Y.dToK k)
  let IX := imgX ⊓ X.fil s k
  let IY := imgY ⊓ Y.fil s k
  let imgMap := imageSubobjectMap (Arrow.homMk' q (g.f k) hgen)
  have himg : imgMap ≫ imgY.arrow = imgX.arrow ≫ g.f k :=
    imageSubobjectMap_arrow _
  have hfacImg : imgY.Factors (IX.arrow ≫ g.f k) := by
    have hIX : imgX.Factors IX.arrow :=
      Subobject.inf_arrow_factors_left _ _
    rw [← Subobject.factorThru_arrow _ _ hIX, Category.assoc, ← himg]
    exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
  have hfacFil : (Y.fil s k).Factors (IX.arrow ≫ g.f k) := by
    have hIX : (X.fil s k).Factors IX.arrow :=
      Subobject.inf_arrow_factors_right _ _
    rw [← Subobject.factorThru_arrow _ _ hIX, Category.assoc, ← hu]
    exact Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow _)
  have hfacI : IY.Factors (IX.arrow ≫ g.f k) := by
    rw [show IY = imgY ⊓ Y.fil s k from rfl, Subobject.inf_factors]
    exact ⟨hfacImg, hfacFil⟩
  let α := IY.factorThru (IX.arrow ≫ g.f k) hfacI
  have hα : α ≫ IY.arrow = IX.arrow ≫ g.f k :=
    IY.factorThru_arrow _ hfacI
  have hmid : α ≫ Subobject.ofLE IY (Y.fil s k) inf_le_right =
      Subobject.ofLE IX (X.fil s k) inf_le_right ≫ u := by
    apply (cancel_mono (Y.fil s k).arrow).1
    calc
      (α ≫ Subobject.ofLE IY (Y.fil s k) inf_le_right) ≫
          (Y.fil s k).arrow = α ≫ IY.arrow := by
            rw [Category.assoc, Subobject.ofLE_arrow]
      _ = IX.arrow ≫ g.f k := hα
      _ = (Subobject.ofLE IX (X.fil s k) inf_le_right ≫ u) ≫
          (Y.fil s k).arrow := by
            rw [Category.assoc, hu, ← Category.assoc, Subobject.ofLE_arrow]
  have hsquare : α ≫
      (Subobject.ofLE IY (Y.fil s k) inf_le_right ≫ πY) =
    (Subobject.ofLE IX (X.fil s k) inf_le_right ≫ πX) ≫
      g.assocGradedMap s k := by
    rw [← Category.assoc, hmid, Category.assoc, hπ]
    simp only [Category.assoc]
  change ∃ lift, lift ≫
      (imageSubobject
        (Subobject.ofLE IY (Y.fil s k) inf_le_right ≫ πY)).arrow =
    (imageSubobject
      (Subobject.ofLE IX (X.fil s k) inf_le_right ≫ πX)).arrow ≫
      g.assocGradedMap s k
  exact ⟨imageSubobjectMap (Arrow.homMk' α (g.assocGradedMap s k) hsquare),
    imageSubobjectMap_arrow _⟩

/-- 过滤复形态射在有限页上的规范商映射；构造只依赖有限 `Z/B` 层。 -/
noncomputable def finitePageMap
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ) :
    X.finitePage s k n ⟶ Y.finitePage s k n :=
  cokernel.map
    (Subobject.ofLE (X.boundarySubobject s k (n : WithTop ℕ))
      (X.cycleSubobject s k (n : WithTop ℕ)) (X.B_le_Z_aux s k n))
    (Subobject.ofLE (Y.boundarySubobject s k (n : WithTop ℕ))
      (Y.cycleSubobject s k (n : WithTop ℕ)) (Y.B_le_Z_aux s k n))
    (finiteBoundaries g s k n).choose
    (finiteCycles g s k n).choose
    (by
      apply (cancel_mono
        (Y.cycleSubobject s k (n : WithTop ℕ)).arrow).1
      simp only [Category.assoc,
        (finiteCycles g s k n).choose_spec,
        Subobject.ofLE_arrow,
        (finiteBoundaries g s k n).choose_spec,
        Subobject.ofLE_arrow_assoc])

/-- 有限页规范映射与循环层到页的商投影交换。 -/
theorem finitePageπ_naturality
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (s k : ℤ) (n : ℕ) :
    X.finitePageπ s k n ≫ finitePageMap g s k n =
      (finiteCycles g s k n).choose ≫
        Y.finitePageπ s k n := by
  simp [finitePageMap, FilteredComplex.finitePageπ]


/-- The original zeroth-page comparison sends a cycle to its ambient class. -/
theorem finitePageπ_zeroIso (X : FilteredComplex C) (s k : ℤ) :
    X.finitePageπ s k 0 ≫ (X.finitePageZeroIso s k).hom =
      (X.cycleSubobject s k (0 : WithTop ℕ)).arrow := by
  simp [FilteredComplex.finitePageZeroIso, FilteredComplex.finitePageπ,
    Category.assoc, cokernel.mapIso]
  exact Subobject.arrow_congr _ _ (X.cycleSubobject_zero_eq_top s k)
/-- The finite zeroth-page comparison is natural in filtered chain maps. -/
theorem finitePageMap_zeroIso {X Y : FilteredComplex C}
    (a : FilteredComplexMorphism X Y) (s k : ℤ) :
    finitePageMap a s k 0 ≫ (Y.finitePageZeroIso s k).hom =
      (X.finitePageZeroIso s k).hom ≫ a.assocGradedMap s k := by
  haveI : Epi (X.finitePageπ s k 0) := by
    dsimp only [FilteredComplex.finitePageπ]
    infer_instance
  apply (cancel_epi (X.finitePageπ s k 0)).mp
  rw [← Category.assoc, finitePageπ_naturality, Category.assoc,
    finitePageπ_zeroIso, ← Category.assoc, finitePageπ_zeroIso]
  exact (finiteCycles a s k 0).choose_spec

theorem finitePageMap_comm_d
    {X Y : FilteredComplex C} (g : FilteredComplexMorphism X Y)
    (n : ℕ) (s k : ℤ) :
    finitePageMap g s k n ≫
        Y.finitePageDifferential s k n =
      X.finitePageDifferential s k n ≫
        finitePageMap g (s + (n : ℤ)) (k - 1) n := by
  classical
  let fX := (X.fil s k).arrow ≫ X.d k ≫
    cokernel.π ((X.fil (s + (n : ℤ)) (k - 1)).arrow)
  let fY := (Y.fil s k).arrow ≫ Y.d k ≫
    cokernel.π ((Y.fil (s + (n : ℤ)) (k - 1)).arrow)
  let KX := kernelSubobject fX
  let KY := kernelSubobject fY
  let πX := X.filToAssocGraded s k
  let πY := Y.filToAssocGraded s k
  let ZX := imageSubobject (KX.arrow ≫ πX)
  let ZY := imageSubobject (KY.arrow ≫ πY)
  let qX := factorThruImageSubobject (KX.arrow ≫ πX)
  let u := (g.filt_compat s k).choose
  have huspec : u ≫ (Y.fil s k).arrow =
      (X.fil s k).arrow ≫ g.f k :=
    (g.filt_compat s k).choose_spec
  let w := (g.filt_compat (s + (n : ℤ)) (k - 1)).choose
  have hwspec : w ≫ (Y.fil (s + (n : ℤ)) (k - 1)).arrow =
      (X.fil (s + (n : ℤ)) (k - 1)).arrow ≫ g.f (k - 1) :=
    (g.filt_compat (s + (n : ℤ)) (k - 1)).choose_spec
  have hφs : πX ≫ FilteredComplexMorphism.assocGradedMap
      (g : FilteredComplexMorphism X Y) s k = u ≫ πY := by
    unfold FilteredComplexMorphism.assocGradedMap πX πY
      FilteredComplex.filToAssocGraded
    exact cokernel.π_desc _ _ _
  let cokT := cokernel.map
    ((X.fil (s + (n : ℤ)) (k - 1)).arrow)
    ((Y.fil (s + (n : ℤ)) (k - 1)).arrow)
    w (g.f (k - 1)) hwspec.symm
  have hcokT : cokernel.π ((X.fil (s + (n : ℤ)) (k - 1)).arrow) ≫ cokT =
      g.f (k - 1) ≫
        cokernel.π ((Y.fil (s + (n : ℤ)) (k - 1)).arrow) := by
    unfold cokT
    exact cokernel.π_desc _ _ _
  have hkernel : u ≫ fY = fX ≫ cokT := by
    dsimp only [fX, fY]
    calc
      u ≫ (Y.fil s k).arrow ≫ Y.d k ≫
          cokernel.π ((Y.fil (s + (n : ℤ)) (k - 1)).arrow) =
        (X.fil s k).arrow ≫ g.f k ≫ Y.d k ≫
          cokernel.π ((Y.fil (s + (n : ℤ)) (k - 1)).arrow) := by
            rw [← Category.assoc, huspec]
            simp only [Category.assoc]
      _ = (X.fil s k).arrow ≫ X.d k ≫ g.f (k - 1) ≫
          cokernel.π ((Y.fil (s + (n : ℤ)) (k - 1)).arrow) := by
            simpa only [Category.assoc] using congrArg
              (fun h => (X.fil s k).arrow ≫ h ≫
                cokernel.π ((Y.fil (s + (n : ℤ)) (k - 1)).arrow))
              (g.comm_d k)
      _ = (X.fil s k).arrow ≫ X.d k ≫
          cokernel.π ((X.fil (s + (n : ℤ)) (k - 1)).arrow) ≫ cokT := by
            rw [hcokT]
      _ = ((X.fil s k).arrow ≫ X.d k ≫
          cokernel.π ((X.fil (s + (n : ℤ)) (k - 1)).arrow)) ≫ cokT := by
            simp only [Category.assoc]
  let kerMap := kernelSubobjectMap
    (Arrow.homMk (f := Arrow.mk fX) (g := Arrow.mk fY) u cokT hkernel)
  have hkerMap : kerMap ≫ KY.arrow = KX.arrow ≫ u := by
    exact kernelSubobjectMap_arrow _
  let qY := kerMap ≫ factorThruImageSubobject (KY.arrow ≫ πY)
  let zmapS := (finiteCycles g s k n).choose
  have hqX : qX ≫ ZX.arrow = KX.arrow ≫ πX := by
    simp only [qX, ZX, imageSubobject_arrow_comp]
  have hqY : qY ≫ ZY.arrow = KX.arrow ≫ u ≫ πY := by
    calc
      qY ≫ ZY.arrow = (kerMap ≫ KY.arrow) ≫ πY := by
        simp only [qY, ZY, Category.assoc, imageSubobject_arrow_comp]
      _ = (KX.arrow ≫ u) ≫ πY := by rw [hkerMap]
      _ = KX.arrow ≫ u ≫ πY := by simp only [Category.assoc]
  have hzmapS : qX ≫ zmapS = qY := by
    apply (cancel_mono ZY.arrow).mp
    have hzspec := (finiteCycles g s k n).choose_spec
    change zmapS ≫ ZY.arrow = ZX.arrow ≫
      FilteredComplexMorphism.assocGradedMap
        (g : FilteredComplexMorphism X Y) s k at hzspec
    calc
      (qX ≫ zmapS) ≫ ZY.arrow = qX ≫ ZX.arrow ≫
          FilteredComplexMorphism.assocGradedMap
            (g : FilteredComplexMorphism X Y) s k := by
              rw [Category.assoc, hzspec]
      _ = KX.arrow ≫ πX ≫
          FilteredComplexMorphism.assocGradedMap
            (g : FilteredComplexMorphism X Y) s k := by
              simpa only [Category.assoc] using congrArg
                (fun h => h ≫ FilteredComplexMorphism.assocGradedMap
                  (g : FilteredComplexMorphism X Y) s k) hqX
      _ = KX.arrow ≫ u ≫ πY := by rw [hφs]
      _ = qY ≫ ZY.arrow := hqY.symm
  let vX := Abelian.monoLift (X.fil (s + (n : ℤ)) (k - 1)).arrow
    (KX.arrow ≫ (X.fil s k).arrow ≫ X.d k)
    (by simpa only [fX, Category.assoc] using kernelSubobject_arrow_comp fX)
  have hvX : vX ≫ (X.fil (s + (n : ℤ)) (k - 1)).arrow =
      KX.arrow ≫ (X.fil s k).arrow ≫ X.d k :=
    Abelian.monoLift_comp _ _ _
  let vY := vX ≫ w
  have hvY : kerMap ≫ KY.arrow ≫ (Y.fil s k).arrow ≫ Y.d k =
      vY ≫ (Y.fil (s + (n : ℤ)) (k - 1)).arrow := by
    calc
      kerMap ≫ KY.arrow ≫ (Y.fil s k).arrow ≫ Y.d k =
          KX.arrow ≫ u ≫ (Y.fil s k).arrow ≫ Y.d k := by
            simpa only [Category.assoc] using congrArg
              (fun h => h ≫ (Y.fil s k).arrow ≫ Y.d k) hkerMap
      _ = KX.arrow ≫ (X.fil s k).arrow ≫ g.f k ≫ Y.d k := by
            simpa only [Category.assoc] using congrArg
              (fun h => KX.arrow ≫ h ≫ Y.d k) huspec
      _ = KX.arrow ≫ (X.fil s k).arrow ≫ X.d k ≫ g.f (k - 1) := by
            simpa only [Category.assoc] using congrArg
              (fun h => KX.arrow ≫ (X.fil s k).arrow ≫ h) (g.comm_d k)
      _ = vX ≫ (X.fil (s + (n : ℤ)) (k - 1)).arrow ≫ g.f (k - 1) := by
            simpa only [Category.assoc] using congrArg
              (fun h => h ≫ g.f (k - 1)) hvX.symm
      _ = vX ≫ w ≫ (Y.fil (s + (n : ℤ)) (k - 1)).arrow := by
            simpa only [Category.assoc] using congrArg (fun h => vX ≫ h) hwspec.symm
      _ = vY ≫ (Y.fil (s + (n : ℤ)) (k - 1)).arrow := by
            simp only [vY, Category.assoc]
  let gX := (X.fil (s + (n : ℤ)) (k - 1)).arrow ≫ X.d (k - 1) ≫
    cokernel.π ((X.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow)
  let gY := (Y.fil (s + (n : ℤ)) (k - 1)).arrow ≫ Y.d (k - 1) ≫
    cokernel.π ((Y.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow)
  have hvgX : vX ≫ gX = 0 := by
    dsimp only [gX]
    calc
      vX ≫ (X.fil (s + (n : ℤ)) (k - 1)).arrow ≫ X.d (k - 1) ≫
          cokernel.π ((X.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow) =
        (KX.arrow ≫ (X.fil s k).arrow ≫ X.d k) ≫ X.d (k - 1) ≫
          cokernel.π ((X.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow) := by
            simpa only [Category.assoc] using congrArg
              (fun h => h ≫ X.d (k - 1) ≫
                cokernel.π
                  ((X.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow)) hvX
      _ = 0 := by
        simpa only [Category.assoc, comp_zero, zero_comp] using congrArg
          (fun h => KX.arrow ≫ (X.fil s k).arrow ≫ h ≫
            cokernel.π
              ((X.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow))
          (X.d_comp_d k)
  have hvgY : vY ≫ gY = 0 := by
    dsimp only [gY]
    calc
      vY ≫ (Y.fil (s + (n : ℤ)) (k - 1)).arrow ≫ Y.d (k - 1) ≫
          cokernel.π ((Y.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow) =
        (kerMap ≫ KY.arrow ≫ (Y.fil s k).arrow ≫ Y.d k) ≫
          Y.d (k - 1) ≫
          cokernel.π ((Y.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow) := by
            simpa only [Category.assoc] using congrArg
              (fun h => h ≫ Y.d (k - 1) ≫
                cokernel.π
                  ((Y.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow)) hvY.symm
      _ = 0 := by
        simpa only [Category.assoc, comp_zero, zero_comp] using congrArg
          (fun h => kerMap ≫ KY.arrow ≫ (Y.fil s k).arrow ≫ h ≫
            cokernel.π
              ((Y.fil (s + (n : ℤ) + (n : ℤ)) (k - 1 - 1)).arrow))
          (Y.d_comp_d k)
  let KX' := kernelSubobject gX
  let KY' := kernelSubobject gY
  let πX' := X.filToAssocGraded (s + (n : ℤ)) (k - 1)
  let πY' := Y.filToAssocGraded (s + (n : ℤ)) (k - 1)
  let qX' := factorThruKernelSubobject gX vX hvgX ≫
    factorThruImageSubobject (KX'.arrow ≫ πX')
  let qY' := factorThruKernelSubobject gY vY hvgY ≫
    factorThruImageSubobject (KY'.arrow ≫ πY')
  let ZX' := imageSubobject (KX'.arrow ≫ πX')
  let ZY' := imageSubobject (KY'.arrow ≫ πY')
  let zmapT := (finiteCycles g (s + (n : ℤ)) (k - 1) n).choose
  have hqX' : qX' ≫ ZX'.arrow = vX ≫ πX' := by
    dsimp only [qX', ZX']
    rw [Category.assoc, imageSubobject_arrow_comp, ← Category.assoc,
      factorThruKernelSubobject_comp_arrow]
  have hqY' : qY' ≫ ZY'.arrow = vX ≫ w ≫ πY' := by
    dsimp only [qY', ZY']
    rw [Category.assoc, imageSubobject_arrow_comp, ← Category.assoc,
      factorThruKernelSubobject_comp_arrow]
    simp only [vY, Category.assoc]
  have hzmapT : qX' ≫ zmapT = qY' := by
    apply (cancel_mono ZY'.arrow).mp
    have hzspec := (finiteCycles g (s + (n : ℤ)) (k - 1) n).choose_spec
    change zmapT ≫ ZY'.arrow = ZX'.arrow ≫
        FilteredComplexMorphism.assocGradedMap
          (g : FilteredComplexMorphism X Y) (s + (n : ℤ)) (k - 1) at hzspec
    have hφt : πX' ≫ FilteredComplexMorphism.assocGradedMap
        (g : FilteredComplexMorphism X Y) (s + (n : ℤ)) (k - 1) =
        w ≫ πY' := by
      unfold FilteredComplexMorphism.assocGradedMap πX' πY'
        FilteredComplex.filToAssocGraded
      exact cokernel.π_desc _ _ _
    calc
      (qX' ≫ zmapT) ≫
          ZY'.arrow =
        qX' ≫ ZX'.arrow ≫
          FilteredComplexMorphism.assocGradedMap
            (g : FilteredComplexMorphism X Y) (s + (n : ℤ)) (k - 1) := by
              rw [Category.assoc, hzspec]
      _ = vX ≫ πX' ≫ FilteredComplexMorphism.assocGradedMap
          (g : FilteredComplexMorphism X Y) (s + (n : ℤ)) (k - 1) := by
            simpa only [Category.assoc] using congrArg
              (fun h => h ≫ FilteredComplexMorphism.assocGradedMap
                (g : FilteredComplexMorphism X Y)
                (s + (n : ℤ)) (k - 1)) hqX'
      _ = vX ≫ w ≫ πY' := by rw [hφt]
      _ = qY' ≫ ZY'.arrow := hqY'.symm
  haveI : Epi (X.finitePageπ s k n) := by
    unfold FilteredComplex.finitePageπ
    infer_instance
  apply (cancel_epi (X.finitePageπ s k n)).mp
  apply (cancel_epi qX).mp
  have hY := Y.finitePageDifferential_on_kernel s k n kerMap vY hvY hvgY
  have hX := X.finitePageDifferential_on_kernel s k n
    (𝟙 (Subobject.underlying.obj KX)) vX
    (by simpa only [Category.id_comp] using hvX.symm) hvgX
  change qY ≫ Y.finitePageπ s k n ≫
      Y.finitePageDifferential s k n =
    qY' ≫ Y.finitePageπ (s + (n : ℤ)) (k - 1) n at hY
  change ((𝟙 (Subobject.underlying.obj KX)) ≫ qX) ≫
      X.finitePageπ s k n ≫
      X.finitePageDifferential s k n =
    qX' ≫ X.finitePageπ (s + (n : ℤ)) (k - 1) n at hX
  simp only [Category.id_comp] at hX
  have hPageS := finitePageπ_naturality g s k n
  have hPageT := finitePageπ_naturality g (s + (n : ℤ)) (k - 1) n
  calc
    qX ≫ X.finitePageπ s k n ≫
        finitePageMap g s k n ≫
        Y.finitePageDifferential s k n =
      qX ≫ zmapS ≫ Y.finitePageπ s k n ≫
        Y.finitePageDifferential s k n := by
          simpa only [Category.assoc] using congrArg
            (fun h => qX ≫ h ≫ Y.finitePageDifferential s k n) hPageS
    _ = qY ≫ Y.finitePageπ s k n ≫
        Y.finitePageDifferential s k n := by
          simpa only [Category.assoc] using congrArg
            (fun h => h ≫ Y.finitePageπ s k n ≫
              Y.finitePageDifferential s k n) hzmapS
    _ = qY' ≫ Y.finitePageπ (s + (n : ℤ)) (k - 1) n := by
          simpa only [Category.assoc] using hY
    _ = qX' ≫ zmapT ≫
        Y.finitePageπ (s + (n : ℤ)) (k - 1) n := by
          simpa only [Category.assoc] using congrArg
            (fun h => h ≫
              Y.finitePageπ (s + (n : ℤ)) (k - 1) n)
            hzmapT.symm
    _ = qX' ≫ X.finitePageπ (s + (n : ℤ)) (k - 1) n ≫
        finitePageMap g (s + (n : ℤ)) (k - 1) n := by
          simpa only [Category.assoc] using congrArg (fun h => qX' ≫ h) hPageT.symm
    _ = qX ≫ X.finitePageπ s k n ≫
        X.finitePageDifferential s k n ≫
        finitePageMap g (s + (n : ℤ)) (k - 1) n := by
          simpa only [Category.assoc] using congrArg
            (fun h => h ≫
              finitePageMap g (s + (n : ℤ)) (k - 1) n)
            hX.symm


/-! ## Infinite layers and the actual ESS ambient objects -/

private theorem preserves_top_cycles {D E : SSData C} (f : D.V ⟶ E.V)
    (h : ∀ n : ℕ, ∃ a : Subobject.underlying.obj (D.Z n) ⟶
      Subobject.underlying.obj (E.Z n), a ≫ (E.Z n).arrow = (D.Z n).arrow ≫ f) :
    ∃ a : Subobject.underlying.obj (D.Z ⊤) ⟶ Subobject.underlying.obj (E.Z ⊤),
      a ≫ (E.Z ⊤).arrow = (D.Z ⊤).arrow ≫ f := by
  let I := imageSubobject ((D.Z ⊤).arrow ≫ f)
  have hI : I ≤ E.Z ⊤ := by
    apply E.Z_top_greatest
    intro n
    obtain ⟨a, ha⟩ := h n
    apply imageSubobject_le _ (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ a)
    rw [Category.assoc, ha, ← Category.assoc, Subobject.ofLE_arrow]
  exact ⟨factorThruImageSubobject ((D.Z ⊤).arrow ≫ f) ≫ Subobject.ofLE I _ hI,
    by rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]⟩

private theorem preserves_top_boundaries {D E : SSData C} (f : D.V ⟶ E.V)
    (h : ∀ n : ℕ, ∃ a : Subobject.underlying.obj (D.B n) ⟶
      Subobject.underlying.obj (E.B n), a ≫ (E.B n).arrow = (D.B n).arrow ≫ f) :
    ∃ a : Subobject.underlying.obj (D.B ⊤) ⟶ Subobject.underlying.obj (E.B ⊤),
      a ≫ (E.B ⊤).arrow = (D.B ⊤).arrow ≫ f := by
  let P := (Subobject.pullback f).obj (E.B ⊤)
  have hP : D.B ⊤ ≤ P := by
    apply D.B_top_least
    intro n
    apply Subobject.le_of_factors
    apply pullback_factors
    apply Subobject.factors_of_le _ (E.B_mono le_top)
    exact Subobject.factors_iff _ _ |>.mpr (h n)
  apply Subobject.factors_iff _ _ |>.mp
  exact (pullback_factors_iff f (E.B ⊤) (D.B ⊤).arrow).mp
    (Subobject.factors_of_le _ hP (Subobject.factors_self _))

private noncomputable def dataComp
    {D E F : ℤ × ℤ → SSData C}
    (f : SSDataMorphism (ℤ × ℤ) D E) (g : SSDataMorphism (ℤ × ℤ) E F) :
    SSDataMorphism (ℤ × ℤ) D F where
  φ k := f.φ k ≫ g.φ k
  preserves_Z k n := ⟨(f.preserves_Z k n).choose ≫ (g.preserves_Z k n).choose, by
    rw [Category.assoc, (g.preserves_Z k n).choose_spec, ← Category.assoc,
      (f.preserves_Z k n).choose_spec, Category.assoc]⟩
  preserves_B k n := ⟨(f.preserves_B k n).choose ≫ (g.preserves_B k n).choose, by
    rw [Category.assoc, (g.preserves_B k n).choose_spec, ← Category.assoc,
      (f.preserves_B k n).choose_spec, Category.assoc]⟩

private theorem dataComp_pageMap
    {D E F : ℤ × ℤ → SSData C}
    (f : SSDataMorphism (ℤ × ℤ) D E) (g : SSDataMorphism (ℤ × ℤ) E F)
    (k : ℤ × ℤ) (n : WithTop ℕ) :
    (dataComp f g).pageMap k n = f.pageMap k n ≫ g.pageMap k n :=
  SSDataMorphism.pageMap_eq_comp f g (dataComp f g) k n rfl

section Extension

variable [LocallySmall.{v} C] [WellPowered.{v} C]
    [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]
    {V₁ V₂ V₃ V₄ : ConvergingSS C (ℤ × ℤ × ℤ) (ℤ × ℤ)}

/-- A filtered chain map induces maps on all finite and infinite cycle and
boundary layers in the complex presentation of the extension SS. -/
noncomputable def complexDataMap (f : V₁ ⟶ V₂) (g : V₃ ⟶ V₄) (t : ℤ × ℤ)
    (a : FilteredComplexMorphism (unboundedUnderlyingComplex f t)
      (unboundedUnderlyingComplex g t)) :
    SSDataMorphism (ℤ × ℤ) (unboundedComplexSSDataFamily f t)
      (unboundedComplexSSDataFamily g t) where
  φ k := a.assocGradedMap k.1 k.2
  preserves_Z := by
    rintro ⟨s, k⟩ n
    cases n with
    | top => exact preserves_top_cycles _ (fun n => finiteCycles a s k n)
    | coe n => exact finiteCycles a s k n
  preserves_B := by
    rintro ⟨s, k⟩ n
    cases n with
    | top => exact preserves_top_boundaries _ (fun n => finiteBoundaries a s k n)
    | coe n => exact finiteBoundaries a s k n

theorem complexDataMap_pageMap (f : V₁ ⟶ V₂) (g : V₃ ⟶ V₄) (t : ℤ × ℤ)
    (a : FilteredComplexMorphism (unboundedUnderlyingComplex f t)
      (unboundedUnderlyingComplex g t)) (s k : ℤ) (n : ℕ) :
    (complexDataMap f g t a).pageMap (s, k) n = finitePageMap a s k n := rfl

/-- The ambient map is transported back to the canonical ESS's original
E-infinity objects. Its cycle and boundary maps are therefore genuine
maps of the existing ESS data, including the infinite layers. -/
noncomputable def dataMap (f : V₁ ⟶ V₂) (g : V₃ ⟶ V₄) (t : ℤ × ℤ)
    (a : FilteredComplexMorphism (unboundedUnderlyingComplex f t)
      (unboundedUnderlyingComplex g t)) :
    SSDataMorphism (ℤ × ℤ) (unboundedExtensionSSData f t)
      (unboundedExtensionSSData g t) :=
  dataComp (dataComp (unboundedSSDataForward f t) (complexDataMap f g t a))
    (unboundedSSDataBackward g t)

theorem dataMap_pageMap (f : V₁ ⟶ V₂) (g : V₃ ⟶ V₄) (t : ℤ × ℤ)
    (a : FilteredComplexMorphism (unboundedUnderlyingComplex f t)
      (unboundedUnderlyingComplex g t)) (s k : ℤ) (n : ℕ) :
    (dataMap f g t a).pageMap (s, k) n =
      (unboundedExtensionPageIso f t (s, k) n).hom ≫ finitePageMap a s k n ≫
        (unboundedExtensionPageIso g t (s, k) n).inv := by
  rw [dataMap, dataComp_pageMap, dataComp_pageMap, complexDataMap_pageMap,
    Category.assoc]
  rfl

/-- Every filtered chain map gives a morphism between the canonical
unbounded extension spectral sequences. There is no boundedness input. -/
noncomputable def spectralMap (f : V₁ ⟶ V₂) (g : V₃ ⟶ V₄) (t : ℤ × ℤ)
    (a : FilteredComplexMorphism (unboundedUnderlyingComplex f t)
      (unboundedUnderlyingComplex g t)) :
    ExtensionSpectralSequence f t ⟶ ExtensionSpectralSequence g t where
  toSSDataMorphism := dataMap f g t a
  r₀_eq := rfl
  diffDeg_eq := rfl
  comm_d := by
    intro r ⟨s, k⟩
    simp only [SSDataMorphism.pageMapOfEq, eqToHom_refl, Category.comp_id]
    by_cases hr : 0 ≤ r
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
      change (dataMap f g t a).pageMap (s, k) n ≫
          (ExtensionSpectralSequence g t).d (n : ℤ) (s, k) =
        (ExtensionSpectralSequence f t).d (n : ℤ) (s, k) ≫
          (dataMap f g t a).pageMap (s + (n : ℤ), k - 1) n
      rw [dataMap_pageMap, dataMap_pageMap,
        ExtensionSpectralSequence_d_nat, ExtensionSpectralSequence_d_nat]
      simp only [unboundedExtensionDifferential, Category.assoc, Iso.inv_hom_id_assoc]
      change _ ≫ finitePageMap a s k n ≫
          (unboundedUnderlyingComplex g t).finitePageDifferential s k n ≫ _ =
        _ ≫ (unboundedUnderlyingComplex f t).finitePageDifferential s k n ≫
          finitePageMap a (s + (n : ℤ)) (k - 1) n ≫ _
      rw [← Category.assoc (finitePageMap a s k n), finitePageMap_comm_d]
      simp only [Category.assoc]
    · rw [ExtensionSpectralSequence_d_neg g t r (by omega),
        ExtensionSpectralSequence_d_neg f t r (by omega), comp_zero, zero_comp]

/-- Page maps commute with differentials with the canonical ESS indices. -/
theorem spectralMap_pageMap_comm_d (f : V₁ ⟶ V₂) (g : V₃ ⟶ V₄) (t : ℤ × ℤ)
    (a : FilteredComplexMorphism (unboundedUnderlyingComplex f t)
      (unboundedUnderlyingComplex g t)) (r : ℤ) (k : ℤ × ℤ) :
    (spectralMap f g t a).toSSDataMorphism.pageMap k (↑(r - 0).toNat) ≫
        (ExtensionSpectralSequence g t).d r k =
      (ExtensionSpectralSequence f t).d r k ≫
        (spectralMap f g t a).toSSDataMorphism.pageMap
          (k + (r, -1)) (↑(r - 0).toNat) := by
  simpa only [SSDataMorphism.pageMapOfEq, eqToHom_refl, Category.comp_id,
    ExtensionSpectralSequence_r₀, ExtensionSpectralSequence_diffDeg] using
      (spectralMap f g t a).comm_d r k

/-- The ambient map is the actual associated-graded map transported through
convergence, so its action is fixed before passing to page quotients. -/
theorem spectralMap_ambient (f : V₁ ⟶ V₂) (g : V₃ ⟶ V₄) (t : ℤ × ℤ)
    (a : FilteredComplexMorphism (unboundedUnderlyingComplex f t)
      (unboundedUnderlyingComplex g t)) (s k : ℤ) :
    (spectralMap f g t a).φ (s, k) ≫ (unboundedExtensionVComplexIso g t s k).hom =
      (unboundedExtensionVComplexIso f t s k).hom ≫ a.assocGradedMap s k := by
  change (((unboundedExtensionVComplexIso f t s k).hom ≫ a.assocGradedMap s k) ≫
    (unboundedExtensionVComplexIso g t s k).inv) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The canonical ESS zeroth-page comparison commutes with the actual
associated-graded map. -/
theorem spectralMap_e0Iso (f : V₁ ⟶ V₂) (g : V₃ ⟶ V₄) (t : ℤ × ℤ)
    (a : FilteredComplexMorphism (unboundedUnderlyingComplex f t)
      (unboundedUnderlyingComplex g t)) (s k : ℤ) :
    (spectralMap f g t a).toSSDataMorphism.pageMap (s, k) 0 ≫
        (extensionE0IsoAssociatedGraded g t s k).hom =
      (extensionE0IsoAssociatedGraded f t s k).hom ≫ a.assocGradedMap s k := by
  change (dataMap f g t a).pageMap (s, k) (↑(0 : ℕ)) ≫ _ = _
  rw [dataMap_pageMap]
  simp only [extensionE0IsoAssociatedGraded, Iso.trans_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [finitePageMap_zeroIso]

/-- The induced morphism carries the specified source and target of an ESS
differential relation to their images under the same ambient map. -/
theorem spectralMap_relation (f : V₁ ⟶ V₂) (g : V₃ ⟶ V₄) (t : ℤ × ℤ)
    (a : FilteredComplexMorphism (unboundedUnderlyingComplex f t)
      (unboundedUnderlyingComplex g t)) (r : ℤ) (k : ℤ × ℤ) {T : C}
    {x : T ⟶ (unboundedExtensionSSData f t k).V}
    {y : T ⟶ (unboundedExtensionSSData f t (k + (r, -1))).V}
    (h : DifferentialRelation (ExtensionSpectralSequence f t) r k x y) :
    DifferentialRelation (ExtensionSpectralSequence g t) r k
      (x ≫ (spectralMap f g t a).φ k)
      (y ≫ (spectralMap f g t a).φ (k + (r, -1))) := by
  let F := spectralMap f g t a
  let n : WithTop ℕ := ↑(r - 0).toNat
  unfold DifferentialRelation at h ⊢
  simp only [ExtensionSpectralSequence_r₀, ExtensionSpectralSequence_diffDeg] at h ⊢
  obtain ⟨xZ, hx, yZ, hy, hd⟩ := h
  let u := (F.preserves_Z k n).choose
  let v := (F.preserves_Z (k + (r, -1)) n).choose
  have hu := (F.preserves_Z k n).choose_spec
  have hv := (F.preserves_Z (k + (r, -1)) n).choose_spec
  refine ⟨xZ ≫ u, ?_, yZ ≫ v, ?_, ?_⟩
  · rw [Category.assoc, hu, ← Category.assoc, hx]
  · rw [Category.assoc, hv, ← Category.assoc, hy]
  · have hc : F.toSSDataMorphism.pageMap k n ≫
        (ExtensionSpectralSequence g t).d r k =
      (ExtensionSpectralSequence f t).d r k ≫
        F.toSSDataMorphism.pageMap (k + (r, -1)) n := by
      simpa only [SSDataMorphism.pageMapOfEq, eqToHom_refl, Category.comp_id,
        ExtensionSpectralSequence_r₀, ExtensionSpectralSequence_diffDeg] using F.comm_d r k
    have hp := F.toSSDataMorphism.pageπ_pageMap k n
    have hq := F.toSSDataMorphism.pageπ_pageMap (k + (r, -1)) n
    change (xZ ≫ u) ≫ ((ExtensionSpectralSequence g t).ssData k).pageπ n ≫ _ =
      (yZ ≫ v) ≫ ((ExtensionSpectralSequence g t).ssData (k + (r, -1))).pageπ n
    calc
      _ = xZ ≫ ((ExtensionSpectralSequence f t).ssData k).pageπ n ≫
          F.toSSDataMorphism.pageMap k n ≫ (ExtensionSpectralSequence g t).d r k := by
        simpa only [Category.assoc] using
          congrArg (fun z => xZ ≫ z ≫ (ExtensionSpectralSequence g t).d r k) hp.symm
      _ = xZ ≫ ((ExtensionSpectralSequence f t).ssData k).pageπ n ≫
          (ExtensionSpectralSequence f t).d r k ≫
          F.toSSDataMorphism.pageMap (k + (r, -1)) n := by rw [hc]
      _ = yZ ≫ ((ExtensionSpectralSequence f t).ssData (k + (r, -1))).pageπ n ≫
          F.toSSDataMorphism.pageMap (k + (r, -1)) n := by
        simpa only [Category.assoc] using
          congrArg (fun z => z ≫ F.toSSDataMorphism.pageMap (k + (r, -1)) n) hd
      _ = _ := by rw [hq, ← Category.assoc]


end Extension

end KIPBase.Synthetic.ESSNaturality
