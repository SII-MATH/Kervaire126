import KIP126.Mathlib.SpectralSequence.FilteredComplex.Relations.Predicates
import KIP126.Def.SpectralSequence.FilteredDifferential.Proofs

/-!
# Proofs for filtered-complex/page relations

These comparison lemmas concern only the canonical quotient pages. The
representative-level relation and crossing argument remain in `Def`.
-/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits
open KIP126.Core.Algebra

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace PageView

variable {FC : FilteredComplex C} (P : PageView FC)

/-- On a quotient page the differential has a unique target.  The historical
crossing argument instead uses representatives in the associated graded,
where two targets may differ by a boundary. -/
theorem relation_target_unique
    {r : ℤ} {hr : P.firstPage ≤ r} {s k : ℤ} {T : C}
    {x : P.element r hr s k T}
    {y₁ y₂ : P.element r hr (s + r) (k - 1) T}
    (h₁ : P.relation r hr s k x y₁)
    (h₂ : P.relation r hr s k x y₂) : y₁ = y₂ := by
  exact h₁.symm.trans h₂

/-- Two lifts of one page element differ by a map through the page boundary. -/
theorem isLift_sub_factors_boundary
    {r : ℤ} {hr : P.firstPage ≤ r} {s k : ℤ} {T : C}
    {x : P.element r hr s k T}
    {xl₁ xl₂ : T ⟶ Subobject.underlying.obj (FC.filtration.F s k)}
    (h₁ : P.IsLift r hr s k xl₁ x)
    (h₂ : P.IsLift r hr s k xl₂ x) :
    (FC.boundarySubobject s k (P.pageNumber r hr)).Factors
      ((xl₁ - xl₂) ≫ FC.filtration.toAssociatedGraded s k) := by
  rcases h₁ with ⟨z₁, hz₁, hp₁⟩
  rcases h₂ with ⟨z₂, hz₂, hp₂⟩
  let B := FC.boundarySubobject s k (P.pageNumber r hr)
  let Z := FC.cycleSubobject s k (P.pageNumber r hr)
  let hBZ := FC.B_le_Z_aux s k (P.pageNumber r hr)
  let ι := Subobject.ofLE B Z hBZ
  have hpage : (z₁ - z₂) ≫ FC.pageπ s k (P.pageNumber r hr) = 0 := by
    rw [Preadditive.sub_comp, hp₁, hp₂, sub_self]
  let w : T ⟶ Subobject.underlying.obj B :=
    Abelian.monoLift ι (z₁ - z₂) hpage
  have hw : w ≫ ι = z₁ - z₂ :=
    Abelian.monoLift_comp ι (z₁ - z₂) hpage
  have hdiff :
      (xl₁ - xl₂) ≫ FC.filtration.toAssociatedGraded s k =
        w ≫ B.arrow := by
    calc
      (xl₁ - xl₂) ≫ FC.filtration.toAssociatedGraded s k =
          (xl₁ ≫ FC.filtration.toAssociatedGraded s k) -
            (xl₂ ≫ FC.filtration.toAssociatedGraded s k) := by
              rw [Preadditive.sub_comp]
      _ = (z₁ ≫ Z.arrow) - (z₂ ≫ Z.arrow) := by rw [← hz₁, ← hz₂]
      _ = (z₁ - z₂) ≫ Z.arrow := by rw [← Preadditive.sub_comp]
      _ = w ≫ ι ≫ Z.arrow := by rw [← hw, Category.assoc]
      _ = w ≫ B.arrow := by rw [Subobject.ofLE_arrow hBZ]
  rw [hdiff]
  exact Subobject.factors_comp_arrow w

end PageView

/-! The following three declarations are internal relation lemmas, not
challenge milestones. -/

theorem differentialRelationOfLift
    (FC : FilteredComplex C) (P : PageView FC)
    (hP : P = PageView.canonical FC)
    (_bnd : FC.filtration.IsBounded)
    (r : ℤ) (hrZero : 0 ≤ r) (hrPage : P.firstPage ≤ r) (s k : ℤ)
    {T : C}
    {x : P.element r hrPage s k T}
    {y : P.element r hrPage (s + r) (k - 1) T}
    {xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k)}
    {yl : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1))}
    (hxl : P.IsLift r hrPage s k xl x)
    (hyl : P.IsLift r hrPage (s + r) (k - 1) yl y)
    (hd : xl ≫ PageView.filDiff (FC := FC) s k =
      yl ≫ PageView.drop (FC := FC) r s k hrZero) :
    P.relation r hrPage s k x y := by
  rcases hP with rfl
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hrZero
  rcases hxl with ⟨xZ, hxZ, hx⟩
  rcases hyl with ⟨yZ, hyZ, hy⟩
  obtain ⟨xZ', yZ', hxZ', hyZ', hd'⟩ :=
    FC.pageDifferential_of_strict_lifts s k n xl yl hd
  have ex : xZ = xZ' := by
    apply (cancel_mono (FC.cycleSubobject s k (↑n)).arrow).mp
    exact hxZ.trans hxZ'.symm
  have ey : yZ = yZ' := by
    apply (cancel_mono (FC.cycleSubobject (s + ↑n) (k - 1) (↑n)).arrow).mp
    exact hyZ.trans hyZ'.symm
  subst xZ'
  subst yZ'
  change x ≫ ((FC.canonicalPageSpectralSequence).page (↑n : ℤ)
      (Int.natCast_nonneg n)).d (s, k) (s + ↑n, k - 1) = y
  change T ⟶ FC.pageObj s k (↑n) at x
  change T ⟶ FC.pageObj (s + ↑n) (k - 1) (↑n) at y
  simp only [PageView.canonical, Iso.refl_hom, Int.toNat_natCast] at hx hy
  have hx' : xZ ≫ FC.pageπ s k (↑n) = x := by
    change xZ ≫ FC.pageπ s k (↑n) = x ≫ 𝟙 (FC.pageObj s k (↑n)) at hx
    simpa only [Category.comp_id] using hx
  have hy' : yZ ≫ FC.pageπ (s + ↑n) (k - 1) (↑n) = y := by
    change yZ ≫ FC.pageπ (s + ↑n) (k - 1) (↑n) =
      y ≫ 𝟙 (FC.pageObj (s + ↑n) (k - 1) (↑n)) at hy
    simpa only [Category.comp_id] using hy
  rw [← hx', ← hy']
  change (xZ ≫ FC.pageπ s k (↑n)) ≫
    FC.pageDifferentialHom n (s, k) (s + ↑n, k - 1) = _
  have hrel : (pageShape n).Rel (s, k) (s + (n : ℤ), k - 1) := by
    change (s, k) + ((n : ℤ), -1) = (s + (n : ℤ), k - 1)
    simp [Int.sub_eq_add_neg]
  rw [FC.pageDifferentialHom_of_rel n (s, k) (s + ↑n, k - 1) hrel]
  convert hd' using 1 <;>
    simp only [Int.sub_eq_add_neg, eqToHom_refl, Category.comp_id,
      Category.assoc] <;> rfl

theorem liftOfDifferentialRelation
    (FC : FilteredComplex C) (P : PageView FC)
    (hP : P = PageView.canonical FC)
    (_bnd : FC.filtration.IsBounded)
    (r : ℤ) (hrZero : 0 ≤ r) (hrPage : P.firstPage ≤ r) (s k : ℤ)
    {T : C} [Projective T]
    {x : P.element r hrPage s k T}
    {y : P.element r hrPage (s + r) (k - 1) T}
    (hrel : P.relation r hrPage s k x y) :
    ∃ (xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k))
      (yl : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1))),
      P.IsLift r hrPage s k xl x ∧
      P.IsLift r hrPage (s + r) (k - 1) yl y ∧
      xl ≫ PageView.filDiff (FC := FC) s k =
        yl ≫ PageView.drop (FC := FC) r s k hrZero := by
  rcases hP with rfl
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hrZero
  change T ⟶ FC.pageObj s k (↑n) at x
  change T ⟶ FC.pageObj (s + ↑n) (k - 1) (↑n) at y
  let f := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
  let K := kernelSubobject f
  let p : Subobject.underlying.obj K ⟶
      Subobject.underlying.obj (FC.cycleSubobject s k (↑n)) :=
    factorThruImageSubobject (K.arrow ≫ FC.filtration.toAssociatedGraded s k)
  let q := Subobject.ofLE (FC.boundarySubobject s k (↑n))
    (FC.cycleSubobject s k (↑n)) (FC.B_le_Z_aux s k (↑n))
  haveI : Epi (FC.pageπ s k (↑n)) := by
    change Epi (cokernel.π q)
    have hq := Cofork.IsColimit.epi (cokernelIsCokernel q)
    exact hq
  haveI : HasEqualizers C := inferInstance
  haveI : Epi p := by
    change Epi (factorThruImageSubobject
      (K.arrow ≫ FC.filtration.toAssociatedGraded s k))
    infer_instance
  let xZ := Projective.factorThru x (FC.pageπ s k (↑n))
  let u := Projective.factorThru xZ p
  let xl := u ≫ K.arrow
  have hxπ : xZ ≫ FC.pageπ s k (↑n) = x :=
    Projective.factorThru_comp _ _
  have hu : u ≫ p = xZ := Projective.factorThru_comp _ _
  have hxl : (PageView.canonical FC).IsLift (↑n) hrPage s k xl x := by
    refine ⟨xZ, ?_, ?_⟩
    · change xZ ≫ (FC.cycleSubobject s k (↑n)).arrow =
        xl ≫ FC.filtration.toAssociatedGraded s k
      calc
        xZ ≫ (FC.cycleSubobject s k (↑n)).arrow =
            (u ≫ p) ≫ (FC.cycleSubobject s k (↑n)).arrow := by rw [hu]
        _ = u ≫ K.arrow ≫ FC.filtration.toAssociatedGraded s k := by
          change (u ≫ factorThruImageSubobject
            (K.arrow ≫ FC.filtration.toAssociatedGraded s k)) ≫
            (imageSubobject (K.arrow ≫ FC.filtration.toAssociatedGraded s k)).arrow = _
          rw [Category.assoc, imageSubobject_arrow_comp]
        _ = xl ≫ FC.filtration.toAssociatedGraded s k := by
          simp only [xl, Category.assoc]
    · change xZ ≫ FC.pageπ s k (↑n) =
        x ≫ 𝟙 (FC.pageObj s k (↑n))
      simpa only [Category.comp_id] using hxπ
  have hk : (K.arrow ≫ (FC.filtration.F s k).arrow ≫
      FC.complex.d k (k - 1)) ≫
      cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) = 0 := by
    simpa only [f, Category.assoc] using kernelSubobject_arrow_comp f
  let dLift := Abelian.monoLift (FC.filtration.F (s + ↑n) (k - 1)).arrow
    (K.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) hk
  let yl := u ≫ dLift
  have hd : xl ≫ PageView.filDiff (FC := FC) s k =
      yl ≫ PageView.drop (FC := FC) (↑n) s k (Int.natCast_nonneg n) := by
    apply (cancel_mono (FC.filtration.F s (k - 1)).arrow).mp
    calc
      (xl ≫ PageView.filDiff (FC := FC) s k) ≫
          (FC.filtration.F s (k - 1)).arrow =
        xl ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
          simpa only [PageView.filDiff, Category.assoc] using
            congrArg (fun z => xl ≫ z)
              (FC.differential_preserves s k).choose_spec
      _ = yl ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow := by
        simp only [xl, yl, dLift, Category.assoc, Abelian.monoLift_comp]
      _ = (yl ≫ PageView.drop (FC := FC) (↑n) s k
          (Int.natCast_nonneg n)) ≫ (FC.filtration.F s (k - 1)).arrow := by
        simp only [PageView.drop, Category.assoc, FC.filtration.inclusion_arrow]
  obtain ⟨zx, zy, hzx, hzy, _⟩ :=
    FC.pageDifferential_of_strict_lifts s k n xl yl hd
  let y₂ : (PageView.canonical FC).element (↑n) hrPage
      (s + ↑n) (k - 1) T := zy ≫ FC.pageπ (s + ↑n) (k - 1) (↑n)
  have hyl₂ : (PageView.canonical FC).IsLift (↑n) hrPage
      (s + ↑n) (k - 1) yl y₂ := by
    refine ⟨zy, hzy, ?_⟩
    change zy ≫ FC.pageπ (s + ↑n) (k - 1) (↑n) =
      y₂ ≫ 𝟙 (FC.pageObj (s + ↑n) (k - 1) (↑n))
    change zy ≫ FC.pageπ (s + ↑n) (k - 1) (↑n) =
      (zy ≫ FC.pageπ (s + ↑n) (k - 1) (↑n)) ≫ 𝟙 _
    rw [Category.comp_id]
  have hrel₂ : (PageView.canonical FC).relation (↑n) hrPage s k x y₂ :=
    differentialRelationOfLift FC (PageView.canonical FC) rfl _bnd
      (↑n) (Int.natCast_nonneg n) hrPage s k hxl hyl₂ hd
  have hy₂ : y₂ = y :=
    PageView.relation_target_unique (PageView.canonical FC) hrel₂ hrel
  refine ⟨xl, yl, hxl, ?_, hd⟩
  simpa only [hy₂] using hyl₂

/-- For canonical quotient pages a strict target lift represents the unique
page-differential target. The no-crossing premise is retained for the old API,
but is only needed for the distinct associated-graded representative theorem. -/
theorem liftRelOfNotCrossed
    (FC : FilteredComplex C) (P : PageView FC)
    (hP : P = PageView.canonical FC)
    (_bnd : FC.filtration.IsBounded)
    (r : ℤ) (hrZero : 0 ≤ r) (hrPage : P.firstPage ≤ r) (s k : ℤ)
    {T : C} [Projective T]
    {x : P.element r hrPage s k T}
    {y₁ : P.element r hrPage (s + r) (k - 1) T}
    (h₁ : P.relation r hrPage s k x y₁)
    (_hnc : ¬ P.crossed r hrPage s k x y₁ h₁)
    {xl : T ⟶ Subobject.underlying.obj (FC.filtration.F s k)}
    (hxl : P.IsLift r hrPage s k xl x)
    (yl : T ⟶ Subobject.underlying.obj (FC.filtration.F (s + r) (k - 1)))
    (hd : xl ≫ PageView.filDiff (FC := FC) s k =
      yl ≫ PageView.drop (FC := FC) r s k hrZero) :
    P.IsLift r hrPage (s + r) (k - 1) yl y₁ := by
  rcases hP with rfl
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hrZero
  obtain ⟨_, zy, _, hzy, _⟩ :=
    FC.pageDifferential_of_strict_lifts s k n xl yl hd
  let y₂ : (PageView.canonical FC).element (↑n) hrPage
      (s + ↑n) (k - 1) T := zy ≫ FC.pageπ (s + ↑n) (k - 1) (↑n)
  have hyl₂ : (PageView.canonical FC).IsLift (↑n) hrPage
      (s + ↑n) (k - 1) yl y₂ := by
    refine ⟨zy, hzy, ?_⟩
    change zy ≫ FC.pageπ (s + ↑n) (k - 1) (↑n) =
      (zy ≫ FC.pageπ (s + ↑n) (k - 1) (↑n)) ≫ 𝟙 _
    rw [Category.comp_id]
  have hrel₂ : (PageView.canonical FC).relation (↑n) hrPage s k x y₂ :=
    differentialRelationOfLift FC (PageView.canonical FC) rfl _bnd
      (↑n) (Int.natCast_nonneg n) hrPage s k hxl hyl₂ hd
  have hy₂ : y₂ = y₁ :=
    PageView.relation_target_unique (PageView.canonical FC) hrel₂ h₁
  simpa only [hy₂] using hyl₂

end KIP126.Core.SpectralSequence.FilteredComplex
