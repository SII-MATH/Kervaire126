import KIPBase.Synthetic.GeometricAdamsBoundaryComparison
import KIPBase.Synthetic.GeometricAdamsCapPage
import KIPBase.Synthetic.Rigidity
import KIPBase.Synthetic.ExtensionSS

/-!
# Geometric realization of the declared synthetic Adams spectral sequence

The project declares `SynAdamsSS` independently of an Adams tower.  The one
axiom in this file says that it is the spectral sequence of an actual filtered
synthetic spectrum: its page classes are represented in the graded pieces of
the filtration, and its `d_r` is the boundary of one relative disk crossing
`r` filtration layers.

Everything after these declarations is proved from them and from the cofiber
calculations in `GeometricAdamsBoundaryComparison`.
-/

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v'

variable (S : Type u) [StableHomotopy.StableHomotopyCategory.{u, v} S]
variable (Syn : Type u') [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]

/-- The cyclic group is projective in `AddCommGrpCat`.  Keeping the explicit
cyclic lift here avoids expensive generic module-instance search in the
representative arguments below. -/
private noncomputable instance intAddCommGrpProjective :
    Projective (AddCommGrpCat.of ℤ) where
  factors := by
    intro E A f e _
    have he : Function.Surjective e.hom :=
      (AddCommGrpCat.epi_iff_surjective e).mp inferInstance
    obtain ⟨z, hz⟩ := he (f.hom 1)
    let lift : AddCommGrpCat.of ℤ ⟶ E := AddCommGrpCat.ofHom
      { toFun := fun n => n • z
        map_zero' := zero_zsmul z
        map_add' := fun p q => add_zsmul z p q }
    refine ⟨lift, ?_⟩
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro n
    change ℤ at n
    change e.hom (n • z) = f.hom n
    rw [map_zsmul, hz]
    calc
      n • f.hom 1 = f.hom (n • (1 : ℤ)) := (map_zsmul _ _ _).symm
      _ = f.hom n := by simp

/-- A lambda-Bockstein differential occurs on two specified actual
homotopy representatives when they lift source and target classes of the
canonical boundary ESS and those classes satisfy its differential relation. -/
def LambdaBocksteinOccursOn
    (Y : Syn) (degree : ℤ × ℤ) (r s : ℤ)
    (a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1)
    (b : Smn (Syn := Syn) degree.1 degree.2 ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj Y)) : Prop :=
  let f := lambdaPowerBocksteinCSSMap Y 1
  let FC := unboundedUnderlyingComplex f degree
  let T := AddCommGrpCat.of ℤ
  ∃ (x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
        f degree (s, 1)).V)
    (y : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
        f degree (s + r, 0)).V)
    (xl : T ⟶ Subobject.underlying.obj
      ((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree))
    (yl : T ⟶ Subobject.underlying.obj
      ((lambdaPowerBocksteinTargetCSS Y 1).F.F (s + r) degree)),
    FC.IsLift s 1 xl
        (x ≫ (unboundedExtensionVComplexIso f degree s 1).hom) ∧
    FC.IsLift (s + r) 0 yl
        (y ≫ (unboundedExtensionVComplexIso f degree (s + r) 0).hom) ∧
    (synAdamsConvergence Syn (XModLambdaN Y 1)).abutmentEquiv degree
        (((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
          (xl.hom 1)) = a ∧
    (synAdamsConvergence Syn
      ((shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj Y))).abutmentEquiv degree
        (((lambdaPowerBocksteinTargetCSS Y 1).F.F (s + r) degree).arrow.hom
          (yl.hom 1)) = b ∧
    DifferentialRelation
      (ExtensionSpectralSequence.{1, 0, 0, 0} f degree) r (s, 1) x
      (Eq.mpr (congrArg (fun A : AddCommGrpCat.{0} => T ⟶ A)
        (show
          ((ExtensionSpectralSequence.{1, 0, 0, 0} f degree).ssData
            ((s, 1) +
              (ExtensionSpectralSequence.{1, 0, 0, 0} f degree).diffDeg r)).V =
            (unboundedExtensionSSData.{1, 0, 0, 0}
              f degree (s + r, 0)).V by
            rw [ExtensionSpectralSequence_diffDeg]
            norm_num)) y)

/-- A source page class of the canonical lambda-Bockstein ESS represents a
specified actual filtered homotopy class.  This separates the source class
from the choice of its differential target. -/
def LambdaBocksteinSourcePageRep
    (Y : Syn) (degree : ℤ × ℤ) (r s : ℤ)
    (a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1)
    (xPage : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1)) : Prop :=
  let f := lambdaPowerBocksteinCSSMap Y 1
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  let T := AddCommGrpCat.of ℤ
  ∃ (x : T ⟶ (E.ssData (s, 1)).V)
    (xl : T ⟶ Subobject.underlying.obj
      ((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree)),
    (unboundedUnderlyingComplex f degree).IsLift s 1 xl
      (x ≫ (unboundedExtensionVComplexIso f degree s 1).hom) ∧
    (synAdamsConvergence Syn (XModLambdaN Y 1)).abutmentEquiv degree
      (((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
        (xl.hom 1)) = a ∧
    ElementPageRel E r (s, 1) x xPage

/-- In the source degree of a two-term filtered complex there are no
incoming differentials, so every finite boundary subobject is zero. -/
private theorem lambdaBocksteinSource_complexBoundary_eq_bot
    {Y : Syn} (degree : ℤ × ℤ) (s : ℤ) (n : ℕ) :
    FilteredComplex.boundarySubobject
      (unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap Y 1) degree)
        s 1 (n : WithTop ℕ) = ⊥ := by
  let FC := unboundedUnderlyingComplex
    (lambdaPowerBocksteinCSSMap Y 1) degree
  have hd : FC.dToK 1 = 0 := by
    simp [FC, unboundedUnderlyingComplex, underlyingComplex,
      FilteredComplex.dToK, twoTermObj, twoTermDiff]
  let f := (FC.fil (s - (n : ℤ) + 1) (1 + 1)).arrow ≫ FC.dToK 1
  have hf : f = 0 := by
    dsimp only [f]
    rw [hd, comp_zero]
  have himg : imageSubobject f = ⊥ := by
    apply le_antisymm
    · apply imageSubobject_le f 0
      rw [zero_comp, hf]
    · exact bot_le
  simp only [FilteredComplex.boundarySubobject]
  change imageSubobject
    ((imageSubobject f ⊓ FC.fil s 1).ofLE (FC.fil s 1) _ ≫
      FC.filToAssocGraded s 1) = ⊥
  let I := imageSubobject f ⊓ FC.fil s 1
  have hI : I = ⊥ := by
    dsimp only [I]
    rw [himg, bot_inf_eq]
  let q := Subobject.ofLE I (FC.fil s 1) inf_le_right
  change imageSubobject (q ≫ FC.filToAssocGraded s 1) = ⊥
  have hbot : IsZero ((⊥ : Subobject (FC.A 1)) : AddCommGrpCat) :=
    IsZero.of_iso (isZero_zero AddCommGrpCat)
      (Subobject.botCoeIsoZero (C := AddCommGrpCat))
  have hIZero : IsZero (I : AddCommGrpCat) :=
    IsZero.of_iso hbot (Subobject.isoOfEq I ⊥ hI)
  have hq : q = 0 := hIZero.eq_of_src _ _
  rw [hq, zero_comp, imageSubobject_zero]

/-- The source boundary object in the actual unbounded extension data is a
zero object on every finite page. -/
private theorem lambdaBocksteinSource_boundary_isZero
    {Y : Syn} (degree : ℤ × ℤ) (s : ℤ) (n : ℕ) :
    IsZero (Subobject.underlying.obj
      (((canonicalLambdaPowerBocksteinESS Y 1 degree).ssData (s, 1)).B
        (n : WithTop ℕ))) := by
  let f := lambdaPowerBocksteinCSSMap Y 1
  have hB :
      ((unboundedComplexSSDataFamily.{1, 0, 0, 0} f degree (s, 1)).B
        (n : WithTop ℕ)) = ⊥ := by
    change (unboundedUnderlyingComplex f degree).boundarySubobject
      s 1 (n : WithTop ℕ) = ⊥
    exact lambdaBocksteinSource_complexBoundary_eq_bot
      (Syn := Syn) degree s n
  have hzero : IsZero (Subobject.underlying.obj
      ((unboundedComplexSSDataFamily.{1, 0, 0, 0} f degree (s, 1)).B
        (n : WithTop ℕ))) := by
    rw [hB]
    exact IsZero.of_iso (isZero_zero AddCommGrpCat)
      (Subobject.botCoeIsoZero (C := AddCommGrpCat))
  exact IsZero.of_iso hzero
    (unboundedExtensionBIso.{1, 0, 0, 0}
      f degree (s, 1) (n : WithTop ℕ))

/-- No boundary enters the source column of the λ-Bockstein sequence, so
every finite source boundary subobject agrees with the initial one. -/
theorem lambdaBocksteinSource_boundaries_eq_initial
    {Y : Syn} (degree : ℤ × ℤ) (s : ℤ) (n : ℕ) :
    ((canonicalLambdaPowerBocksteinESS Y 1 degree).ssData (s, 1)).B
        (n : WithTop ℕ) =
      ((canonicalLambdaPowerBocksteinESS Y 1 degree).ssData (s, 1)).B 0 := by
  let D := (canonicalLambdaPowerBocksteinESS Y 1 degree).ssData (s, 1)
  have hn : IsZero (Subobject.underlying.obj (D.B (n : WithTop ℕ))) :=
    lambdaBocksteinSource_boundary_isZero (Syn := Syn) degree s n
  have h0 : IsZero (Subobject.underlying.obj (D.B 0)) :=
    lambdaBocksteinSource_boundary_isZero (Syn := Syn) degree s 0
  apply le_antisymm
  · apply Subobject.le_of_comm (0 : Subobject.underlying.obj (D.B n) ⟶
      Subobject.underlying.obj (D.B 0))
    rw [zero_comp]
    exact hn.eq_of_src _ _
  · apply Subobject.le_of_comm (0 : Subobject.underlying.obj (D.B 0) ⟶
      Subobject.underlying.obj (D.B n))
    rw [zero_comp]
    exact h0.eq_of_src _ _

/-- An occurrence relation determines actual source and target classes on
the displayed lambda-Bockstein page, and the page differential sends the
source class to the target class. -/
theorem LambdaBocksteinOccursOn.exists_page_differential
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {b : Smn (Syn := Syn) degree.1 degree.2 ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj Y)}
    (h : LambdaBocksteinOccursOn (Syn := Syn) Y degree r s a b) :
    let f := lambdaPowerBocksteinCSSMap Y 1
    let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
    let T := AddCommGrpCat.of ℤ
    ∃ (x : T ⟶ (E.ssData (s, 1)).V)
      (y : T ⟶ (E.ssData ((s, 1) + E.diffDeg r)).V)
      (xPage : T ⟶ E.Page r (s, 1))
      (yPage : T ⟶ E.Page r ((s, 1) + E.diffDeg r)),
      xPage ≫ E.d r (s, 1) = yPage ∧
      ElementPageRel E r (s, 1) x xPage ∧
      ElementPageRel E r ((s, 1) + E.diffDeg r) y yPage := by
  dsimp only
  rcases h with ⟨x, y, xl, yl, hx, hy, ha, hb, hrel⟩
  let f := lambdaPowerBocksteinCSSMap Y 1
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  let T := AddCommGrpCat.of ℤ
  let y' : T ⟶ (E.ssData ((s, 1) + E.diffDeg r)).V :=
    Eq.mpr (congrArg (fun A : AddCommGrpCat.{0} => T ⟶ A)
      (show
        (E.ssData ((s, 1) + E.diffDeg r)).V =
          (unboundedExtensionSSData.{1, 0, 0, 0}
            f degree (s + r, 0)).V by
          change
            (unboundedExtensionSSData.{1, 0, 0, 0}
              f degree (s + r, 0)).V =
            (unboundedExtensionSSData.{1, 0, 0, 0}
              f degree (s + r, 0)).V
          rfl)) y
  change DifferentialRelation E r (s, 1) x y' at hrel
  obtain ⟨xPage, yPage, hd, hxPage, hyPage⟩ :=
    (dr_apply_iff_rel E r (s, 1) x y').mpr hrel
  exact ⟨x, y', xPage, yPage, hd, hxPage, hyPage⟩

/-- Forgetting the target of an actual Bockstein occurrence gives a source
representative on the corresponding page. -/
theorem LambdaBocksteinOccursOn.exists_sourcePageRep
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {b : Smn (Syn := Syn) degree.1 degree.2 ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj Y)}
    (h : LambdaBocksteinOccursOn (Syn := Syn) Y degree r s a b) :
    ∃ xPage : AddCommGrpCat.of ℤ ⟶
        (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1),
      LambdaBocksteinSourcePageRep (Syn := Syn)
        Y degree r s a xPage := by
  obtain ⟨x, y, xPage, yPage, hd, hxPage, hyPage⟩ :=
    h.exists_page_differential
  rcases h with ⟨x', y', xl, yl, hx, hy, ha, hb, hrel⟩
  let f := lambdaPowerBocksteinCSSMap Y 1
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  let y'' : AddCommGrpCat.of ℤ ⟶
      (E.ssData ((s, 1) + E.diffDeg r)).V :=
    Eq.mpr (congrArg
      (fun A : AddCommGrpCat.{0} => AddCommGrpCat.of ℤ ⟶ A)
      (show
        (E.ssData ((s, 1) + E.diffDeg r)).V =
          (unboundedExtensionSSData.{1, 0, 0, 0}
            f degree (s + r, 0)).V by
          change
            (unboundedExtensionSSData.{1, 0, 0, 0}
              f degree (s + r, 0)).V =
            (unboundedExtensionSSData.{1, 0, 0, 0}
              f degree (s + r, 0)).V
          rfl)) y'
  change DifferentialRelation E r (s, 1) x' y'' at hrel
  obtain ⟨xPage', yPage', hd', hxPage', hyPage'⟩ :=
    (dr_apply_iff_rel E r (s, 1) x' y'').mpr hrel
  exact ⟨xPage', x', xl, hx, ha, hxPage'⟩

/-- An occurrence can be represented on the page while retaining the proof
that its source page class represents the specified actual source. -/
theorem LambdaBocksteinOccursOn.exists_page_differential_sourceRep
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {b : Smn (Syn := Syn) degree.1 degree.2 ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj Y)}
    (h : LambdaBocksteinOccursOn (Syn := Syn) Y degree r s a b) :
    let E := canonicalLambdaPowerBocksteinESS Y 1 degree
    let T := AddCommGrpCat.of ℤ
    ∃ (y : T ⟶ (E.ssData ((s, 1) + E.diffDeg r)).V)
      (xPage : T ⟶ E.Page r (s, 1))
      (yPage : T ⟶ E.Page r ((s, 1) + E.diffDeg r)),
      xPage ≫ E.d r (s, 1) = yPage ∧
      LambdaBocksteinSourcePageRep (Syn := Syn)
        Y degree r s a xPage ∧
      ElementPageRel E r ((s, 1) + E.diffDeg r) y yPage := by
  dsimp only
  rcases h with ⟨x, y, xl, yl, hx, hy, ha, hb, hrel⟩
  let f := lambdaPowerBocksteinCSSMap Y 1
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  let T := AddCommGrpCat.of ℤ
  let y' : T ⟶ (E.ssData ((s, 1) + E.diffDeg r)).V :=
    Eq.mpr (congrArg (fun A : AddCommGrpCat.{0} => T ⟶ A)
      (show
        (E.ssData ((s, 1) + E.diffDeg r)).V =
          (unboundedExtensionSSData.{1, 0, 0, 0}
            f degree (s + r, 0)).V by
          change
            (unboundedExtensionSSData.{1, 0, 0, 0}
              f degree (s + r, 0)).V =
            (unboundedExtensionSSData.{1, 0, 0, 0}
              f degree (s + r, 0)).V
          rfl)) y
  change DifferentialRelation E r (s, 1) x y' at hrel
  obtain ⟨xPage, yPage, hd, hxPage, hyPage⟩ :=
    (dr_apply_iff_rel E r (s, 1) x y').mpr hrel
  exact ⟨y', xPage, yPage, hd, ⟨x, xl, hx, ha, hxPage⟩, hyPage⟩

/-- The page class represented by a fixed actual filtered homotopy class is
independent of every lift used to construct it. -/
theorem LambdaBocksteinSourcePageRep.unique
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {xPage₁ xPage₂ : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1)}
    (h₁ : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a xPage₁)
    (h₂ : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a xPage₂) :
    xPage₁ = xPage₂ := by
  let f := lambdaPowerBocksteinCSSMap Y 1
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  let A := synAdamsConvergence Syn (XModLambdaN Y 1)
  rcases h₁ with ⟨x₁, xl₁, hx₁, ha₁, hp₁⟩
  rcases h₂ with ⟨x₂, xl₂, hx₂, ha₂, hp₂⟩
  have hbaseOne :
      ((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
          (xl₁.hom 1) =
        ((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
          (xl₂.hom 1) := by
    apply (A.abutmentEquiv degree).injective
    exact ha₁.trans ha₂.symm
  have hxl : xl₁ = xl₂ := by
    apply (cancel_mono
      ((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow).mp
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change ℤ at z
    change
      ((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
          (xl₁.hom z) =
        ((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
          (xl₂.hom z)
    calc
      _ = z • ((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
          (xl₁.hom 1) := by rw [← map_zsmul, ← map_zsmul]; simp
      _ = z • ((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
          (xl₂.hom 1) := congrArg (fun q => z • q) hbaseOne
      _ = _ := by rw [← map_zsmul, ← map_zsmul]; simp
  have hx : x₁ = x₂ := by
    apply (cancel_mono
      (unboundedExtensionVComplexIso f degree s 1).hom).mp
    rw [← hx₁, ← hx₂, hxl]
  rcases hp₁ with ⟨xZ₁, hxZ₁, hxClass₁⟩
  rcases hp₂ with ⟨xZ₂, hxZ₂, hxClass₂⟩
  have hxZ : xZ₁ = xZ₂ := by
    apply (cancel_mono ((E.ssData (s, 1)).Z
      (↑(r - E.r₀).toNat : WithTop ℕ)).arrow).mp
    rw [hxZ₁, hxZ₂, hx]
  rw [← hxClass₁, ← hxClass₂, hxZ]

/-- Every generalized element of a lambda-Bockstein source page has an
actual filtered homotopy representative.  It is enough to lift the image of
the generator of `ℤ`: first through the page quotient, then through the
associated-graded quotient of the source filtration. -/
theorem LambdaBocksteinSourcePageRep.exists_of_page
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    (xPage : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1)) :
    ∃ a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1,
      LambdaBocksteinSourcePageRep (Syn := Syn)
        Y degree r s a xPage := by
  let f := lambdaPowerBocksteinCSSMap Y 1
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  let FC := unboundedUnderlyingComplex f degree
  let T := AddCommGrpCat.of ℤ
  let pageIndex : WithTop ℕ := ↑(r - E.r₀).toNat
  have hPageSurj : Function.Surjective
      ((E.ssData (s, 1)).pageπ pageIndex).hom :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨xOne, hxOne⟩ := hPageSurj (xPage.hom 1)
  let xZ : T ⟶ Subobject.underlying.obj
      ((E.ssData (s, 1)).Z pageIndex) := AddCommGrpCat.ofHom
    { toFun := fun z => z • xOne
      map_zero' := zero_zsmul xOne
      map_add' := fun p q => add_zsmul xOne p q }
  have hxZPage : xZ ≫ (E.ssData (s, 1)).pageπ pageIndex = xPage := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change ℤ at z
    change ((E.ssData (s, 1)).pageπ pageIndex).hom (z • xOne) = xPage.hom z
    rw [map_zsmul, hxOne]
    calc
      z • xPage.hom 1 = xPage.hom (z • (1 : ℤ)) := (map_zsmul _ _ _).symm
      _ = xPage.hom z := by simp
  let x : T ⟶ (E.ssData (s, 1)).V :=
    xZ ≫ ((E.ssData (s, 1)).Z pageIndex).arrow
  let xGraded := x ≫ (unboundedExtensionVComplexIso f degree s 1).hom
  letI : Epi (FC.filToAssocGraded s 1) := by
    dsimp only [FilteredComplex.filToAssocGraded]
    infer_instance
  have hGradedSurj : Function.Surjective (FC.filToAssocGraded s 1).hom :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨xlOne, hxlOne⟩ := hGradedSurj (xGraded.hom 1)
  let xl : T ⟶ Subobject.underlying.obj (FC.fil s 1) := AddCommGrpCat.ofHom
    { toFun := fun z => z • xlOne
      map_zero' := zero_zsmul xlOne
      map_add' := fun p q => add_zsmul xlOne p q }
  have hxl : xl ≫ FC.filToAssocGraded s 1 = xGraded := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change ℤ at z
    change (FC.filToAssocGraded s 1).hom (z • xlOne) = xGraded.hom z
    rw [map_zsmul, hxlOne]
    calc
      z • xGraded.hom 1 = xGraded.hom (z • (1 : ℤ)) := (map_zsmul _ _ _).symm
      _ = xGraded.hom z := by simp
  let A := synAdamsConvergence Syn (XModLambdaN Y 1)
  let a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1 :=
    A.abutmentEquiv degree
      (((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
        (xl.hom 1))
  refine ⟨a, x, xl, ?_, rfl, ?_⟩
  · dsimp only [FilteredComplex.IsLift]
    exact hxl
  · refine ⟨xZ, rfl, ?_⟩
    exact hxZPage

/-- A representative of a source class on the `r`-th lambda-Bockstein page
can be chosen so that its actual boundary already factors through filtration
`s + r`.  This is the source-cycle condition written in the unbounded
filtered complex.  No convergence or boundedness assumption enters here. -/
theorem LambdaBocksteinSourcePageRep.exists_filtered_boundary_lift
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {xPage : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1)}
    (hr : 0 ≤ r)
    (h : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a xPage) :
    ∃ (x : AddCommGrpCat.of ℤ ⟶
        (unboundedExtensionSSData.{1, 0, 0, 0} (lambdaPowerBocksteinCSSMap Y 1)
          degree (s, 1)).V)
      (xl : AddCommGrpCat.of ℤ ⟶ Subobject.underlying.obj
        ((unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap Y 1)
          degree).fil s 1))
      (yl : AddCommGrpCat.of ℤ ⟶ Subobject.underlying.obj
        ((unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap Y 1)
          degree).fil (s + r) (1 - 1))),
      xl ≫ (unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap Y 1)
        degree).filToAssocGraded s 1 =
        x ≫ (unboundedExtensionVComplexIso
          (lambdaPowerBocksteinCSSMap Y 1) degree s 1).hom ∧
      xl ≫ (unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap Y 1)
        degree).filDiff s 1 =
        yl ≫ Subobject.ofLE
          ((unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap Y 1)
            degree).fil (s + r) (1 - 1))
          ((unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap Y 1)
            degree).fil s (1 - 1))
          ((unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap Y 1)
            degree).fil_anti_of_le (1 - 1) (by omega)) := by
  classical
  rcases h with ⟨x, _xl, _hx, _ha, xZ, hxZ, _hxPage⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  let f := lambdaPowerBocksteinCSSMap Y 1
  let FC := unboundedUnderlyingComplex f degree
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  let xC := xZ ≫ (unboundedExtensionZIso.{1, 0, 0, 0} f degree (s, 1)
    (n : WithTop ℕ)).hom
  let g := (FC.fil s 1).arrow ≫ FC.d 1 ≫
    cokernel.π ((FC.fil (s + (n : ℤ)) (1 - 1)).arrow)
  let K := kernelSubobject g
  let p := factorThruImageSubobject (K.arrow ≫ FC.filToAssocGraded s 1)
  let xC' : AddCommGrpCat.of ℤ ⟶ Subobject.underlying.obj
      (imageSubobject (K.arrow ≫ FC.filToAssocGraded s 1)) := by
    change AddCommGrpCat.of ℤ ⟶ Subobject.underlying.obj
      ((unboundedComplexSSDataFamily.{1, 0, 0, 0} f degree (s, 1)).Z
        (n : WithTop ℕ))
    exact xC
  let u := Projective.factorThru xC' p
  have hxC' : xC' ≫ (imageSubobject
      (K.arrow ≫ FC.filToAssocGraded s 1)).arrow =
      x ≫ (unboundedExtensionVComplexIso f degree s 1).hom := by
    have hcompat := congrArg (fun q => xZ ≫ q)
      (unboundedExtensionZIso_hom_arrow.{1, 0, 0, 0} f degree s 1 (n : WithTop ℕ))
    change xZ ≫ (unboundedExtensionZIso.{1, 0, 0, 0} f degree (s, 1)
      (n : WithTop ℕ)).hom ≫
        (FC.cycleSubobject s 1 (n : WithTop ℕ)).arrow = _ at hcompat
    have hcompat' := (Category.assoc xZ
      (unboundedExtensionZIso.{1, 0, 0, 0} f degree (s, 1) (n : WithTop ℕ)).hom
      (FC.cycleSubobject s 1 (n : WithTop ℕ)).arrow).trans hcompat
    have hcompat'' := hcompat'.trans (Category.assoc xZ
      ((E.ssData (s, 1)).Z (n : WithTop ℕ)).arrow
      (unboundedExtensionVComplexIso f degree s 1).hom).symm
    have hleft : xC' ≫ (imageSubobject
        (K.arrow ≫ FC.filToAssocGraded s 1)).arrow =
        (xZ ≫ ((E.ssData (s, 1)).Z (n : WithTop ℕ)).arrow) ≫
          (unboundedExtensionVComplexIso f degree s 1).hom := by
      dsimp only [xC', xC]
      exact hcompat''
    exact hleft.trans (congrArg (fun q => q ≫
      (unboundedExtensionVComplexIso f degree s 1).hom) hxZ)
  have hgK : (K.arrow ≫ (FC.fil s 1).arrow ≫ FC.d 1) ≫
      cokernel.π ((FC.fil (s + (n : ℤ)) (1 - 1)).arrow) = 0 := by
    simpa only [g, Category.assoc] using kernelSubobject_arrow_comp g
  let dLift := Abelian.monoLift (FC.fil (s + (n : ℤ)) (1 - 1)).arrow
    (K.arrow ≫ (FC.fil s 1).arrow ≫ FC.d 1) hgK
  refine ⟨x, u ≫ K.arrow, u ≫ dLift, ?_, ?_⟩
  · calc
      (u ≫ K.arrow) ≫ FC.filToAssocGraded s 1 =
          u ≫ (K.arrow ≫ FC.filToAssocGraded s 1) := Category.assoc _ _ _
      _ = (u ≫ p) ≫ (imageSubobject
          (K.arrow ≫ FC.filToAssocGraded s 1)).arrow := by
            rw [Category.assoc, imageSubobject_arrow_comp]
      _ = xC' ≫ (imageSubobject
          (K.arrow ≫ FC.filToAssocGraded s 1)).arrow := by
            rw [Projective.factorThru_comp]
      _ = x ≫ (unboundedExtensionVComplexIso f degree s 1).hom := hxC'
  · apply (cancel_mono (FC.fil s (1 - 1)).arrow).mp
    change ((u ≫ K.arrow) ≫ FC.filDiff s 1) ≫
        (FC.fil s (1 - 1)).arrow =
      ((u ≫ dLift) ≫ Subobject.ofLE
        (FC.fil (s + (n : ℤ)) (1 - 1)) (FC.fil s (1 - 1)) _) ≫
          (FC.fil s (1 - 1)).arrow
    simp only [Category.assoc, FC.filDiff_comp_arrow,
      Subobject.ofLE_arrow, dLift, Abelian.monoLift_comp]

/-- The zero actual class is represented by the zero page class. -/
theorem LambdaBocksteinSourcePageRep.zero
    (Y : Syn) (degree : ℤ × ℤ) (r s : ℤ) :
    LambdaBocksteinSourcePageRep (Syn := Syn) Y degree r s
      0 (0 : AddCommGrpCat.of ℤ ⟶
        (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1)) := by
  let f := lambdaPowerBocksteinCSSMap Y 1
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · dsimp only [FilteredComplex.IsLift]
    simp
  · simp
  · exact ⟨0, by simp, by simp⟩

/-- Addition of actual filtered classes is represented by addition on the
Bockstein page. -/
theorem LambdaBocksteinSourcePageRep.add
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a₁ a₂ : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {xPage₁ xPage₂ : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1)}
    (h₁ : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a₁ xPage₁)
    (h₂ : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a₂ xPage₂) :
    LambdaBocksteinSourcePageRep (Syn := Syn) Y degree r s
      (a₁ + a₂) (xPage₁ + xPage₂) := by
  let f := lambdaPowerBocksteinCSSMap Y 1
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  rcases h₁ with ⟨x₁, xl₁, hx₁, ha₁, ⟨xZ₁, hxZ₁, hp₁⟩⟩
  rcases h₂ with ⟨x₂, xl₂, hx₂, ha₂, ⟨xZ₂, hxZ₂, hp₂⟩⟩
  refine ⟨x₁ + x₂, xl₁ + xl₂, ?_, ?_, xZ₁ + xZ₂, ?_, ?_⟩
  · dsimp only [FilteredComplex.IsLift] at hx₁ hx₂ ⊢
    simpa only [Preadditive.add_comp] using congrArg₂ (fun p q => p + q) hx₁ hx₂
  · change (synAdamsConvergence Syn (XModLambdaN Y 1)).abutmentEquiv degree
      (((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
        (xl₁.hom 1 + xl₂.hom 1)) = a₁ + a₂
    rw [map_add, map_add, ha₁, ha₂]
  · simpa only [Preadditive.add_comp] using congrArg₂ (fun p q => p + q) hxZ₁ hxZ₂
  · simpa only [Preadditive.add_comp] using congrArg₂ (fun p q => p + q) hp₁ hp₂

/-- Negation of an actual filtered representative represents the negated
source-page class. -/
theorem LambdaBocksteinSourcePageRep.neg
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {xPage : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1)}
    (h : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a xPage) :
    LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s (-a) (-xPage) := by
  rcases h with ⟨x, xl, hx, ha, xZ, hxZ, hp⟩
  refine ⟨-x, -xl, ?_, ?_, -xZ, ?_, ?_⟩
  · dsimp only [FilteredComplex.IsLift] at hx ⊢
    simpa only [Preadditive.neg_comp] using congrArg Neg.neg hx
  · change (synAdamsConvergence Syn (XModLambdaN Y 1)).abutmentEquiv degree
      (((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
        (-xl.hom 1)) = -a
    rw [map_neg, map_neg, ha]
  · simpa only [Preadditive.neg_comp] using congrArg Neg.neg hxZ
  · simpa only [Preadditive.neg_comp] using congrArg Neg.neg hp

/-- Subtraction of actual filtered representatives agrees with subtraction
on the source page. -/
theorem LambdaBocksteinSourcePageRep.sub
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a₁ a₂ : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {xPage₁ xPage₂ : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1)}
    (h₁ : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a₁ xPage₁)
    (h₂ : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a₂ xPage₂) :
    LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s (a₁ - a₂) (xPage₁ - xPage₂) := by
  simpa only [sub_eq_add_neg] using
    LambdaBocksteinSourcePageRep.add (Syn := Syn) h₁
      (LambdaBocksteinSourcePageRep.neg (Syn := Syn) h₂)

/-- An actual class in the next filtration layer represents zero on the
current Bockstein page. -/
theorem LambdaBocksteinSourcePageRep.eq_zero_of_mem_next
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {xPage : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1)}
    (h : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a xPage)
    (haNext : a ∈ synAdamsFiltration Syn (XModLambdaN Y 1)
      degree.1 degree.2 (s + 1)) :
    xPage = 0 := by
  rcases h with ⟨x, xl, hx, ha, hxPage⟩
  let f := lambdaPowerBocksteinCSSMap Y 1
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  let A := synAdamsConvergence Syn (XModLambdaN Y 1)
  have haCurrent : a ∈ synAdamsFiltration Syn (XModLambdaN Y 1)
      degree.1 degree.2 s :=
    synAdamsFiltration_mono Syn (XModLambdaN Y 1)
      degree.1 degree.2 s haNext
  let aFiltered : synAdamsFiltration Syn (XModLambdaN Y 1)
      degree.1 degree.2 s := ⟨a, haCurrent⟩
  have hfil : A.filtrationEquiv s degree (xl.hom 1) = aFiltered := by
    apply Subtype.ext
    exact (A.filtrationEquiv_comm s degree (xl.hom 1)).symm.trans ha
  have hxlOne : xl.hom 1 =
      (A.filtrationEquiv s degree).symm aFiltered := by
    apply (A.filtrationEquiv s degree).injective
    rw [hfil, AddEquiv.apply_symm_apply]
  have hproj : A.homotopyGradedProjection s degree aFiltered = 0 :=
    (A.homotopyGradedProjection_eq_zero_iff s degree aFiltered).mpr haNext
  let FC := unboundedUnderlyingComplex f degree
  have hxlZero : xl ≫ FC.filToAssocGraded s 1 = 0 := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change (FC.filToAssocGraded s 1).hom (xl.hom z) = 0
    have hzx : xl.hom z = z • xl.hom 1 := by
      change ℤ at z
      calc
        xl.hom z = xl.hom (z • (1 : ℤ)) := by simp
        _ = z • xl.hom 1 := map_zsmul _ _ _
    rw [hzx, map_zsmul, hxlOne]
    change z • A.homotopyGradedProjection s degree aFiltered = 0
    rw [hproj, smul_zero]
  have hxZero : x = 0 := by
    apply (cancel_mono (unboundedExtensionVComplexIso f degree s 1).hom).mp
    rw [← hx, hxlZero, zero_comp]
  rcases hxPage with ⟨xZ, hxZ, hxClass⟩
  have hxZZero : xZ = 0 := by
    apply (cancel_mono ((E.ssData (s, 1)).Z
      (↑(r - E.r₀).toNat : WithTop ℕ)).arrow).mp
    rw [hxZ, hxZero, zero_comp]
  rw [← hxClass, hxZZero, zero_comp]

/-- Two actual representatives that differ by the next filtration layer
determine the same source-page class. -/
theorem LambdaBocksteinSourcePageRep.eq_of_sub_mem_next
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a₁ a₂ : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {xPage₁ xPage₂ : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1)}
    (h₁ : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a₁ xPage₁)
    (h₂ : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a₂ xPage₂)
    (hnext : a₁ - a₂ ∈
      synAdamsFiltration Syn (XModLambdaN Y 1)
        degree.1 degree.2 (s + 1)) :
    xPage₁ = xPage₂ := by
  have hzero := LambdaBocksteinSourcePageRep.eq_zero_of_mem_next
    (Syn := Syn) (LambdaBocksteinSourcePageRep.sub (Syn := Syn) h₁ h₂) hnext
  exact sub_eq_zero.mp hzero

/-- Since the source column has no incoming boundaries, a represented source
page class is zero only if its actual homotopy class lies in the next
filtration layer. -/
theorem LambdaBocksteinSourcePageRep.mem_next_of_eq_zero
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {xPage : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS Y 1 degree).Page r (s, 1)}
    (h : LambdaBocksteinSourcePageRep (Syn := Syn)
      Y degree r s a xPage)
    (hzero : xPage = 0) :
    a ∈ synAdamsFiltration Syn (XModLambdaN Y 1)
      degree.1 degree.2 (s + 1) := by
  rcases h with ⟨x, xl, hx, ha, ⟨xZ, hxZ, hxClass⟩⟩
  let f := lambdaPowerBocksteinCSSMap Y 1
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  let D := E.ssData (s, 1)
  let pageIndex : WithTop ℕ := ↑(r - E.r₀).toNat
  let i := Subobject.ofLE (D.B pageIndex) (D.Z pageIndex)
    (D.B_le_Z pageIndex)
  have hxPageZero : xZ ≫ cokernel.π i = 0 := by
    change xZ ≫ D.pageπ pageIndex = 0
    rw [hxClass, hzero]
  let xB := Abelian.monoLift i xZ hxPageZero
  have hxZero : x = 0 := by
    calc
      x = xZ ≫ (D.Z pageIndex).arrow := hxZ.symm
      _ = (xB ≫ i) ≫ (D.Z pageIndex).arrow := by
        rw [Abelian.monoLift_comp]
      _ = xB ≫ (D.B pageIndex).arrow := by
        rw [Category.assoc, Subobject.ofLE_arrow]
      _ = 0 := by
        have hB : IsZero (Subobject.underlying.obj (D.B pageIndex)) := by
          dsimp only [pageIndex, D, E]
          exact lambdaBocksteinSource_boundary_isZero
            (Syn := Syn) degree s (r - 0).toNat
        have hxB : xB = 0 := hB.eq_of_tgt xB 0
        rw [hxB, zero_comp]
  let FC := unboundedUnderlyingComplex f degree
  have hxlZero : xl ≫ FC.filToAssocGraded s 1 = 0 := by
    rw [hxZero, zero_comp] at hx
    exact hx
  let A := synAdamsConvergence Syn (XModLambdaN Y 1)
  let aFiltered := A.filtrationEquiv s degree (xl.hom 1)
  have hproj : A.homotopyGradedProjection s degree aFiltered = 0 := by
    have hpoint := congrArg (fun q => q.hom 1) hxlZero
    change (FC.filToAssocGraded s 1).hom (xl.hom 1) = 0 at hpoint
    change (A.filtration.toAssociatedGraded s degree).hom
      (xl.hom 1) = 0 at hpoint
    change (A.filtration.toAssociatedGraded s degree).hom
      ((A.filtrationEquiv s degree).symm aFiltered) = 0
    rw [show (A.filtrationEquiv s degree).symm aFiltered = xl.hom 1 from
      (A.filtrationEquiv s degree).symm_apply_apply (xl.hom 1)]
    exact hpoint
  have hnext :=
    (A.homotopyGradedProjection_eq_zero_iff s degree aFiltered).mp hproj
  have haval : aFiltered.val = a :=
    (A.filtrationEquiv_comm s degree (xl.hom 1)).symm.trans ha
  simpa only [haval] using hnext

/-- Restriction from a finite lambda quotient to the first quotient sends
the associated-graded class of an actual filtered representative to the
associated-graded class of its restriction. -/
theorem lambdaPowerToOne_homotopyGradedProjection
    (X : S) (n : ℕ) (degree : ℤ × ℤ) (s : ℤ)
    (q : synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) (n + 1))
      degree.1 degree.2 s) :
    let Aₙ := synAdamsConvergence Syn
      (XModLambdaN ((nu S Syn).obj X) (n + 1))
    let A₁ := synAdamsConvergence Syn (XModLambdaN ((nu S Syn).obj X) 1)
    let g := (synAdamsFunctoriality Syn).convergenceMap
      (XModLambdaN.toOne ((nu S Syn).obj X) n)
    let a := q.val ≫ XModLambdaN.toOne ((nu S Syn).obj X) n
    let ha : a ∈ synAdamsFiltration Syn
        (XModLambdaN ((nu S Syn).obj X) 1)
        degree.1 degree.2 s :=
      lambdaPowerBockstein_toOne_preserves_filtration
        ((nu S Syn).obj X) n degree.1 degree.2 s q.val q.property
    (Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
      s degree).hom (Aₙ.homotopyGradedProjection s degree q) =
        A₁.homotopyGradedProjection s degree ⟨a, ha⟩ := by
  dsimp only
  let Aₙ := synAdamsConvergence Syn
    (XModLambdaN ((nu S Syn).obj X) (n + 1))
  let A₁ := synAdamsConvergence Syn (XModLambdaN ((nu S Syn).obj X) 1)
  let g := (synAdamsFunctoriality Syn).convergenceMap
    (XModLambdaN.toOne ((nu S Syn).obj X) n)
  let qLift := (Aₙ.filtrationEquiv s degree).symm q
  let mappedLift : (A₁.filtration.F s degree : AddCommGrpCat) :=
    (g.filtration_compat s degree).choose.hom qLift
  let a := q.val ≫ XModLambdaN.toOne ((nu S Syn).obj X) n
  let ha : a ∈ synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) 1)
      degree.1 degree.2 s :=
    lambdaPowerBockstein_toOne_preserves_filtration
      ((nu S Syn).obj X) n degree.1 degree.2 s q.val q.property
  let aFiltered : synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) 1)
      degree.1 degree.2 s := ⟨a, ha⟩
  have hmapped : A₁.filtrationEquiv s degree mappedLift = aFiltered := by
    apply Subtype.ext
    calc
      (A₁.filtrationEquiv s degree mappedLift).val =
          A₁.abutmentEquiv degree
            (((A₁.filtration.F s degree).arrow).hom mappedLift) :=
        (A₁.filtrationEquiv_comm s degree mappedLift).symm
      _ = A₁.abutmentEquiv degree
          (g.aMap degree |>.hom
            (((Aₙ.filtration.F s degree).arrow).hom qLift)) := by
        apply congrArg (A₁.abutmentEquiv degree)
        exact ConcreteCategory.congr_hom
          (g.filtration_compat s degree).choose_spec qLift
      _ = Aₙ.abutmentEquiv degree
            (((Aₙ.filtration.F s degree).arrow).hom qLift) ≫
          XModLambdaN.toOne ((nu S Syn).obj X) n := by
        exact (synAdamsFunctoriality Syn).abutment_naturality
          (XModLambdaN.toOne ((nu S Syn).obj X) n) degree _
      _ = q.val ≫ XModLambdaN.toOne ((nu S Syn).obj X) n := by
        rw [Aₙ.filtrationEquiv_comm]
        rw [show Aₙ.filtrationEquiv s degree qLift = q from
          (Aₙ.filtrationEquiv s degree).apply_symm_apply q]
      _ = aFiltered.val := rfl
  change (Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
      s degree).hom
      ((Aₙ.filtration.toAssociatedGraded s degree).hom qLift) =
    (A₁.filtration.toAssociatedGraded s degree).hom
      ((A₁.filtrationEquiv s degree).symm aFiltered)
  rw [show (A₁.filtrationEquiv s degree).symm aFiltered = mappedLift from
    (A₁.filtrationEquiv s degree).injective
      ((A₁.filtrationEquiv s degree).apply_symm_apply aFiltered |>.trans
        hmapped.symm)]
  have hgraded : Aₙ.filtration.toAssociatedGraded s degree ≫
        Filtration.inducedAssocGradedMap g.aMap g.filtration_compat s degree =
      (g.filtration_compat s degree).choose ≫
        A₁.filtration.toAssociatedGraded s degree := by
    dsimp only [Filtration.inducedAssocGradedMap,
      Filtration.toAssociatedGraded]
    rw [cokernel.π_desc]
  exact ConcreteCategory.congr_hom hgraded qLift

/-- Restriction on finite-quotient limiting pages is the canonical inclusion
of Adams page `n+2` into E2.  This local proof uses only Adams page
naturality, so the comparison does not depend on the separate boundary-ESS
naturality module. -/
private theorem nuModLambdaSuccGeneratorEInftyIsoPage_toOne_local
    (X : S) (n : ℕ) (s t : ℤ) :
    (synAdamsSS_functorial
        (XModLambdaN.toOne ((nu S Syn).obj X) n)).eInftyMap (s, t, t) ≫
        (nuModLambdaSuccGeneratorEInftyIsoPage S Syn X 0 s t).hom =
      (nuModLambdaSuccGeneratorEInftyIsoPage S Syn X n s t).hom ≫
        synAdams_displayedPageToE2OfBoundariesEq
          ((nu S Syn).obj X) n (s, t, t)
          (synAdams_nu_diagonal_boundaries S Syn X s t n) := by
  let A := (nu S Syn).obj X
  let QN := XModLambdaN A (n + 1)
  let Q1 := XModLambdaN A 1
  have hdN := synAdams_mod_lambda_degenerates S Syn X (n + 1) (by omega)
  have hpN : max 2 ((((n + 1 : ℕ) : ℤ)) + 1) =
      ((n + 2 : ℕ) : ℤ) := by omega
  rw [hpN] at hdN
  have hd10 := synAdams_mod_lambda_degenerates S Syn X 1 (by omega)
  have hp0 : max 2 ((((1 : ℕ) : ℤ)) + 1) = 2 := by omega
  rw [hp0] at hd10
  have hd1N : (SynAdamsSS Syn Q1).DegeneratesAt
      ((n + 2 : ℕ) : ℤ) := by
    intro r hr k
    exact hd10 r (by omega) k
  let hBQ1 :=
    (synAdams_limit_boundaries_natAddTwo Q1 n hd1N (s, t, t)).symm.trans
      (synAdams_limit_boundaries_natAddTwo Q1 0 hd10 (s, t, t))
  have hnat := synAdams_eInftyIso_page_natAddTwo_naturality
    (XModLambdaN.toOne A n) n hdN hd1N (s, t, t)
  have hfactor := synAdams_eInftyIso_page_natAddTwo_factor_toE2
    Q1 n hd10 hd1N (s, t, t)
  have hincl := synAdams_displayedPageToE2OfBoundariesEq_naturality
    (nuModLambdaIncl S Syn X 1) n (s, t, t)
      (synAdams_nu_diagonal_boundaries S Syn X s t n) hBQ1
  let qN := nuModLambdaAdamsPageMap S Syn X (n + 1)
    ((n + 2 : ℕ) : ℤ) (s, t, t)
  let q1N := nuModLambdaAdamsPageMap S Syn X 1
    ((n + 2 : ℕ) : ℤ) (s, t, t)
  let q10 := nuModLambdaAdamsPageMap S Syn X 1 2 (s, t, t)
  let fN := synAdamsPageMap (XModLambdaN.toOne A n)
    ((n + 2 : ℕ) : ℤ) (s, t, t)
  have hq : qN ≫ fN = q1N := by
    dsimp only [qN, fN, q1N, nuModLambdaAdamsPageMap, nuModLambdaIncl]
    rw [← synAdamsPageMap_comp]
    exact congrArg
      (fun g => synAdamsPageMap g ((n + 2 : ℕ) : ℤ) (s, t, t))
      (XModLambdaN.incl_toOne A n)
  letI : IsIso qN := nuModLambdaAdamsPageMapIsIso_of_safe_range
    S Syn X (n + 1) (by omega) ((n + 2 : ℕ) : ℤ)
      (by omega) s t t (by omega) (by omega)
  letI : IsIso q10 := nuModLambdaAdamsE2PageMapIsIso
    S Syn X 1 (by omega) s t t (by omega)
  simp only [nuModLambdaSuccGeneratorEInftyIsoPage, Iso.trans_hom]
  rw [hfactor, ← Category.assoc, ← Category.assoc, hnat]
  simp only [Category.assoc]
  apply (cancel_epi
    (synAdams_eInftyIso_page_natAddTwo QN n hdN (s, t, t)).hom).mpr
  apply (cancel_epi qN).mp
  change qN ≫ (fN ≫
      synAdams_displayedPageToE2OfBoundariesEq Q1 n (s, t, t) hBQ1 ≫
        inv q10) =
    qN ≫ (inv qN ≫
      synAdams_displayedPageToE2OfBoundariesEq A n (s, t, t)
        (synAdams_nu_diagonal_boundaries S Syn X s t n))
  rw [← Category.assoc, hq]
  dsimp only [q1N] at hincl ⊢
  unfold nuModLambdaAdamsPageMap
  dsimp only [Q1, A] at hincl ⊢
  rw [← Category.assoc, hincl]
  have hq10eq : synAdamsPageMap (nuModLambdaIncl S Syn X 1)
      2 (s, t, t) = q10 := rfl
  rw [hq10eq]
  simp

/-- On the diagonal generator, restriction from `nu X/lambda^(n+1)` to
`nu X/lambda` is injective on limiting Adams classes: under the canonical
identifications it is the inclusion of Adams page `n+2` into E2. -/
theorem nuModLambdaSuccGenerator_toOne_eInftyMap_injective
    (X : S) (n : ℕ) (s : ℕ) (t : ℤ) :
    Function.Injective
      ((synAdamsSS_functorial
        (XModLambdaN.toOne ((nu S Syn).obj X) n)).eInftyMap
          ((s : ℤ), t, t)).hom := by
  let eN := nuModLambdaSuccGeneratorEInftyIsoPage S Syn X n (s : ℤ) t
  let e1 := nuModLambdaSuccGeneratorEInftyIsoPage S Syn X 0 (s : ℤ) t
  let inc := synAdams_nu_diagonal_displayed_toE2 S Syn X (s : ℤ) t n
  have hnat := nuModLambdaSuccGeneratorEInftyIsoPage_toOne_local
    S Syn X n (s : ℤ) t
  rw [← synAdams_nu_diagonal_displayed_toE2_eq S Syn X (s : ℤ) t n] at hnat
  intro x y hxy
  have hcomp :
      ((synAdamsSS_functorial
          (XModLambdaN.toOne ((nu S Syn).obj X) n)).eInftyMap
            ((s : ℤ), t, t) ≫ e1.hom).hom x =
        ((synAdamsSS_functorial
          (XModLambdaN.toOne ((nu S Syn).obj X) n)).eInftyMap
            ((s : ℤ), t, t) ≫ e1.hom).hom y := by
    exact congrArg e1.hom.hom hxy
  rw [hnat] at hcomp
  have hinc : eN.hom.hom x = eN.hom.hom y :=
    (synAdams_nu_diagonal_displayed_toE2_injective
      S Syn X (s : ℤ) t n) hcomp
  exact (AddCommGrpCat.mono_iff_injective eN.hom).mp inferInstance hinc

private theorem inverse_convergence_square_local
    {C : Type*} [Category C] [Abelian C]
    {A B : ℤ × ℤ → C} {F : Filtration A} {G : Filtration B}
    (aMap : ∀ d, A d ⟶ B d)
    (compat : ∀ s d, ∃ a,
      a ≫ (G.F s d).arrow = (F.F s d).arrow ≫ aMap d)
    {U V : C} {p q z : ℤ × (ℤ × ℤ)}
    (hpq : p = q) (hpz : p = z) (hqz : q = z)
    (e : U ≅ F.associatedGraded p.1 p.2)
    (e' : V ≅ G.associatedGraded q.1 q.2) (a : U ⟶ V)
    (h : a ≫ e'.hom ≫ G.transportGraded hpq.symm =
      e.hom ≫ Filtration.inducedAssocGradedMap aMap compat p.1 p.2) :
    Filtration.inducedAssocGradedMap aMap compat z.1 z.2 ≫
        G.transportGraded hqz.symm ≫ e'.inv =
      F.transportGraded hpz.symm ≫ e.inv ≫ a := by
  subst q
  subst z
  simp only [Filtration.transportGraded_self, Category.comp_id,
    Category.id_comp] at h ⊢
  apply (cancel_mono e'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

/-- The associated-graded map induced by restriction to `nu X/lambda` is
injective in the diagonal generator degree. -/
theorem lambdaPowerToOne_generator_inducedGradedMap_injective
    (X : S) (n s : ℕ) (t : ℤ) :
    let degree : ℤ × ℤ := (t - (s : ℤ), t)
    let g := (synAdamsFunctoriality Syn).convergenceMap
      (XModLambdaN.toOne ((nu S Syn).obj X) n)
    Function.Injective
      (Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
        (s : ℤ) degree).hom := by
  dsimp only
  let degree : ℤ × ℤ := (t - (s : ℤ), t)
  let Aₙ := synAdamsConvergence Syn
    (XModLambdaN ((nu S Syn).obj X) (n + 1))
  let A₁ := synAdamsConvergence Syn (XModLambdaN ((nu S Syn).obj X) 1)
  let g := (synAdamsFunctoriality Syn).convergenceMap
    (XModLambdaN.toOne ((nu S Syn).obj X) n)
  let k : ℤ × ℤ × ℤ := ((s : ℤ), t, t)
  have hpz : Aₙ.convergence.reindex k = ((s : ℤ), degree) := by
    rw [Aₙ.reindex_eq]
  have hqz : A₁.convergence.reindex k = ((s : ℤ), degree) := by
    rw [A₁.reindex_eq]
  have hsquare := inverse_convergence_square_local
    g.aMap g.filtration_compat
    (congrFun g.reindex_eq k) hpz hqz
    (Aₙ.convergence.iso k) (A₁.convergence.iso k) (g.eMap k)
    (g.iso_compat k)
  let preN := Aₙ.filtration.transportGraded hpz.symm ≫
    (Aₙ.convergence.iso k).inv
  let post1 := A₁.filtration.transportGraded hqz.symm ≫
    (A₁.convergence.iso k).inv
  have hsquare' :
      Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
          (s : ℤ) degree ≫ post1 = preN ≫ g.eMap k := by
    exact hsquare
  intro x y hxy
  have hpost :
      (preN ≫ g.eMap k).hom x = (preN ≫ g.eMap k).hom y := by
    rw [← hsquare']
    exact congrArg post1.hom hxy
  change (g.eMap k).hom (preN.hom x) =
    (g.eMap k).hom (preN.hom y) at hpost
  have heMap : g.eMap k =
      (synAdamsSS_functorial
        (XModLambdaN.toOne ((nu S Syn).obj X) n)).eInftyMap k :=
    congrFun ((synAdamsFunctoriality Syn).eMap_eq
      (XModLambdaN.toOne ((nu S Syn).obj X) n)) k
  rw [heMap] at hpost
  have hpre : preN.hom x = preN.hom y :=
    (nuModLambdaSuccGenerator_toOne_eInftyMap_injective
      S Syn X n s t) hpost
  haveI : IsIso (Aₙ.filtration.transportGraded hpz.symm) := by
    dsimp only [Filtration.transportGraded]
    infer_instance
  haveI : IsIso preN := by
    dsimp only [preN]
    infer_instance
  exact (AddCommGrpCat.mono_iff_injective preN).mp (by infer_instance) hpre

/-- In the generator bidegree, restriction to the first lambda quotient
reflects the next Adams-filtration layer. -/
theorem lambdaPowerToOne_reflects_generator_next_filtration
    (X : S) (n s : ℕ) (t : ℤ)
    (q : synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) (n + 1))
      (t - (s : ℤ)) t (s : ℤ))
    (haNext : q.val ≫ XModLambdaN.toOne ((nu S Syn).obj X) n ∈
      synAdamsFiltration Syn (XModLambdaN ((nu S Syn).obj X) 1)
        (t - (s : ℤ)) t ((s : ℤ) + 1)) :
    q.val ∈ synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) (n + 1))
      (t - (s : ℤ)) t ((s : ℤ) + 1) := by
  let degree : ℤ × ℤ := (t - (s : ℤ), t)
  let Aₙ := synAdamsConvergence Syn
    (XModLambdaN ((nu S Syn).obj X) (n + 1))
  let A₁ := synAdamsConvergence Syn (XModLambdaN ((nu S Syn).obj X) 1)
  let g := (synAdamsFunctoriality Syn).convergenceMap
    (XModLambdaN.toOne ((nu S Syn).obj X) n)
  let a := q.val ≫ XModLambdaN.toOne ((nu S Syn).obj X) n
  let ha : a ∈ synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) 1)
      degree.1 degree.2 (s : ℤ) :=
    lambdaPowerBockstein_toOne_preserves_filtration
      ((nu S Syn).obj X) n degree.1 degree.2 (s : ℤ) q.val q.property
  let aFiltered : synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) 1)
      degree.1 degree.2 (s : ℤ) := ⟨a, ha⟩
  have haZero : A₁.homotopyGradedProjection (s : ℤ) degree aFiltered = 0 :=
    (A₁.homotopyGradedProjection_eq_zero_iff
      (s : ℤ) degree aFiltered).mpr haNext
  have hnat := lambdaPowerToOne_homotopyGradedProjection
    (S := S) (Syn := Syn) X n degree (s : ℤ) q
  have himage :
      (Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
        (s : ℤ) degree).hom
          (Aₙ.homotopyGradedProjection (s : ℤ) degree q) = 0 := by
    exact hnat.trans haZero
  have hsource : Aₙ.homotopyGradedProjection (s : ℤ) degree q = 0 :=
    (lambdaPowerToOne_generator_inducedGradedMap_injective
      (S := S) (Syn := Syn) X n s t) (himage.trans (map_zero _).symm)
  exact (Aₙ.homotopyGradedProjection_eq_zero_iff
    (s : ℤ) degree q).mp hsource

/-- If the actual source class already lies in the next filtration layer,
then the source page class supplied by an occurrence is zero.  Consequently
the represented target page class is zero as well. -/
theorem LambdaBocksteinOccursOn.exists_page_differential_eq_zero
    {Y : Syn} {degree : ℤ × ℤ} {r s : ℤ}
    {a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1}
    {b : Smn (Syn := Syn) degree.1 degree.2 ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj Y)}
    (h : LambdaBocksteinOccursOn (Syn := Syn) Y degree r s a b)
    (haNext : a ∈ synAdamsFiltration Syn (XModLambdaN Y 1)
      degree.1 degree.2 (s + 1)) :
    let f := lambdaPowerBocksteinCSSMap Y 1
    let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
    let T := AddCommGrpCat.of ℤ
    ∃ (x : T ⟶ (E.ssData (s, 1)).V)
      (y : T ⟶ (E.ssData ((s, 1) + E.diffDeg r)).V)
      (xPage : T ⟶ E.Page r (s, 1))
      (yPage : T ⟶ E.Page r ((s, 1) + E.diffDeg r)),
      x = 0 ∧ xPage = 0 ∧ yPage = 0 ∧
      xPage ≫ E.d r (s, 1) = yPage ∧
      ElementPageRel E r (s, 1) x xPage ∧
      ElementPageRel E r ((s, 1) + E.diffDeg r) y yPage := by
  dsimp only
  rcases h with ⟨x, y, xl, yl, hx, hy, ha, hb, hrel⟩
  let f := lambdaPowerBocksteinCSSMap Y 1
  let E := ExtensionSpectralSequence.{1, 0, 0, 0} f degree
  let T := AddCommGrpCat.of ℤ
  let A := synAdamsConvergence Syn (XModLambdaN Y 1)
  have haCurrent : a ∈ synAdamsFiltration Syn (XModLambdaN Y 1)
      degree.1 degree.2 s :=
    synAdamsFiltration_mono Syn (XModLambdaN Y 1)
      degree.1 degree.2 s haNext
  let aFiltered : synAdamsFiltration Syn (XModLambdaN Y 1)
      degree.1 degree.2 s := ⟨a, haCurrent⟩
  have hfil : A.filtrationEquiv s degree (xl.hom 1) = aFiltered := by
    apply Subtype.ext
    exact (A.filtrationEquiv_comm s degree (xl.hom 1)).symm.trans ha
  have hxlOne : xl.hom 1 =
      (A.filtrationEquiv s degree).symm aFiltered := by
    apply (A.filtrationEquiv s degree).injective
    rw [hfil, AddEquiv.apply_symm_apply]
  have hproj : A.homotopyGradedProjection s degree aFiltered = 0 :=
    (A.homotopyGradedProjection_eq_zero_iff s degree aFiltered).mpr haNext
  let FC := unboundedUnderlyingComplex f degree
  have hxlZero : xl ≫ FC.filToAssocGraded s 1 = 0 := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change (FC.filToAssocGraded s 1).hom (xl.hom z) = 0
    have hzx : xl.hom z = z • xl.hom 1 := by
      change ℤ at z
      calc
        xl.hom z = xl.hom (z • (1 : ℤ)) := by simp
        _ = z • xl.hom 1 := map_zsmul _ _ _
    rw [hzx, map_zsmul, hxlOne]
    change z • A.homotopyGradedProjection s degree aFiltered = 0
    rw [hproj, smul_zero]
  have hxZero : x = 0 := by
    apply (cancel_mono (unboundedExtensionVComplexIso f degree s 1).hom).mp
    rw [← hx, hxlZero, zero_comp]
  let y' : T ⟶ (E.ssData ((s, 1) + E.diffDeg r)).V :=
    Eq.mpr (congrArg (fun B : AddCommGrpCat.{0} => T ⟶ B)
      (show
        (E.ssData ((s, 1) + E.diffDeg r)).V =
          (unboundedExtensionSSData.{1, 0, 0, 0}
            f degree (s + r, 0)).V by
          change
            (unboundedExtensionSSData.{1, 0, 0, 0}
              f degree (s + r, 0)).V =
            (unboundedExtensionSSData.{1, 0, 0, 0}
              f degree (s + r, 0)).V
          rfl)) y
  change DifferentialRelation E r (s, 1) x y' at hrel
  obtain ⟨xPage, yPage, hd, hxPage, hyPage⟩ :=
    (dr_apply_iff_rel E r (s, 1) x y').mpr hrel
  have hxPageZero : xPage = 0 := by
    rcases hxPage with ⟨xZ, hxZ, hxClass⟩
    have hxZZero : xZ = 0 := by
      apply (cancel_mono ((E.ssData (s, 1)).Z
        (↑(r - E.r₀).toNat : WithTop ℕ)).arrow).mp
      rw [hxZ, hxZero, zero_comp]
    rw [← hxClass, hxZZero, zero_comp]
  have hyPageZero : yPage = 0 := by
    rw [← hd, hxPageZero, zero_comp]
  exact ⟨x, y', xPage, yPage, hxZero, hxPageZero, hyPageZero,
    hd, hxPage, hyPage⟩

/-- Actual filtered representatives related by the lambda connecting map
produce a lambda-Bockstein differential relation. -/
theorem lambdaBocksteinOccursOn_of_filtered_boundary
    (Y : Syn) (degree : ℤ × ℤ) (r s : ℤ) (hr : 0 ≤ r)
    (a : Smn (Syn := Syn) degree.1 degree.2 ⟶ XModLambdaN Y 1)
    (b : Smn (Syn := Syn) degree.1 degree.2 ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj Y))
    (ha : a ∈ synAdamsFiltration Syn (XModLambdaN Y 1)
      degree.1 degree.2 s)
    (hb : b ∈ synAdamsFiltration Syn
      ((shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj Y))
      degree.1 degree.2 (s + r))
    (hab : a ≫ lambdaBocksteinConnecting Y = b) :
    LambdaBocksteinOccursOn (Syn := Syn) Y degree r s a b := by
  let A := synAdamsConvergence Syn (XModLambdaN Y 1)
  let B := synAdamsConvergence Syn
    ((shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj Y))
  let f := lambdaPowerBocksteinCSSMap Y 1
  let FC := unboundedUnderlyingComplex f degree
  let T := AddCommGrpCat.of ℤ
  let aFil := (A.filtrationEquiv s degree).symm ⟨a, ha⟩
  let bFil := (B.filtrationEquiv (s + r) degree).symm ⟨b, hb⟩
  let xl : T ⟶ Subobject.underlying.obj
      ((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree) :=
    AddCommGrpCat.ofHom
      { toFun := fun z => z • aFil
        map_zero' := zero_zsmul aFil
        map_add' := fun p q => add_zsmul aFil p q }
  let yl : T ⟶ Subobject.underlying.obj
      ((lambdaPowerBocksteinTargetCSS Y 1).F.F (s + r) degree) :=
    AddCommGrpCat.ofHom
      { toFun := fun z => z • bFil
        map_zero' := zero_zsmul bFil
        map_add' := fun p q => add_zsmul bFil p q }
  have hxl (z : T) : xl.hom z = z • aFil := by
    rfl
  have hyl (z : T) : yl.hom z = z • bFil := by
    rfl
  let x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      f degree (s, 1)).V :=
    (xl ≫ FC.filToAssocGraded s 1) ≫
      (unboundedExtensionVComplexIso f degree s 1).inv
  let y : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      f degree (s + r, 0)).V :=
    (yl ≫ FC.filToAssocGraded (s + r) 0) ≫
      (unboundedExtensionVComplexIso f degree (s + r) 0).inv
  have hx : FC.IsLift s 1 xl
      (x ≫ (unboundedExtensionVComplexIso f degree s 1).hom) := by
    dsimp only [FilteredComplex.IsLift, x]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hy : FC.IsLift (s + r) 0 yl
      (y ≫ (unboundedExtensionVComplexIso f degree (s + r) 0).hom) := by
    dsimp only [FilteredComplex.IsLift, y]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have haEval : A.abutmentEquiv degree
        (((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
          (xl.hom 1)) = a := by
    change A.abutmentEquiv degree
      ((A.filtration.F s degree).arrow.hom (xl.hom 1)) = a
    rw [A.filtrationEquiv_comm]
    simp [xl, aFil]
  have hbEval : B.abutmentEquiv degree
        (((lambdaPowerBocksteinTargetCSS Y 1).F.F (s + r) degree).arrow.hom
          (yl.hom 1)) = b := by
    change B.abutmentEquiv degree
      ((B.filtration.F (s + r) degree).arrow.hom (yl.hom 1)) = b
    rw [B.filtrationEquiv_comm]
    simp [yl, bFil]
  have hboundary : ∀ z : T,
      LambdaPowerBoundary.boundaryHom
        (Smn (Syn := Syn) degree.1 degree.2) Y 1
        (A.abutmentEquiv degree
          (((lambdaPowerBocksteinSourceCSS Y 1).F.F s degree).arrow.hom
            (xl.hom z))) =
      B.abutmentEquiv degree
        (((lambdaPowerBocksteinTargetCSS Y 1).F.F (s + r) degree).arrow.hom
          (yl.hom z)) := by
    intro z
    change ℤ at z
    change LambdaPowerBoundary.boundaryHom _ Y 1
        (A.abutmentEquiv degree
          ((A.filtration.F s degree).arrow.hom (xl.hom z))) =
      B.abutmentEquiv degree
        ((B.filtration.F (s + r) degree).arrow.hom (yl.hom z))
    rw [A.filtrationEquiv_comm, B.filtrationEquiv_comm]
    rw [hxl, hyl]
    have hsource :
        ((A.filtrationEquiv s degree) (z • aFil)).1 = z • a := by
      calc
        ((A.filtrationEquiv s degree) (z • aFil)).1 =
            (z • (A.filtrationEquiv s degree) aFil).1 :=
          congrArg Subtype.val
            ((A.filtrationEquiv s degree).toAddMonoidHom.map_zsmul z aFil)
        _ = z • a := by
          rw [show (A.filtrationEquiv s degree) aFil = ⟨a, ha⟩ from
            (A.filtrationEquiv s degree).apply_symm_apply ⟨a, ha⟩]
          rfl
    have htarget :
        ((B.filtrationEquiv (s + r) degree) (z • bFil)).1 = z • b := by
      calc
        ((B.filtrationEquiv (s + r) degree) (z • bFil)).1 =
            (z • (B.filtrationEquiv (s + r) degree) bFil).1 :=
          congrArg Subtype.val
            ((B.filtrationEquiv (s + r) degree).toAddMonoidHom.map_zsmul z bFil)
        _ = z • b := by
          rw [show (B.filtrationEquiv (s + r) degree) bFil = ⟨b, hb⟩ from
            (B.filtrationEquiv (s + r) degree).apply_symm_apply ⟨b, hb⟩]
          rfl
    have hab' : LambdaPowerBoundary.boundaryHom
        (Smn (Syn := Syn) degree.1 degree.2) Y 1 a = b := by
      exact hab
    rw [hsource, htarget,
      (LambdaPowerBoundary.boundaryHom
        (Smn (Syn := Syn) degree.1 degree.2) Y 1).map_zsmul, hab']
  have hrel := lambdaPowerBockstein_relation_of_homotopy_boundary
    Y 1 degree r hr s (s + r) rfl hx hy hboundary
  exact ⟨x, y, xl, yl, hx, hy, haEval, hbEval, hrel⟩

/-- Geometric data underlying the synthetic Adams spectral sequence of
`nu X`. The realization field is exactly the assertion that a divided page
target can be represented at the required stage with the same relative
representative. -/
structure NuSynAdamsGeometricModel (X : S) where
  input : GeometricAdams.Input ((nu S Syn).obj X)
  freeLayers : input.FreeLayers
  realization : input.SyntheticAdamsGeometricRealization freeLayers
  quotientFiltration_eq (n s : ℕ) (m w : ℤ) :
    (input.quotient n).filtration (Smn (Syn := Syn) m w) s =
      synAdamsFiltration Syn (XModLambdaN ((nu S Syn).obj X) n)
        m w (s : ℤ)
  boundaryTargetFiltration_eq (n s : ℕ) (m w : ℤ) :
    (input.boundaryTarget n).filtration (Smn (Syn := Syn) m w) s =
      synAdamsFiltration Syn
        ((shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -(n : ℤ))).obj
            ((nu S Syn).obj X))) m w (s : ℤ)

namespace NuSynAdamsGeometricModel

variable {S Syn} {X : S}

/-- The sphere which represents Adams filtration `s` and internal degree
`t`; this spelling keeps the generator weight definitionally equal to
`(t-s)+s` in the geometric page API. -/
noncomputable abbrev SourceSphere (s : ℕ) (t : ℤ) : Syn :=
  Smn (Syn := Syn) (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ))

/-- The displayed source sphere is canonically the usual sphere of
homotopy degree `(t-s,t)`.  The expanded weight in `SourceSphere` is kept
for the free-layer API; this is the transport used by the canonical Adams
filtration and finite-quotient detection maps. -/
noncomputable def sourceSphereIso (s : ℕ) (t : ℤ) :
    SourceSphere (Syn := Syn) s t ≅ Smn (Syn := Syn) (t - (s : ℤ)) t :=
  eqToIso (congrArg (fun w : ℤ =>
    Smn (Syn := Syn) (t - (s : ℤ)) w)
      (show t - (s : ℤ) + (s : ℤ) = t by omega))

/-- The target quotient in which the boundary of a geometric representative
of an `r`-differential is read. -/
abbrev TargetPage (M : NuSynAdamsGeometricModel S Syn X)
    (s r : ℕ) (hr : 1 ≤ r) (t : ℤ) :=
  (SourceSphere (Syn := Syn) s t ⟶
      (shiftFunctor Syn (1 : ℤ)).obj (M.input.layer (s + r))) ⧸
    M.input.targetAmbiguity
      (SourceSphere (Syn := Syn) s t) s r hr

theorem quotient_afGe_iff_synAdamsFiltration
    (M : NuSynAdamsGeometricModel S Syn X)
    (n s : ℕ) (m w : ℤ)
    (a : Smn (Syn := Syn) m w ⟶ XModLambdaN ((nu S Syn).obj X) n) :
    (M.input.quotient n).AFGe a s ↔
      a ∈ synAdamsFiltration Syn (XModLambdaN ((nu S Syn).obj X) n)
        m w (s : ℤ) := by
  change a ∈ (M.input.quotient n).filtration (Smn m w) s ↔ _
  rw [M.quotientFiltration_eq]

theorem boundaryTarget_afGe_iff_synAdamsFiltration
    (M : NuSynAdamsGeometricModel S Syn X)
    (n s : ℕ) (m w : ℤ)
    (a : Smn (Syn := Syn) m w ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -(n : ℤ))).obj
          ((nu S Syn).obj X))) :
    (M.input.boundaryTarget n).AFGe a s ↔
      a ∈ synAdamsFiltration Syn
        ((shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -(n : ℤ))).obj
            ((nu S Syn).obj X))) m w (s : ℤ) := by
  change a ∈ (M.input.boundaryTarget n).filtration (Smn m w) s ↔ _
  rw [M.boundaryTargetFiltration_eq]

/-- The finite-quotient class of a cap, written on the standard sphere
`S^(t-s,t)`, lies in the canonical Adams filtration at the cap's source
stage. -/
theorem capQuotientClass_canonical_mem_filtration
    (M : NuSynAdamsGeometricModel S Syn X)
    (s r n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (SourceSphere (Syn := Syn) s t) s r n) :
    (sourceSphereIso (Syn := Syn) s t).inv ≫
        M.input.capQuotientClass
          (SourceSphere (Syn := Syn) s t) s r n c ∈
      synAdamsFiltration Syn
        (XModLambdaN ((nu S Syn).obj X) n)
        (t - (s : ℤ)) t (s : ℤ) := by
  let e := sourceSphereIso (Syn := Syn) s t
  let q := M.input.capQuotientClass
    (SourceSphere (Syn := Syn) s t) s r n c
  obtain ⟨qStage, hqStage⟩ :=
    M.input.capQuotientClass_mem_filtration
      (SourceSphere (Syn := Syn) s t) s r n c
  have hge : (M.input.quotient n).AFGe (e.inv ≫ q) s := by
    refine ⟨e.inv ≫ qStage, ?_⟩
    change (e.inv ≫ qStage) ≫ (M.input.quotient n).toBase s = e.inv ≫ q
    change qStage ≫ (M.input.quotient n).toBase s = q at hqStage
    rw [Category.assoc, hqStage]
  exact (M.quotient_afGe_iff_synAdamsFiltration n s
    (t - (s : ℤ)) t (e.inv ≫ q)).mp hge

/-- The canonical finite-quotient Adams class detected by an actual cap. -/
noncomputable def capQuotientDetectedClass
    (M : NuSynAdamsGeometricModel S Syn X)
    (s r : ℕ) (hr : 2 ≤ r) (t : ℤ)
    (c : M.input.CapRepresentatives
      (SourceSphere (Syn := Syn) s t) s r (r - 1)) :
    (SynAdamsSS Syn ((nu S Syn).obj X)).Page (r : ℤ)
      ((s : ℤ), t, t) :=
  nuModLambdaPredGeneratorDetection S Syn X r hr (s : ℤ) t
    ⟨(sourceSphereIso (Syn := Syn) s t).inv ≫
        M.input.capQuotientClass
          (SourceSphere (Syn := Syn) s t) s r (r - 1) c,
      M.capQuotientClass_canonical_mem_filtration s r (r - 1) t c⟩

/-- Every actual cap gives a differential occurrence in the canonical
single-lambda Bockstein ESS.  The source is the finite lambda quotient class
of the cap restricted to `X/lambda`; its target is its actual lambda
connecting boundary. -/
theorem lambdaBocksteinOccursOn_of_cap
    (M : NuSynAdamsGeometricModel S Syn X)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (SourceSphere (Syn := Syn) s t) s (n + 2) (n + 1)) :
    let aOne :=
      M.input.capQuotientClass (SourceSphere (Syn := Syn) s t)
          s (n + 2) (n + 1) c ≫
        XModLambdaN.toOne ((nu S Syn).obj X) n
    let bOne :=
      aOne ≫ lambdaBocksteinConnecting ((nu S Syn).obj X)
    LambdaBocksteinOccursOn (Syn := Syn) ((nu S Syn).obj X)
      (t - (s : ℤ), t - (s : ℤ) + (s : ℤ))
      ((n + 2 : ℕ) : ℤ) (s : ℤ) aOne bOne := by
  dsimp only
  let sphere := SourceSphere (Syn := Syn) s t
  let qPower := M.input.capQuotientClass sphere s (n + 2) (n + 1) c
  let aOne := qPower ≫ XModLambdaN.toOne ((nu S Syn).obj X) n
  let bOne := aOne ≫ lambdaBocksteinConnecting ((nu S Syn).obj X)
  have hqPower : (M.input.quotient (n + 1)).AFGe qPower s :=
    M.input.capQuotientClass_mem_filtration sphere s (n + 2) (n + 1) c
  have hAFa : (M.input.quotient 1).AFGe aOne s :=
    M.input.toOne_preserves_filtration n sphere s qPower hqPower
  let yStage :=
    M.input.capStageBoundary sphere s (n + 2) (n + 1) c ≫
      (shiftFunctor Syn (1 : ℤ)).map
        (lambdaPowerToOne (M.input.stage (s + (n + 2))) n)
  have hboundary : aOne ≫
      lambdaBocksteinConnecting ((nu S Syn).obj X) =
        yStage ≫ (M.input.boundaryTarget 1).toBase (s + (n + 2)) := by
    exact M.input.capQuotientClass_toOne_boundary
      sphere s (n + 2) n c
  have hAFb : (M.input.boundaryTarget 1).AFGe bOne (s + (n + 2)) := by
    exact ⟨yStage, hboundary.symm⟩
  have ha : aOne ∈ synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) 1)
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ)) (s : ℤ) :=
    (M.quotient_afGe_iff_synAdamsFiltration 1 s
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ)) aOne).mp hAFa
  have hb : bOne ∈ synAdamsFiltration Syn
      ((shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj
          ((nu S Syn).obj X)))
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ))
      (((s + (n + 2) : ℕ) : ℤ)) :=
    (M.boundaryTarget_afGe_iff_synAdamsFiltration 1 (s + (n + 2))
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ)) bOne).mp hAFb
  have hb' : bOne ∈ synAdamsFiltration Syn
      ((shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj
          ((nu S Syn).obj X)))
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ))
      ((s : ℤ) + ((n + 2 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hb
  exact lambdaBocksteinOccursOn_of_filtered_boundary
    (Syn := Syn) ((nu S Syn).obj X)
    (t - (s : ℤ), t - (s : ℤ) + (s : ℤ))
    ((n + 2 : ℕ) : ℤ) (s : ℤ) (by omega)
    aOne bOne ha hb' rfl

/-- Canonically regraded form of `lambdaBocksteinOccursOn_of_cap`, with the
source written on `S^(t-s,t)`.  This is the form compatible with the
finite-quotient detection map and the Adams tridegree `(s,t,t)`. -/
theorem canonicalLambdaBocksteinOccursOn_of_cap
    (M : NuSynAdamsGeometricModel S Syn X)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (SourceSphere (Syn := Syn) s t) s (n + 2) (n + 1)) :
    let qPower :=
      (sourceSphereIso (Syn := Syn) s t).inv ≫
        M.input.capQuotientClass (SourceSphere (Syn := Syn) s t)
          s (n + 2) (n + 1) c
    let aOne := qPower ≫ XModLambdaN.toOne ((nu S Syn).obj X) n
    let bOne := aOne ≫ lambdaBocksteinConnecting ((nu S Syn).obj X)
    LambdaBocksteinOccursOn (Syn := Syn) ((nu S Syn).obj X)
      (t - (s : ℤ), t) ((n + 2 : ℕ) : ℤ) (s : ℤ) aOne bOne := by
  dsimp only
  let sphere := SourceSphere (Syn := Syn) s t
  let e := sourceSphereIso (Syn := Syn) s t
  let qPower := e.inv ≫
    M.input.capQuotientClass sphere s (n + 2) (n + 1) c
  let aOne := qPower ≫ XModLambdaN.toOne ((nu S Syn).obj X) n
  let bOne := aOne ≫ lambdaBocksteinConnecting ((nu S Syn).obj X)
  have hqPower : qPower ∈ synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) (n + 1))
      (t - (s : ℤ)) t (s : ℤ) :=
    M.capQuotientClass_canonical_mem_filtration s (n + 2) (n + 1) t c
  have ha : aOne ∈ synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) 1)
      (t - (s : ℤ)) t (s : ℤ) :=
    lambdaPowerBockstein_toOne_preserves_filtration
      ((nu S Syn).obj X) n (t - (s : ℤ)) t (s : ℤ) qPower hqPower
  let yStage := e.inv ≫
    M.input.capStageBoundary sphere s (n + 2) (n + 1) c ≫
      (shiftFunctor Syn (1 : ℤ)).map
        (lambdaPowerToOne (M.input.stage (s + (n + 2))) n)
  have hboundary : aOne ≫
      lambdaBocksteinConnecting ((nu S Syn).obj X) =
        yStage ≫ (M.input.boundaryTarget 1).toBase (s + (n + 2)) := by
    have h := M.input.capQuotientClass_toOne_boundary
      sphere s (n + 2) n c
    exact (by
      simpa only [aOne, qPower, yStage, Category.assoc] using
        congrArg (fun f => e.inv ≫ f) h)
  have hAFb : (M.input.boundaryTarget 1).AFGe bOne (s + (n + 2)) := by
    exact ⟨yStage, hboundary.symm⟩
  have hb : bOne ∈ synAdamsFiltration Syn
      ((shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj
          ((nu S Syn).obj X)))
      (t - (s : ℤ)) t (((s + (n + 2) : ℕ) : ℤ)) :=
    (M.boundaryTarget_afGe_iff_synAdamsFiltration 1 (s + (n + 2))
      (t - (s : ℤ)) t bOne).mp hAFb
  have hb' : bOne ∈ synAdamsFiltration Syn
      ((shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj
          ((nu S Syn).obj X)))
      (t - (s : ℤ)) t ((s : ℤ) + ((n + 2 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hb
  exact lambdaBocksteinOccursOn_of_filtered_boundary
    (Syn := Syn) ((nu S Syn).obj X) (t - (s : ℤ), t)
    ((n + 2 : ℕ) : ℤ) (s : ℤ) (by omega)
    aOne bOne ha hb' rfl

/-- Every actual cap determines source and target classes on the canonical
single-lambda Bockstein page, and the page differential is represented by
the actual connecting boundary of that same cap.  This is the page-level
form of `lambdaBocksteinOccursOn_of_cap`; no cap chosen from a pre-existing
Adams differential is required. -/
theorem exists_lambdaBockstein_page_differential_of_cap
    (M : NuSynAdamsGeometricModel S Syn X)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (SourceSphere (Syn := Syn) s t) s (n + 2) (n + 1)) :
    let degree : ℤ × ℤ :=
      (t - (s : ℤ), t - (s : ℤ) + (s : ℤ))
    let E := canonicalLambdaPowerBocksteinESS
      ((nu S Syn).obj X) 1 degree
    let T := AddCommGrpCat.of ℤ
    let aOne :=
      M.input.capQuotientClass (SourceSphere (Syn := Syn) s t)
          s (n + 2) (n + 1) c ≫
        XModLambdaN.toOne ((nu S Syn).obj X) n
    let bOne :=
      aOne ≫ lambdaBocksteinConnecting ((nu S Syn).obj X)
    ∃ (xAmbient : T ⟶ (E.ssData ((s : ℤ), 1)).V)
      (yAmbient : T ⟶
        (E.ssData (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))).V)
      (xPage : T ⟶ E.Page ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1))
      (yPage : T ⟶ E.Page ((n + 2 : ℕ) : ℤ)
        (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))),
      xPage ≫ E.d ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) = yPage ∧
      ElementPageRel E ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1)
        xAmbient xPage ∧
      ElementPageRel E ((n + 2 : ℕ) : ℤ)
        (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))
        yAmbient yPage := by
  dsimp only
  obtain ⟨xAmbient, yAmbient, xPage, yPage, hd, hxPage, hyPage⟩ :=
    (M.lambdaBocksteinOccursOn_of_cap s n t c).exists_page_differential
  exact ⟨xAmbient, yAmbient, xPage, yPage, hd, hxPage, hyPage⟩

end NuSynAdamsGeometricModel

/-- Comparison of the declared synthetic Adams page with the page built from
the actual tower. The last field says that the declared differential is the
projected relative boundary of the same geometric representative. -/
structure NuSynAdamsGeometricComparison (X : S)
    (M : NuSynAdamsGeometricModel S Syn X) where
  sourceEquiv (s r : ℕ) (hr : 2 ≤ r) (t : ℤ) :
    ((SynAdamsSS Syn ((nu S Syn).obj X)).Page (r : ℤ) ((s : ℤ), t, t)) ≃+
      M.input.PageGroup
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t) s r (by omega)
  /-- The page comparison uses the same filtered class as finite-quotient
  Adams detection.  This is the source coherence contained in saying that
  the declared Adams spectral sequence comes from this filtered synthetic
  spectrum, rather than from an unrelated abstract page isomorphism. -/
  source_detects_cap (s r : ℕ) (hr : 2 ≤ r) (t : ℤ)
      (c : M.input.CapRepresentatives
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s r (r - 1)) :
    M.capQuotientDetectedClass s r hr t c =
      (sourceEquiv s r hr t).symm
        (M.input.capSourceClass
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s r (by omega) (r - 1) c)
  targetEquiv (s r : ℕ) (hr : 2 ≤ r) (t : ℤ) :
    ((SynAdamsSS Syn ((nu S Syn).obj X)).Page (r : ℤ)
        ((s : ℤ) + (r : ℤ), t + (r : ℤ) - 1, t)) ≃+
      M.TargetPage s r (by omega) t
  differential (s r : ℕ) (hr : 2 ≤ r) (t : ℤ)
      (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
        (r : ℤ) ((s : ℤ), t, t)) :
    targetEquiv s r hr t
        ((synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
          (r : ℤ) (s : ℤ) t t).hom x) =
      M.input.pageObstruction
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s r (by omega) (sourceEquiv s r hr t x)

/-- The complete filtered origin of the declared synthetic Adams spectral
sequence.  `model.input.tower` is the filtered synthetic spectrum;
`comparison.sourceEquiv` identifies its graded relative-disk classes with the
declared Adams page, and `comparison.differential` says that `d_r` is obtained
by taking the actual boundary of the same relative disk and projecting it to
the target graded piece. -/
structure NuSynAdamsFilteredGeometricOrigin (X : S) where
  model : NuSynAdamsGeometricModel S Syn X
  comparison : NuSynAdamsGeometricComparison S Syn X model

/-- Geometric-origin axiom for the synthetic Adams spectral sequence: it is
induced by a filtered synthetic spectrum, and every `d_r` is represented by a
relative disk whose source in the first graded piece is the source class and
whose boundary in the `r`-th graded piece is the target class. -/
axiom nuSynAdamsFilteredGeometricOrigin (X : S) :
  NuSynAdamsFilteredGeometricOrigin S Syn X

/-- The filtered model selected by the geometric-origin axiom. -/
noncomputable def nuSynAdamsGeometricModel (X : S) :
    NuSynAdamsGeometricModel S Syn X :=
  (nuSynAdamsFilteredGeometricOrigin S Syn X).model

/-- The page comparison selected by the same geometric-origin axiom. -/
noncomputable def nuSynAdamsGeometricComparison (X : S) :
    NuSynAdamsGeometricComparison S Syn X
      (nuSynAdamsGeometricModel S Syn X) :=
  (nuSynAdamsFilteredGeometricOrigin S Syn X).comparison

namespace NuSynAdamsGeometricComparison

variable {S Syn} {X : S} {M : NuSynAdamsGeometricModel S Syn X}

/-- A cap relation has zero canonical finite-quotient detection, hence its
actual finite-quotient class lies one Adams-filtration step deeper.  This is
the kernel statement needed to descend the cap construction to the
lambda-Bockstein source page. -/
theorem capQuotientClass_mem_next_filtration_of_relation
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s r p : ℕ) (hr : 2 ≤ r) (hp : p = r - 1) (t : ℤ)
    (c : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s r p)
    (hc : c ∈ M.input.capRelations
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s r (by omega) p) :
    (NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t).inv ≫
        M.input.capQuotientClass
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s r p c ∈
      synAdamsFiltration Syn
        (XModLambdaN ((nu S Syn).obj X) p)
        (t - (s : ℤ)) t ((s + 1 : ℕ) : ℤ) := by
  subst p
  let q :=
    (NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t).inv ≫
      M.input.capQuotientClass
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s r (r - 1) c
  have hq : q ∈ synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) (r - 1))
      (t - (s : ℤ)) t (s : ℤ) :=
    M.capQuotientClass_canonical_mem_filtration s r (r - 1) t c
  let qFiltered : synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) (r - 1))
      (t - (s : ℤ)) t (s : ℤ) := ⟨q, hq⟩
  have hsource : M.input.capSourceClass
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s r (by omega) (r - 1) c = 0 := by
    have hker : c ∈ (M.input.capSourceHom
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s r (by omega) (r - 1)).ker := by
      rw [← M.input.capRelations_eq_ker
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s r (by omega) (r - 1)]
      exact hc
    exact hker
  have hdet : nuModLambdaPredGeneratorDetection S Syn X r hr (s : ℤ) t
      qFiltered = 0 := by
    change M.capQuotientDetectedClass s r hr t c = 0
    rw [C.source_detects_cap s r hr t c, hsource, map_zero]
  exact (nuModLambdaPredGeneratorDetection_eq_zero_iff
    S Syn X r hr (s : ℤ) t qFiltered).mp hdet

/-- After restriction to the first lambda quotient, a cap relation still
lies one filtration step deeper. -/
theorem capToOne_mem_next_filtration_of_relation
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (n + 1))
    (hc : c ∈ M.input.capRelations
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (by omega) (n + 1)) :
    ((NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t).inv ≫
        M.input.capQuotientClass
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s (n + 2) (n + 1) c) ≫
        XModLambdaN.toOne ((nu S Syn).obj X) n ∈
      synAdamsFiltration Syn
        (XModLambdaN ((nu S Syn).obj X) 1)
        (t - (s : ℤ)) t ((s + 1 : ℕ) : ℤ) := by
  have hq := C.capQuotientClass_mem_next_filtration_of_relation
    s (n + 2) (n + 1) (by omega) (by omega) t c hc
  exact lambdaPowerBockstein_toOne_preserves_filtration
    ((nu S Syn).obj X) n (t - (s : ℤ)) t ((s + 1 : ℕ) : ℤ) _ hq

/-- The canonical Bockstein source-page representative selected by an actual
cap.  Choice is harmless because `LambdaBocksteinSourcePageRep.unique` proves
that the resulting page morphism is unique. -/
noncomputable def capBocksteinSourcePage
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (n + 1)) :
    AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS ((nu S Syn).obj X) 1
        (t - (s : ℤ), t)).Page ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) :=
  Classical.choose
    ((M.canonicalLambdaBocksteinOccursOn_of_cap s n t c).exists_sourcePageRep)

/-- The chosen cap page class represents exactly the finite-quotient class
obtained from that cap and then restricted to `X/lambda`. -/
theorem capBocksteinSourcePage_spec
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (n + 1)) :
    LambdaBocksteinSourcePageRep (Syn := Syn) ((nu S Syn).obj X)
      (t - (s : ℤ), t) ((n + 2 : ℕ) : ℤ) (s : ℤ)
      (((NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t).inv ≫
          M.input.capQuotientClass
            (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
            s (n + 2) (n + 1) c) ≫
        XModLambdaN.toOne ((nu S Syn).obj X) n)
      (C.capBocksteinSourcePage s n t c) :=
  Classical.choose_spec
    ((M.canonicalLambdaBocksteinOccursOn_of_cap s n t c).exists_sourcePageRep)

/-- Additive cap-to-Bockstein map before quotienting by cap relations. -/
noncomputable def capToBocksteinSourcePageHom
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ) :
    M.input.CapRepresentatives
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1) →+
      (canonicalLambdaPowerBocksteinESS ((nu S Syn).obj X) 1
        (t - (s : ℤ), t)).Page ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) where
  toFun c := (C.capBocksteinSourcePage s n t c).hom 1
  map_zero' := by
    have hchosen := C.capBocksteinSourcePage_spec s n t 0
    have hzero := LambdaBocksteinSourcePageRep.zero
      (Syn := Syn) ((nu S Syn).obj X) (t - (s : ℤ), t)
      ((n + 2 : ℕ) : ℤ) (s : ℤ)
    have heq : C.capBocksteinSourcePage s n t 0 = 0 := by
      apply LambdaBocksteinSourcePageRep.unique (Syn := Syn)
        (h₁ := ?_) (h₂ := hzero)
      simpa only [map_zero, comp_zero, zero_comp] using hchosen
    exact congrArg (fun q => q.hom 1) heq
  map_add' c d := by
    have hchosen := C.capBocksteinSourcePage_spec s n t (c + d)
    have hadd := LambdaBocksteinSourcePageRep.add (Syn := Syn)
      (C.capBocksteinSourcePage_spec s n t c)
      (C.capBocksteinSourcePage_spec s n t d)
    have heq : C.capBocksteinSourcePage s n t (c + d) =
        C.capBocksteinSourcePage s n t c +
          C.capBocksteinSourcePage s n t d := by
      apply LambdaBocksteinSourcePageRep.unique (Syn := Syn)
        (h₁ := hchosen) (h₂ := ?_)
      simpa only [map_add, Preadditive.comp_add, Preadditive.add_comp] using hadd
    exact congrArg (fun q => q.hom 1) heq

/-- Cap relations are killed by the cap-to-Bockstein source map. -/
theorem capToBocksteinSourcePageHom_mem
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (n + 1))
    (hc : c ∈ M.input.capRelations
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (by omega) (n + 1)) :
    C.capToBocksteinSourcePageHom s n t c = 0 := by
  have haNext :
      (((NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t).inv ≫
          M.input.capQuotientClass
            (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
            s (n + 2) (n + 1) c) ≫
        XModLambdaN.toOne ((nu S Syn).obj X) n) ∈
      synAdamsFiltration Syn (XModLambdaN ((nu S Syn).obj X) 1)
        (t - (s : ℤ)) t ((s : ℤ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      C.capToOne_mem_next_filtration_of_relation s n t c hc
  have hzero : C.capBocksteinSourcePage s n t c = 0 :=
    LambdaBocksteinSourcePageRep.eq_zero_of_mem_next (Syn := Syn)
      (C.capBocksteinSourcePage_spec s n t c) haNext
  change (C.capBocksteinSourcePage s n t c).hom 1 = 0
  rw [hzero]
  rfl

/-- The canonical additive map from the geometric cap page to the
lambda-Bockstein source page. -/
noncomputable def capPageToBocksteinSourcePageHom
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ) :
    M.input.CapPage
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (by omega) (n + 1) →+
      (canonicalLambdaPowerBocksteinESS ((nu S Syn).obj X) 1
        (t - (s : ℤ), t)).Page ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) :=
  QuotientAddGroup.lift _ (C.capToBocksteinSourcePageHom s n t) (by
    intro c hc
    exact C.capToBocksteinSourcePageHom_mem s n t c hc)

@[simp] theorem capPageToBocksteinSourcePageHom_mk
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (n + 1)) :
    C.capPageToBocksteinSourcePageHom s n t (QuotientAddGroup.mk c) =
      C.capToBocksteinSourcePageHom s n t c := rfl

/-- The cap page is the declared synthetic Adams page through the geometric
page comparison contained in `C`. -/
noncomputable def capPageEquivSynAdams
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ) :
    M.input.CapPage
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (by omega) (n + 1) ≃+
      (SynAdamsSS Syn ((nu S Syn).obj X)).Page ((n + 2 : ℕ) : ℤ)
        ((s : ℤ), t, t) :=
  (M.input.capPageEquiv M.freeLayers M.realization
    s (n + 2) (by omega) (t - (s : ℤ))).trans
      (C.sourceEquiv s (n + 2) (by omega) t).symm

/-- The page comparison map from synthetic Adams to the canonical
lambda-Bockstein ESS, obtained from actual cap representatives. -/
noncomputable def synAdamsToLambdaBocksteinPageHom
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ) :
    (SynAdamsSS Syn ((nu S Syn).obj X)).Page ((n + 2 : ℕ) : ℤ)
        ((s : ℤ), t, t) →+
      (canonicalLambdaPowerBocksteinESS ((nu S Syn).obj X) 1
        (t - (s : ℤ), t)).Page ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) :=
  (C.capPageToBocksteinSourcePageHom s n t).comp
    (C.capPageEquivSynAdams s n t).symm.toAddMonoidHom

/-- On a cap generator, the cap-to-Adams equivalence is the canonical
finite-quotient detection class. -/
theorem capPageEquivSynAdams_mk
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (n + 1)) :
    C.capPageEquivSynAdams s n t (QuotientAddGroup.mk c) =
      M.capQuotientDetectedClass s (n + 2) (by omega) t c := by
  change (C.sourceEquiv s (n + 2) (by omega) t).symm
      (M.input.capSourceClass
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (by omega) (n + 1) c) = _
  exact (C.source_detects_cap s (n + 2) (by omega) t c).symm

/-- The Adams-to-Bockstein comparison sends the class detected by a cap to
the Bockstein page class represented by that same cap. -/
theorem synAdamsToLambdaBocksteinPageHom_cap
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (n + 1)) :
    C.synAdamsToLambdaBocksteinPageHom s n t
        (M.capQuotientDetectedClass s (n + 2) (by omega) t c) =
      C.capToBocksteinSourcePageHom s n t c := by
  rw [← C.capPageEquivSynAdams_mk s n t c]
  change C.capPageToBocksteinSourcePageHom s n t
      ((C.capPageEquivSynAdams s n t).symm
        (C.capPageEquivSynAdams s n t (QuotientAddGroup.mk c))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- The comparison class attached to a cap supports the Bockstein
differential computed by the actual lambda boundary of the same cap. -/
theorem capBocksteinSourcePage_differential
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (n + 1)) :
    let E := canonicalLambdaPowerBocksteinESS ((nu S Syn).obj X) 1
      (t - (s : ℤ), t)
    let T := AddCommGrpCat.of ℤ
    ∃ (y : T ⟶
        (E.ssData (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))).V)
      (yPage : T ⟶ E.Page ((n + 2 : ℕ) : ℤ)
        (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))),
      C.capBocksteinSourcePage s n t c ≫
          E.d ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) = yPage ∧
      ElementPageRel E ((n + 2 : ℕ) : ℤ)
        (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ)) y yPage := by
  dsimp only
  obtain ⟨y, xPage, yPage, hd, hxRep, hyPage⟩ :=
    (M.canonicalLambdaBocksteinOccursOn_of_cap s n t c).exists_page_differential_sourceRep
  have hx : xPage = C.capBocksteinSourcePage s n t c :=
    LambdaBocksteinSourcePageRep.unique (Syn := Syn) hxRep
      (C.capBocksteinSourcePage_spec s n t c)
  rw [hx] at hd
  exact ⟨y, yPage, hd, hyPage⟩

/-- Every declared synthetic Adams page class is represented by an actual
cap whose finite-quotient detection is that class. -/
theorem exists_cap_detecting_synAdamsClass
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ) ((s : ℤ), t, t)) :
    ∃ c : M.input.CapRepresentatives
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1),
      M.capQuotientDetectedClass s (n + 2) (by omega) t c = x := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    (M.input.capRelations
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (by omega) (n + 1))
    ((C.capPageEquivSynAdams s n t).symm x)
  refine ⟨c, ?_⟩
  rw [← C.capPageEquivSynAdams_mk s n t c]
  change C.capPageEquivSynAdams s n t
      ((QuotientAddGroup.mk'
        (M.input.capRelations
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s (n + 2) (by omega) (n + 1))) c) = x
  rw [hc, AddEquiv.apply_symm_apply]

/-- If a declared Adams differential is zero, a cap detecting its source has
the same divided target as a cap relation.  The latter cap represents the
zero source class in the finite λ quotient.  This is the geometric cycle
step: the zero Adams target is converted into an actual zero-source cap
with the identical divided boundary. -/
theorem exists_capRelation_same_dividedTarget_of_adams_differential_eq_zero
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ) ((s : ℤ), t, t))
    (hzero : (synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
      ((n + 2 : ℕ) : ℤ) (s : ℤ) t t).hom x = 0) :
    ∃ (c d : M.input.CapRepresentatives
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1)),
      M.capQuotientDetectedClass s (n + 2) (by omega) t c = x ∧
      d ∈ M.input.capRelations
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (by omega) (n + 1) ∧
      M.input.capDividedTarget
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1) d =
        M.input.capDividedTarget
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s (n + 2) (n + 1) c := by
  obtain ⟨c, hc⟩ := C.exists_cap_detecting_synAdamsClass s n t x
  have hsource : C.sourceEquiv s (n + 2) (by omega) t x =
      M.input.capSourceClass
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (by omega) (n + 1) c := by
    rw [← hc, C.source_detects_cap]
    exact AddEquiv.apply_symm_apply _ _
  have htarget : M.input.pageObstruction
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (by omega)
      (M.input.capSourceClass
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (by omega) (n + 1) c) = 0 := by
    rw [← hsource, ← C.differential, hzero, map_zero]
  have hcapzero : M.input.capDifferential
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (by omega) (n + 1) (QuotientAddGroup.mk c) = 0 := by
    apply (M.input.dividedTargetEquiv M.freeLayers s (n + 2)
      (by omega) (t - (s : ℤ))).injective
    dsimp only [NuSynAdamsGeometricModel.SourceSphere]
    have hpage := M.input.pageObstruction_capSourceClass
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (by omega) (n + 1) c
    rw [htarget] at hpage
    rw [map_zero]
    calc
      _ = QuotientAddGroup.mk
        (M.input.capDividedTarget
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s (n + 2) (n + 1) c ≫
            (shiftFunctor Syn (1 : ℤ)).map
              (lambdaPow (n + 1) (M.input.layer (s + (n + 2))))) := by
          rfl
      _ = 0 := hpage.symm
  obtain ⟨d, hd, hdivided⟩ :=
    (M.input.capDifferential_mk_eq_zero_iff_exists_capRelation_same_dividedTarget
      M.freeLayers M.realization s (n + 2) (by omega) (t - (s : ℤ)) c).mp hcapzero
  exact ⟨c, d, hc, hd, hdivided⟩

/-- For two caps with the same divided target, their actual single-λ
boundaries have equal current Adams associated-graded classes.  This is the
filtration form used to identify the two Bockstein target-page
representatives. -/
theorem capSingleLambdaBoundary_sub_mem_next_of_same_dividedTarget
    [SyntheticShiftCofiberCompatibility (Syn := Syn)]
    (M : NuSynAdamsGeometricModel S Syn X)
    (s n : ℕ) (t : ℤ)
    (c d : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (n + 1))
    (hdivided : M.input.capDividedTarget
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1) c =
      M.input.capDividedTarget
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1) d) :
    ((M.input.capQuotientClass
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1) c ≫ XModLambdaN.toOne ((nu S Syn).obj X) n) ≫
        lambdaBocksteinConnecting ((nu S Syn).obj X) -
      (M.input.capQuotientClass
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1) d ≫ XModLambdaN.toOne ((nu S Syn).obj X) n) ≫
        lambdaBocksteinConnecting ((nu S Syn).obj X)) ∈
      synAdamsFiltration Syn
        ((shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj ((nu S Syn).obj X)))
        (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ))
        ((s : ℤ) + ((n + 2 : ℕ) : ℤ) + 1) := by
  have hfiltered := M.input.capToOne_boundary_sub_mem_next_of_same_dividedTarget
    (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) n c d hdivided
  have h := (M.boundaryTarget_afGe_iff_synAdamsFiltration 1
    (s + (n + 2) + 1) (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ)) _).mp hfiltered
  simpa [NuSynAdamsGeometricModel.SourceSphere] using h

/-- The same filtration comparison after changing the source to the
standard generator sphere used by the canonical Bockstein page. -/
theorem canonicalCapSingleLambdaBoundary_sub_mem_next_of_same_dividedTarget
    [SyntheticShiftCofiberCompatibility (Syn := Syn)]
    (M : NuSynAdamsGeometricModel S Syn X)
    (s n : ℕ) (t : ℤ)
    (c d : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (n + 1))
    (hdivided : M.input.capDividedTarget
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1) c =
      M.input.capDividedTarget
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1) d) :
    (((NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t).inv ≫
        M.input.capQuotientClass
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s (n + 2) (n + 1) c ≫
        XModLambdaN.toOne ((nu S Syn).obj X) n) ≫
          lambdaBocksteinConnecting ((nu S Syn).obj X)) -
      (((NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t).inv ≫
        M.input.capQuotientClass
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s (n + 2) (n + 1) d ≫
        XModLambdaN.toOne ((nu S Syn).obj X) n) ≫
          lambdaBocksteinConnecting ((nu S Syn).obj X)) ∈
      synAdamsFiltration Syn
        ((shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj ((nu S Syn).obj X)))
        (t - (s : ℤ)) t
        ((s : ℤ) + ((n + 2 : ℕ) : ℤ) + 1) := by
  let sphere := NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t
  let e := NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t
  have hfiltered := M.input.capToOne_boundary_sub_mem_next_of_same_dividedTarget
    sphere s (n + 2) n c d hdivided
  obtain ⟨y', hy'⟩ := hfiltered
  have hAF : (M.input.boundaryTarget 1).AFGe
      (((e.inv ≫ M.input.capQuotientClass sphere s (n + 2) (n + 1) c ≫
          XModLambdaN.toOne ((nu S Syn).obj X) n) ≫
            lambdaBocksteinConnecting ((nu S Syn).obj X)) -
        ((e.inv ≫ M.input.capQuotientClass sphere s (n + 2) (n + 1) d ≫
          XModLambdaN.toOne ((nu S Syn).obj X) n) ≫
            lambdaBocksteinConnecting ((nu S Syn).obj X)))
      (s + (n + 2) + 1) := by
    refine ⟨e.inv ≫ y', ?_⟩
    change (e.inv ≫ y') ≫ (M.input.boundaryTarget 1).toBase
      (s + (n + 2) + 1) = _
    change y' ≫ (M.input.boundaryTarget 1).toBase
      (s + (n + 2) + 1) = _ at hy'
    rw [Category.assoc]
    rw [hy', Preadditive.comp_sub]
    simp only [Category.assoc]
  have h := (M.boundaryTarget_afGe_iff_synAdamsFiltration 1
    (s + (n + 2) + 1) (t - (s : ℤ)) t _).mp hAF
  simpa [NuSynAdamsGeometricModel.SourceSphere] using h

/-- Every Adams source class is sent to a Bockstein source represented by
one actual cap, and the Bockstein differential is the boundary of that same
cap. -/
theorem exists_cap_differential_for_synAdamsClass
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ) ((s : ℤ), t, t)) :
    let E := canonicalLambdaPowerBocksteinESS ((nu S Syn).obj X) 1
      (t - (s : ℤ), t)
    let T := AddCommGrpCat.of ℤ
    ∃ (c : M.input.CapRepresentatives
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1))
      (y : T ⟶
        (E.ssData (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))).V)
      (yPage : T ⟶ E.Page ((n + 2 : ℕ) : ℤ)
        (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))),
      M.capQuotientDetectedClass s (n + 2) (by omega) t c = x ∧
      (C.capBocksteinSourcePage s n t c).hom 1 =
        C.synAdamsToLambdaBocksteinPageHom s n t x ∧
      C.capBocksteinSourcePage s n t c ≫
          E.d ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) = yPage ∧
      ElementPageRel E ((n + 2 : ℕ) : ℤ)
        (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ)) y yPage := by
  dsimp only
  obtain ⟨c, hc⟩ := C.exists_cap_detecting_synAdamsClass s n t x
  obtain ⟨y, yPage, hd, hy⟩ := C.capBocksteinSourcePage_differential s n t c
  have hsource := C.synAdamsToLambdaBocksteinPageHom_cap s n t c
  rw [hc] at hsource
  exact ⟨c, y, yPage, hc, hsource.symm, hd, hy⟩

/-- The cap-defined comparison from the synthetic Adams page to the
lambda-Bockstein page is injective. -/
theorem synAdamsToLambdaBocksteinPageHom_injective
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ) :
    Function.Injective (C.synAdamsToLambdaBocksteinPageHom s n t) := by
  intro x y hxy
  rw [← sub_eq_zero]
  let z := x - y
  have hzMap : C.synAdamsToLambdaBocksteinPageHom s n t z = 0 := by
    dsimp only [z]
    rw [map_sub, hxy, sub_self]
  obtain ⟨c, hc⟩ := C.exists_cap_detecting_synAdamsClass s n t z
  have hvalue : C.capToBocksteinSourcePageHom s n t c = 0 := by
    rw [← C.synAdamsToLambdaBocksteinPageHom_cap s n t c, hc, hzMap]
  have hpage : C.capBocksteinSourcePage s n t c = 0 := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro m
    change ℤ at m
    calc
      (C.capBocksteinSourcePage s n t c).hom m =
          m • (C.capBocksteinSourcePage s n t c).hom 1 := by
        rw [← map_zsmul]
        simp
      _ = m • C.capToBocksteinSourcePageHom s n t c := rfl
      _ = 0 := by rw [hvalue, smul_zero]
      _ = (0 : AddCommGrpCat.of ℤ ⟶
          (canonicalLambdaPowerBocksteinESS ((nu S Syn).obj X) 1
            (t - (s : ℤ), t)).Page ((n + 2 : ℕ) : ℤ)
              ((s : ℤ), 1)).hom m := rfl
  have haNext :=
    LambdaBocksteinSourcePageRep.mem_next_of_eq_zero (Syn := Syn)
      (C.capBocksteinSourcePage_spec s n t c) hpage
  let qPower :=
    (NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t).inv ≫
      M.input.capQuotientClass
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1) c
  let qFiltered : synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) (n + 1))
      (t - (s : ℤ)) t (s : ℤ) :=
    ⟨qPower, M.capQuotientClass_canonical_mem_filtration
      s (n + 2) (n + 1) t c⟩
  have hqNext : qPower ∈ synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) (n + 1))
      (t - (s : ℤ)) t ((s : ℤ) + 1) := by
    apply lambdaPowerToOne_reflects_generator_next_filtration
      (S := S) (Syn := Syn) X n s t qFiltered
    simpa only [qFiltered, qPower] using haNext
  have hdetZero :
      nuModLambdaPredGeneratorDetection S Syn X (n + 2) (by omega)
        (s : ℤ) t qFiltered = 0 :=
    (nuModLambdaPredGeneratorDetection_eq_zero_iff
      S Syn X (n + 2) (by omega) (s : ℤ) t qFiltered).mpr hqNext
  have hz : z = 0 := by
    rw [← hc]
    change nuModLambdaPredGeneratorDetection S Syn X (n + 2) (by omega)
      (s : ℤ) t qFiltered = 0
    exact hdetZero
  exact hz

/-- The remaining geometric lifting statement sufficient for surjectivity:
every actual representative of a Bockstein source class is, modulo the next
filtration layer, the restriction of a cap in the finite lambda quotient. -/
def CapLiftsBocksteinSourceClasses
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ) : Prop :=
  ∀ (xPage : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS ((nu S Syn).obj X) 1
        (t - (s : ℤ), t)).Page ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1))
    (a : Smn (Syn := Syn) (t - (s : ℤ)) t ⟶
      XModLambdaN ((nu S Syn).obj X) 1),
    LambdaBocksteinSourcePageRep (Syn := Syn) ((nu S Syn).obj X)
        (t - (s : ℤ), t) ((n + 2 : ℕ) : ℤ) (s : ℤ) a xPage →
      ∃ c : M.input.CapRepresentatives
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s (n + 2) (n + 1),
        a - (((NuSynAdamsGeometricModel.sourceSphereIso
            (Syn := Syn) s t).inv ≫
              M.input.capQuotientClass
                (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
                s (n + 2) (n + 1) c) ≫
              XModLambdaN.toOne ((nu S Syn).obj X) n) ∈
          synAdamsFiltration Syn
            (XModLambdaN ((nu S Syn).obj X) 1)
            (t - (s : ℤ)) t ((s : ℤ) + 1)

/-- Once the geometric cap-lifting statement holds, the cap-defined
Adams-to-Bockstein comparison is surjective. -/
theorem synAdamsToLambdaBocksteinPageHom_surjective
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (hcap : C.CapLiftsBocksteinSourceClasses s n t) :
    Function.Surjective (C.synAdamsToLambdaBocksteinPageHom s n t) := by
  intro z
  let xPage : AddCommGrpCat.of ℤ ⟶
      (canonicalLambdaPowerBocksteinESS ((nu S Syn).obj X) 1
        (t - (s : ℤ), t)).Page ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) :=
    AddCommGrpCat.ofHom
      { toFun := fun m => m • z
        map_zero' := zero_zsmul z
        map_add' := fun p q => add_zsmul z p q }
  obtain ⟨a, ha⟩ := LambdaBocksteinSourcePageRep.exists_of_page
    (Syn := Syn) xPage
  obtain ⟨c, hc⟩ := hcap xPage a ha
  have hpage : xPage = C.capBocksteinSourcePage s n t c :=
    LambdaBocksteinSourcePageRep.eq_of_sub_mem_next (Syn := Syn)
      ha (C.capBocksteinSourcePage_spec s n t c) hc
  refine ⟨M.capQuotientDetectedClass s (n + 2) (by omega) t c, ?_⟩
  rw [C.synAdamsToLambdaBocksteinPageHom_cap s n t c]
  change (C.capBocksteinSourcePage s n t c).hom 1 = z
  rw [← hpage]
  simp [xPage]

/-- Surjectivity is equivalent to the concrete cap-lifting statement; no
extra convergence or boundedness condition is hidden in the reduction. -/
theorem capLiftsBocksteinSourceClasses_iff_surjective
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ) :
    C.CapLiftsBocksteinSourceClasses s n t ↔
      Function.Surjective (C.synAdamsToLambdaBocksteinPageHom s n t) := by
  constructor
  · exact C.synAdamsToLambdaBocksteinPageHom_surjective s n t
  · intro hsurj xPage a ha
    obtain ⟨x, hx⟩ := hsurj (xPage.hom 1)
    obtain ⟨c, hc⟩ := C.exists_cap_detecting_synAdamsClass s n t x
    have hone : (C.capBocksteinSourcePage s n t c).hom 1 = xPage.hom 1 := by
      calc
        (C.capBocksteinSourcePage s n t c).hom 1 =
            C.capToBocksteinSourcePageHom s n t c := rfl
        _ = C.synAdamsToLambdaBocksteinPageHom s n t
              (M.capQuotientDetectedClass s (n + 2) (by omega) t c) :=
          (C.synAdamsToLambdaBocksteinPageHom_cap s n t c).symm
        _ = C.synAdamsToLambdaBocksteinPageHom s n t x := by rw [hc]
        _ = xPage.hom 1 := hx
    have hpage : xPage = C.capBocksteinSourcePage s n t c := by
      apply AddCommGrpCat.int_hom_ext
      exact hone.symm
    refine ⟨c, ?_⟩
    apply LambdaBocksteinSourcePageRep.mem_next_of_eq_zero (Syn := Syn)
      (LambdaBocksteinSourcePageRep.sub (Syn := Syn)
        ha (C.capBocksteinSourcePage_spec s n t c))
    rw [hpage, sub_self]

/-- Page equivalence obtained from the proved injectivity and the geometric
cap-lifting statement. -/
noncomputable def synAdamsLambdaBocksteinPageEquiv
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (hcap : C.CapLiftsBocksteinSourceClasses s n t) :
    (SynAdamsSS Syn ((nu S Syn).obj X)).Page ((n + 2 : ℕ) : ℤ)
        ((s : ℤ), t, t) ≃+
      (canonicalLambdaPowerBocksteinESS ((nu S Syn).obj X) 1
        (t - (s : ℤ), t)).Page ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) :=
  AddEquiv.ofBijective (C.synAdamsToLambdaBocksteinPageHom s n t)
    ⟨C.synAdamsToLambdaBocksteinPageHom_injective s n t,
      C.synAdamsToLambdaBocksteinPageHom_surjective s n t hcap⟩

/-- A cap relation represents the zero source class and zero differential
target on the canonical lambda-Bockstein page.  Thus the cap-to-Bockstein
construction has the required kernel compatibility for passage to
`CapPage`. -/
theorem exists_canonicalLambdaBockstein_page_zero_of_capRelation
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (c : M.input.CapRepresentatives
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (n + 1))
    (hc : c ∈ M.input.capRelations
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) (by omega) (n + 1)) :
    let degree : ℤ × ℤ := (t - (s : ℤ), t)
    let E := canonicalLambdaPowerBocksteinESS
      ((nu S Syn).obj X) 1 degree
    let T := AddCommGrpCat.of ℤ
    ∃ (x : T ⟶ (E.ssData ((s : ℤ), 1)).V)
      (y : T ⟶
        (E.ssData (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))).V)
      (xPage : T ⟶ E.Page ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1))
      (yPage : T ⟶ E.Page ((n + 2 : ℕ) : ℤ)
        (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))),
      x = 0 ∧ xPage = 0 ∧ yPage = 0 ∧
      xPage ≫ E.d ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) = yPage ∧
      ElementPageRel E ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) x xPage ∧
      ElementPageRel E ((n + 2 : ℕ) : ℤ)
        (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ)) y yPage := by
  dsimp only
  let qPower :=
    (NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t).inv ≫
      M.input.capQuotientClass
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (n + 1) c
  let aOne := qPower ≫ XModLambdaN.toOne ((nu S Syn).obj X) n
  have hoccurs := M.canonicalLambdaBocksteinOccursOn_of_cap s n t c
  have haNext : aOne ∈ synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) 1)
      (t - (s : ℤ)) t ((s : ℤ) + 1) := by
    simpa only [aOne, qPower, Nat.cast_add, Nat.cast_one] using
      C.capToOne_mem_next_filtration_of_relation s n t c hc
  exact LambdaBocksteinOccursOn.exists_page_differential_eq_zero
    (Syn := Syn) hoccurs haNext

/-- Literal disk formulation of the geometric-origin axiom.  The relative
map `z` is the stable disk crossing the stages from `s` to `s+r`; its
projection to the source graded piece represents `x`, while its actual
boundary projected to the target graded piece is `y`. -/
theorem differential_eq_iff_relativeDisk
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s r : ℕ) (hr : 2 ≤ r) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      (r : ℤ) ((s : ℤ), t, t))
    (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      (shiftFunctor Syn (1 : ℤ)).obj (M.input.layer (s + r))) :
    C.targetEquiv s r hr t
        ((synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
          (r : ℤ) (s : ℤ) t t).hom x) = QuotientAddGroup.mk y ↔
      ∃ z : M.input.Representative
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t) s r,
        QuotientAddGroup.mk
            (⟨M.input.source
                (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
                s r (by omega) z,
              ⟨z, rfl⟩⟩ :
              M.input.sourceCycles
                (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
                s r (by omega)) =
          C.sourceEquiv s r hr t x ∧
        M.input.target
            (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
            s r z = y := by
  rw [C.differential]
  constructor
  · intro h
    exact M.input.exists_representative_of_pageObstruction
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s r (by omega) (C.sourceEquiv s r hr t x) y h
  · rintro ⟨z, hz, rfl⟩
    rw [← hz]
    exact M.input.pageObstruction_mk
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s r (by omega)
      ⟨M.input.source
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s r (by omega) z, ⟨z, rfl⟩⟩ |>.trans
        (M.input.obstruction_source
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s r (by omega) z)

/-- A page differential is realized by an actual relative disk whose
boundary at stage `s+r` is divisible by the degree-forced power
`lambda^(r-1)`.  The map `yStage` is the divided boundary in the actual
stage, while `y` is its image in the adjacent graded layer and represents
the target page class. -/
theorem exists_relativeDisk_lambdaPow_boundary_of_differential
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s r : ℕ) (hr : 2 ≤ r) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      (r : ℤ) ((s : ℤ), t, t))
    (b : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      (r : ℤ) ((s : ℤ) + (r : ℤ), t + (r : ℤ) - 1, t))
    (hdb : (synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
      (r : ℤ) (s : ℤ) t t).hom x = b) :
    ∃ (z : M.input.Representative
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t) s r)
      (yStage : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (M.input.boundaryTarget (r - 1)).stage (s + r))
      (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).obj
            (M.input.layer (s + r)))),
      QuotientAddGroup.mk
          (⟨M.input.source
              (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
              s r (by omega) z,
            ⟨z, rfl⟩⟩ :
            M.input.sourceCycles
              (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
              s r (by omega)) =
        C.sourceEquiv s r hr t x ∧
      C.targetEquiv s r hr t b =
        QuotientAddGroup.mk
          (y ≫ (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPow (r - 1) (M.input.layer (s + r)))) ∧
      yStage ≫ M.input.dividedLayerProjection (r - 1) (s + r) = y ∧
      z ≫ M.input.boundary s (s + r) (Nat.le_add_right s r) =
        yStage ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (r - 1) (M.input.stage (s + r))) := by
  have hr1 : 1 ≤ r := by omega
  let T := NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t
  let targetClass := C.targetEquiv s r hr t b
  obtain ⟨q, hq⟩ := QuotientAddGroup.mk'_surjective
    (M.input.targetAmbiguity T s r hr1) targetClass
  obtain ⟨y, hy⟩ :=
    (M.freeLayers (s + r)).shiftMulHom_surjective
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ)) (r - 1) (by omega) q
  change y ≫ (shiftFunctor Syn (1 : ℤ)).map
      (lambdaPow (r - 1) (M.input.layer (s + r))) = q at hy
  have htarget : targetClass =
      QuotientAddGroup.mk
        (y ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (r - 1) (M.input.layer (s + r)))) := by
    calc
      targetClass = QuotientAddGroup.mk q := hq.symm
      _ = QuotientAddGroup.mk
          (y ≫ (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPow (r - 1) (M.input.layer (s + r)))) :=
        congrArg QuotientAddGroup.mk hy.symm
  have hxy : M.input.pageObstruction T s r hr1
      (C.sourceEquiv s r hr t x) =
        QuotientAddGroup.mk
          (y ≫ (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPow (r - 1) (M.input.layer (s + r)))) := by
    calc
      M.input.pageObstruction T s r hr1
          (C.sourceEquiv s r hr t x) =
          C.targetEquiv s r hr t
            ((synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
              (r : ℤ) (s : ℤ) t t).hom x) :=
        (C.differential s r hr t x).symm
      _ = C.targetEquiv s r hr t b := congrArg _ hdb
      _ = targetClass := rfl
      _ = QuotientAddGroup.mk
          (y ≫ (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPow (r - 1) (M.input.layer (s + r)))) := htarget
  obtain ⟨z, yStage, hz, hyStage, hboundary⟩ :=
    GeometricAdams.Deferred.correctedBoundary
      M.input M.freeLayers M.realization s r hr (t - (s : ℤ))
        (C.sourceEquiv s r hr t x) y hxy
  exact ⟨z, yStage, y, hz, htarget, hyStage, hboundary⟩

/-- Cap the relative disk supplied by a page differential along its
`lambda^(r-1)`-divisible boundary.  The map `c` lands in the common cone:
its relative-disk face is exactly `z`, while its cone face is exactly the
chosen divided boundary `yStage`.  Its image `q` in the lambda cofiber has
the corresponding connecting boundary. -/
theorem exists_cappedRelativeDisk_of_differential
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s r : ℕ) (hr : 2 ≤ r) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      (r : ℤ) ((s : ℤ), t, t))
    (b : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      (r : ℤ) ((s : ℤ) + (r : ℤ), t + (r : ℤ) - 1, t))
    (hdb : (synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
      (r : ℤ) (s : ℤ) t t).hom x = b) :
    ∃ (z : M.input.Representative
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t) s r)
      (yStage : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (M.input.boundaryTarget (r - 1)).stage (s + r))
      (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).obj
            (M.input.layer (s + r))))
      (c : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        LambdaCofiberGeometry.commonCone
          (M.input.transition s (s + r) (Nat.le_add_right s r)) (r - 1))
      (q : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        XModLambdaN (M.input.stage s) (r - 1)),
      QuotientAddGroup.mk
          (⟨M.input.source
              (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
              s r (by omega) z,
            ⟨z, rfl⟩⟩ :
            M.input.sourceCycles
              (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
              s r (by omega)) =
        C.sourceEquiv s r hr t x ∧
      C.targetEquiv s r hr t b =
        QuotientAddGroup.mk
          (y ≫ (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPow (r - 1) (M.input.layer (s + r)))) ∧
      yStage ≫ M.input.dividedLayerProjection (r - 1) (s + r) = y ∧
      c ≫ LambdaCofiberGeometry.toRelative
          (M.input.transition s (s + r) (Nat.le_add_right s r)) (r - 1) = z ∧
      c ≫ LambdaCofiberGeometry.toQuotient
          (M.input.transition s (s + r) (Nat.le_add_right s r)) (r - 1) = q ∧
      c ≫ syn_functorial_cofiber.cofibδ
          (lambdaPow (r - 1) (M.input.stage (s + r)) ≫
            M.input.transition s (s + r) (Nat.le_add_right s r)) = yStage ∧
      q ≫ syn_functorial_cofiber.cofibδ
          (lambdaPow (r - 1) (M.input.stage s)) =
        yStage ≫ (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).map
            (M.input.transition s (s + r) (Nat.le_add_right s r))) := by
  obtain ⟨z, yStage, y, hz, htarget, hy, hboundary⟩ :=
    C.exists_relativeDisk_lambdaPow_boundary_of_differential
      s r hr t x b hdb
  obtain ⟨c, q, hc, hq, hcone, hqboundary⟩ :=
    LambdaCofiberGeometry.exists_cap_of_relative_boundary
      (M.input.transition s (s + r) (Nat.le_add_right s r))
      (r - 1) z yStage hboundary
  exact ⟨z, yStage, y, c, q, hz, htarget, hy, hc, hq, hcone, hqboundary⟩

/-- The capped disk gives the promised lambda-Bockstein representative.
Its class in the cofiber of `lambda^(r-1)` restricts to a class `aOne` in
the cofiber of `lambda`; the actual lambda connecting map sends `aOne` to
`bOne`.  The source cap represents `x`, while the divided target represents
`b`, and the two filtration statements place `aOne` and `bOne` in the
corresponding Adams layers. -/
theorem exists_lambdaCofiber_restriction_boundary_of_differential
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ) ((s : ℤ), t, t))
    (b : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ)
        ((s : ℤ) + ((n + 2 : ℕ) : ℤ),
          t + ((n + 2 : ℕ) : ℤ) - 1, t))
    (hdb : (synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
      ((n + 2 : ℕ) : ℤ) (s : ℤ) t t).hom x = b) :
    ∃ (z : M.input.Representative
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t) s (n + 2))
      (yStage : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (M.input.boundaryTarget (n + 1)).stage (s + (n + 2)))
      (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).obj
            (M.input.layer (s + (n + 2)))))
      (c : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        LambdaCofiberGeometry.commonCone
          (M.input.transition s (s + (n + 2)) (Nat.le_add_right s (n + 2)))
          (n + 1))
      (qPower : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        XModLambdaN ((nu S Syn).obj X) (n + 1))
      (aOne : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        XModLambdaN ((nu S Syn).obj X) 1)
      (bOne : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj
            ((nu S Syn).obj X))),
      QuotientAddGroup.mk
          (⟨M.input.source
              (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
              s (n + 2) (by omega) z,
            ⟨z, rfl⟩⟩ :
            M.input.sourceCycles
              (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
              s (n + 2) (by omega)) =
        C.sourceEquiv s (n + 2) (by omega) t x ∧
      C.targetEquiv s (n + 2) (by omega) t b =
        QuotientAddGroup.mk
          (y ≫ (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPow (n + 1) (M.input.layer (s + (n + 2))))) ∧
      yStage ≫ M.input.dividedLayerProjection (n + 1) (s + (n + 2)) = y ∧
      c ≫ LambdaCofiberGeometry.toRelative
          (M.input.transition s (s + (n + 2)) (Nat.le_add_right s (n + 2)))
          (n + 1) = z ∧
      (c ≫ LambdaCofiberGeometry.toQuotient
          (M.input.transition s (s + (n + 2)) (Nat.le_add_right s (n + 2)))
          (n + 1)) ≫
        XModLambdaN.map (M.input.toBase s) (n + 1) = qPower ∧
      qPower ≫ XModLambdaN.toOne ((nu S Syn).obj X) n = aOne ∧
      aOne ≫ lambdaBocksteinConnecting ((nu S Syn).obj X) = bOne ∧
      bOne =
        (yStage ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPowerToOne (M.input.stage (s + (n + 2))) n)) ≫
            (M.input.boundaryTarget 1).toBase (s + (n + 2)) ∧
      (M.input.quotient 1).AFGe aOne s ∧
      (M.input.boundaryTarget 1).AFGe bOne (s + (n + 2)) := by
  obtain ⟨z, yStage, y, hz, htarget, hy, hboundary⟩ :=
    C.exists_relativeDisk_lambdaPow_boundary_of_differential
      s (n + 2) (by omega) t x b hdb
  obtain ⟨c, aOne, hc, haOne, hAFa, hboundaryOne, hAFb⟩ :=
    M.input.exists_singleCap
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
      s (n + 2) n z yStage hboundary
  let qPower :=
    (c ≫ LambdaCofiberGeometry.toQuotient
      (M.input.transition s (s + (n + 2)) (Nat.le_add_right s (n + 2)))
      (n + 1)) ≫
        XModLambdaN.map (M.input.toBase s) (n + 1)
  let bOne := aOne ≫ lambdaBocksteinConnecting ((nu S Syn).obj X)
  refine ⟨z, yStage, y, c, qPower, aOne, bOne,
    hz, htarget, hy, hc, rfl, ?_, rfl, ?_, hAFa, ?_⟩
  · exact haOne
  · exact hboundaryOne
  · exact hAFb

/-- A synthetic Adams differential of length `n+2` produces the corresponding
`lambda`-Bockstein differential of length `n+2`.  The first two equalities
retain the geometric identifications with the named Adams source `x` and
target `b`; the last assertion is the differential relation in the canonical
boundary ESS on the actual quotient class and its actual lambda boundary. -/
theorem lambdaBocksteinOccursOn_of_adams_differential
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ) ((s : ℤ), t, t))
    (b : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ)
        ((s : ℤ) + ((n + 2 : ℕ) : ℤ),
          t + ((n + 2 : ℕ) : ℤ) - 1, t))
    (hdb : (synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
      ((n + 2 : ℕ) : ℤ) (s : ℤ) t t).hom x = b) :
    ∃ (z : M.input.Representative
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t) s (n + 2))
      (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).obj
            (M.input.layer (s + (n + 2)))))
      (aOne : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        XModLambdaN ((nu S Syn).obj X) 1)
      (bOne : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj
            ((nu S Syn).obj X))),
      QuotientAddGroup.mk
          (⟨M.input.source
              (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
              s (n + 2) (by omega) z,
            ⟨z, rfl⟩⟩ :
            M.input.sourceCycles
              (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
              s (n + 2) (by omega)) =
        C.sourceEquiv s (n + 2) (by omega) t x ∧
      C.targetEquiv s (n + 2) (by omega) t b =
        QuotientAddGroup.mk
          (y ≫ (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPow (n + 1) (M.input.layer (s + (n + 2))))) ∧
      aOne ≫ lambdaBocksteinConnecting ((nu S Syn).obj X) = bOne ∧
      LambdaBocksteinOccursOn (Syn := Syn) ((nu S Syn).obj X)
        (t - (s : ℤ), t - (s : ℤ) + (s : ℤ))
        ((n + 2 : ℕ) : ℤ) (s : ℤ) aOne bOne := by
  obtain ⟨z, yStage, y, c, qPower, aOne, bOne,
      hsource, htarget, hyStage, hc, hqPower, haOne,
      hboundary, hbOne, hAFa, hAFb⟩ :=
    C.exists_lambdaCofiber_restriction_boundary_of_differential
      s n t x b hdb
  have ha : aOne ∈ synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) 1)
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ)) (s : ℤ) :=
    (M.quotient_afGe_iff_synAdamsFiltration 1 s
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ)) aOne).mp hAFa
  have hb : bOne ∈ synAdamsFiltration Syn
      ((shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj
          ((nu S Syn).obj X)))
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ))
      (((s + (n + 2) : ℕ) : ℤ)) :=
    (M.boundaryTarget_afGe_iff_synAdamsFiltration 1 (s + (n + 2))
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ)) bOne).mp hAFb
  have hb' : bOne ∈ synAdamsFiltration Syn
      ((shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj
          ((nu S Syn).obj X)))
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ))
      ((s : ℤ) + ((n + 2 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hb
  have hoccurs := lambdaBocksteinOccursOn_of_filtered_boundary
    (Syn := Syn) ((nu S Syn).obj X)
    (t - (s : ℤ), t - (s : ℤ) + (s : ℤ))
    ((n + 2 : ℕ) : ℤ) (s : ℤ) (by omega)
    aOne bOne ha hb' hboundary
  exact ⟨z, y, aOne, bOne, hsource, htarget, hboundary, hoccurs⟩

/-- Page-level form of the Adams-to-Bockstein comparison.  A declared
synthetic Adams `d_(n+2)` produces actual classes on the corresponding
lambda-Bockstein page, and the lambda-Bockstein page differential carries
the constructed source class to the constructed target class. -/
theorem exists_lambdaBockstein_page_differential_of_adams_differential
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ) ((s : ℤ), t, t))
    (b : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ)
        ((s : ℤ) + ((n + 2 : ℕ) : ℤ),
          t + ((n + 2 : ℕ) : ℤ) - 1, t))
    (hdb : (synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
      ((n + 2 : ℕ) : ℤ) (s : ℤ) t t).hom x = b) :
    let degree : ℤ × ℤ :=
      (t - (s : ℤ), t - (s : ℤ) + (s : ℤ))
    let E := canonicalLambdaPowerBocksteinESS
      ((nu S Syn).obj X) 1 degree
    let T := AddCommGrpCat.of ℤ
    ∃ (aOne : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
          XModLambdaN ((nu S Syn).obj X) 1)
      (bOne : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj
            ((nu S Syn).obj X)))
      (xAmbient : T ⟶ (E.ssData ((s : ℤ), 1)).V)
      (yAmbient : T ⟶
        (E.ssData (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))).V)
      (xPage : T ⟶ E.Page ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1))
      (yPage : T ⟶ E.Page ((n + 2 : ℕ) : ℤ)
        (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))),
      aOne ≫ lambdaBocksteinConnecting ((nu S Syn).obj X) = bOne ∧
      xPage ≫ E.d ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1) = yPage ∧
      ElementPageRel E ((n + 2 : ℕ) : ℤ) ((s : ℤ), 1)
        xAmbient xPage ∧
      ElementPageRel E ((n + 2 : ℕ) : ℤ)
        (((s : ℤ), 1) + E.diffDeg ((n + 2 : ℕ) : ℤ))
        yAmbient yPage := by
  dsimp only
  obtain ⟨z, y, aOne, bOne, hsource, htarget, hboundary, hoccurs⟩ :=
    C.lambdaBocksteinOccursOn_of_adams_differential s n t x b hdb
  obtain ⟨xAmbient, yAmbient, xPage, yPage, hd, hxPage, hyPage⟩ :=
    hoccurs.exists_page_differential
  exact ⟨aOne, bOne, xAmbient, yAmbient, xPage, yPage,
    hboundary, hd, hxPage, hyPage⟩

/-- Geometric characterization of the original synthetic Adams differential:
after identifying its target with the actual adjacent-layer quotient, the
differential is `lambda^(r-1)` times `y` exactly when the source and divided
target are represented by one cap over the Adams tower. -/
theorem differential_eq_lambdaPow_iff_cap
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s r : ℕ) (hr : 2 ≤ r) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      (r : ℤ) ((s : ℤ), t, t))
    (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).obj
          (M.input.layer (s + r)))) :
    C.targetEquiv s r hr t
        ((synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
          (r : ℤ) (s : ℤ) t t).hom x) =
      QuotientAddGroup.mk
        (y ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (r - 1) (M.input.layer (s + r)))) ↔
      M.input.CapRealizes
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s r (by omega) (r - 1) (C.sourceEquiv s r hr t x) y := by
  rw [C.differential]
  exact (M.input.capRealizes_iff_pageObstruction M.freeLayers M.realization
    s r hr (t - (s : ℤ)) (C.sourceEquiv s r hr t x) y).symm

/-- The same geometric characterization detects essential differentials:
the cap target must remain nonzero modulo all shorter incoming boundaries. -/
theorem essential_differential_iff_cap
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s r : ℕ) (hr : 2 ≤ r) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      (r : ℤ) ((s : ℤ), t, t))
    (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).obj
          (M.input.layer (s + r)))) :
    (C.targetEquiv s r hr t
          ((synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
            (r : ℤ) (s : ℤ) t t).hom x) =
        QuotientAddGroup.mk
          (y ≫ (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPow (r - 1) (M.input.layer (s + r)))) ∧
      (synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
        (r : ℤ) (s : ℤ) t t).hom x ≠ 0) ↔
      (M.input.CapRealizes
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s r (by omega) (r - 1) (C.sourceEquiv s r hr t x) y ∧
        y ≫ (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPow (r - 1) (M.input.layer (s + r))) ∉
          M.input.suspendedBoundaries
            (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
            (s + 1) (s + r) (by omega)) := by
  have hne :
      (synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
          (r : ℤ) (s : ℤ) t t).hom x ≠ 0 ↔
        M.input.pageObstruction
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s r (by omega) (C.sourceEquiv s r hr t x) ≠ 0 := by
    rw [← C.differential]
    exact (C.targetEquiv s r hr t).map_ne_zero_iff.symm
  rw [C.differential, hne]
  exact M.input.essential_cap_iff M.freeLayers M.realization
    s r hr (t - (s : ℤ)) (C.sourceEquiv s r hr t x) y

/-- A declared Adams differential therefore produces the actual cap whose
single-lambda boundary is used by the lambda-Bockstein construction. The
remaining power on the target is `lambda^n` for a differential of length
`n+2`. -/
theorem exists_singleLambdaBoundary_of_differential
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ) ((s : ℤ), t, t))
    (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).obj
          (M.input.layer (s + (n + 2)))))
    (hxy : C.targetEquiv s (n + 2) (by omega) t
        ((synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
          ((n + 2 : ℕ) : ℤ) (s : ℤ) t t).hom x) =
      QuotientAddGroup.mk
        (y ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (n + 1) (M.input.layer (s + (n + 2)))))) :
    ∃ (c : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        LambdaCofiberGeometry.commonCone
          (M.input.transition s (s + (n + 2))
            (Nat.le_add_right s (n + 2))) (n + 1))
      (y' : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (M.input.boundaryTarget (n + 1)).stage (s + (n + 2)))
      (w : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        XModLambdaN ((nu S Syn).obj X) 1),
      M.input.capSourceClass
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s (n + 2) (by omega) (n + 1) c =
        C.sourceEquiv s (n + 2) (by omega) t x ∧
      (((c ≫ LambdaCofiberGeometry.toQuotient
          (M.input.transition s (s + (n + 2))
            (Nat.le_add_right s (n + 2))) (n + 1)) ≫
            XModLambdaN.map (M.input.toBase s) (n + 1)) ≫
          XModLambdaN.toOne ((nu S Syn).obj X) n) = w ∧
      y' ≫ M.input.dividedLayerProjection (n + 1) (s + (n + 2)) = y ∧
      (M.input.quotient 1).AFGe w s ∧
      w ≫ lambdaBocksteinConnecting ((nu S Syn).obj X) =
        (y' ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPowerToOne (M.input.stage (s + (n + 2))) n)) ≫
            (M.input.boundaryTarget 1).toBase (s + (n + 2)) ∧
      (M.input.boundaryTarget 1).AFGe
        (w ≫ lambdaBocksteinConnecting ((nu S Syn).obj X))
          (s + (n + 2)) := by
  have hpage : M.input.pageObstruction
      (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (by omega)
        (C.sourceEquiv s (n + 2) (by omega) t x) =
      QuotientAddGroup.mk
        (y ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (n + 1) (M.input.layer (s + (n + 2))))) := by
    rw [← C.differential]
    exact hxy
  exact M.input.exists_singleBoundary_of_pageObstruction
    M.freeLayers M.realization s n (t - (s : ℤ))
      (C.sourceEquiv s (n + 2) (by omega) t x) y hpage

/-- A concrete single-lambda boundary produced from a cap. Its source
represents the named Adams page class, and its boundary is the named divided
target with the remaining lambda power. -/
def SingleLambdaBoundaryWitness
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ) ((s : ℤ), t, t))
    (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).obj
          (M.input.layer (s + (n + 2))))) : Prop :=
  ∃ (c : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      LambdaCofiberGeometry.commonCone
        (M.input.transition s (s + (n + 2))
          (Nat.le_add_right s (n + 2))) (n + 1))
    (y' : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      (M.input.boundaryTarget (n + 1)).stage (s + (n + 2)))
    (w : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      XModLambdaN ((nu S Syn).obj X) 1),
    M.input.capSourceClass
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
        s (n + 2) (by omega) (n + 1) c =
      C.sourceEquiv s (n + 2) (by omega) t x ∧
    (((c ≫ LambdaCofiberGeometry.toQuotient
        (M.input.transition s (s + (n + 2))
          (Nat.le_add_right s (n + 2))) (n + 1)) ≫
          XModLambdaN.map (M.input.toBase s) (n + 1)) ≫
        XModLambdaN.toOne ((nu S Syn).obj X) n) = w ∧
    y' ≫ M.input.dividedLayerProjection (n + 1) (s + (n + 2)) = y ∧
    (M.input.quotient 1).AFGe w s ∧
    w ≫ lambdaBocksteinConnecting ((nu S Syn).obj X) =
      (y' ≫ (shiftFunctor Syn (1 : ℤ)).map
        (lambdaPowerToOne (M.input.stage (s + (n + 2))) n)) ≫
          (M.input.boundaryTarget 1).toBase (s + (n + 2)) ∧
    (M.input.boundaryTarget 1).AFGe
      (w ≫ lambdaBocksteinConnecting ((nu S Syn).obj X)) (s + (n + 2))

/-- Complete geometric boundary formula. The original Adams differential is
equivalent to the existence of its cap together with the actual boundary in
`nu X / lambda`; that boundary carries precisely the remaining `lambda^n`. -/
theorem differential_iff_singleLambdaBoundary
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ) ((s : ℤ), t, t))
    (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).obj
          (M.input.layer (s + (n + 2))))) :
    C.targetEquiv s (n + 2) (by omega) t
        ((synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
          ((n + 2 : ℕ) : ℤ) (s : ℤ) t t).hom x) =
      QuotientAddGroup.mk
        (y ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (n + 1) (M.input.layer (s + (n + 2))))) ↔
      (M.input.CapRealizes
          (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s (n + 2) (by omega) (n + 1)
            (C.sourceEquiv s (n + 2) (by omega) t x) y ∧
        SingleLambdaBoundaryWitness C s n t x y) := by
  constructor
  · intro hxy
    refine ⟨(C.differential_eq_lambdaPow_iff_cap
      s (n + 2) (by omega) t x y).mp hxy, ?_⟩
    exact C.exists_singleLambdaBoundary_of_differential s n t x y hxy
  · rintro ⟨hcap, _⟩
    exact (C.differential_eq_lambdaPow_iff_cap
      s (n + 2) (by omega) t x y).mpr hcap

/-- The same boundary witness, now stated in the canonical Adams filtrations
used by the extension spectral sequence. -/
def CanonicalLambdaBoundaryWitness
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ) ((s : ℤ), t, t))
    (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).obj
          (M.input.layer (s + (n + 2))))) : Prop :=
  SingleLambdaBoundaryWitness C s n t x y ∧
  ∃ (y' : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      (M.input.boundaryTarget (n + 1)).stage (s + (n + 2)))
    (w : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      XModLambdaN ((nu S Syn).obj X) 1),
    y' ≫ M.input.dividedLayerProjection (n + 1) (s + (n + 2)) = y ∧
    w ∈ synAdamsFiltration Syn (XModLambdaN ((nu S Syn).obj X) 1)
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ)) (s : ℤ) ∧
    w ≫ lambdaBocksteinConnecting ((nu S Syn).obj X) =
      (y' ≫ (shiftFunctor Syn (1 : ℤ)).map
        (lambdaPowerToOne (M.input.stage (s + (n + 2))) n)) ≫
          (M.input.boundaryTarget 1).toBase (s + (n + 2)) ∧
    w ≫ lambdaBocksteinConnecting ((nu S Syn).obj X) ∈
      synAdamsFiltration Syn
        ((shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj
            ((nu S Syn).obj X)))
        (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ))
        ((s + (n + 2) : ℕ) : ℤ)

/-- The geometric Adams differential supplies exactly the canonical filtered
homotopy boundary required by the lambda-Bockstein ESS. -/
theorem canonicalLambdaBoundaryWitness_of_differential
    (C : NuSynAdamsGeometricComparison S Syn X M)
    (s n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu S Syn).obj X)).Page
      ((n + 2 : ℕ) : ℤ) ((s : ℤ), t, t))
    (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).obj
          (M.input.layer (s + (n + 2)))))
    (hxy : C.targetEquiv s (n + 2) (by omega) t
        ((synAdamsDifferentialNormalized Syn ((nu S Syn).obj X)
          ((n + 2 : ℕ) : ℤ) (s : ℤ) t t).hom x) =
      QuotientAddGroup.mk
        (y ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (n + 1) (M.input.layer (s + (n + 2)))))) :
    CanonicalLambdaBoundaryWitness C s n t x y := by
  obtain ⟨c, y', w, hsource, hwdef, hy, hw, hb, hbf⟩ :=
    C.exists_singleLambdaBoundary_of_differential s n t x y hxy
  refine ⟨⟨c, y', w, hsource, hwdef, hy, hw, hb, hbf⟩,
    y', w, hy, ?_, hb, ?_⟩
  · exact (M.quotient_afGe_iff_synAdamsFiltration 1 s
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ)) w).mp hw
  · exact (M.boundaryTarget_afGe_iff_synAdamsFiltration 1 (s + (n + 2))
      (t - (s : ℤ)) (t - (s : ℤ) + (s : ℤ))
      (w ≫ lambdaBocksteinConnecting ((nu S Syn).obj X))).mp hbf

end NuSynAdamsGeometricComparison

end KIPBase.Synthetic
