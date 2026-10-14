import KIPBase.Synthetic.LambdaBoundaryNaturality

/-!
# The canonical boundary ESS and actual homotopy representatives

The forward formula already constructed in `ExtensionSS` is upgraded to
an equivalence. Both directions use the canonical ESS, its actual Adams
filtrations, and postcomposition by the actual λ-cofiber boundary. There
are no deferred proofs in this file.
-/

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]

/-- Actual filtered homotopy lifts of two specified ambient ESS classes.
The last equality is postcomposition by the actual finite λ-cofiber boundary. -/
def LambdaPowerBoundaryLifts
    (X : Syn) (n : ℕ) (degree : ℤ × ℤ) (r s : ℤ)
    {T : AddCommGrpCat.{0}}
    (x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X n) degree (s, 1)).V)
    (y : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X n) degree (s + r, 0)).V) : Prop :=
    ∃ (xl : T ⟶ Subobject.underlying.obj
        ((lambdaPowerBocksteinSourceCSS X n).F.F s degree))
      (yl : T ⟶ Subobject.underlying.obj
        ((lambdaPowerBocksteinTargetCSS X n).F.F (s + r) degree)),
      (unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap X n) degree).IsLift
        s 1 xl (x ≫ (unboundedExtensionVComplexIso
          (lambdaPowerBocksteinCSSMap X n) degree s 1).hom) ∧
      (unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap X n) degree).IsLift
        (s + r) 0 yl (y ≫ (unboundedExtensionVComplexIso
          (lambdaPowerBocksteinCSSMap X n) degree (s + r) 0).hom) ∧
      ∀ a : T,
        LambdaPowerBoundary.boundaryHom (Smn degree.1 degree.2) X n
          ((synAdamsConvergence Syn (XModLambdaN X n)).abutmentEquiv degree
            (((lambdaPowerBocksteinSourceCSS X n).F.F s degree).arrow.hom
              (xl.hom a))) =
        (synAdamsConvergence Syn
          ((shiftFunctor Syn (1 : ℤ)).obj
            ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X))).abutmentEquiv degree
          (((lambdaPowerBocksteinTargetCSS X n).F.F (s + r) degree).arrow.hom
            (yl.hom a))

/-- The complete representative formula for a specified differential of
the canonical finite-power λ-boundary ESS. Projectivity is needed only to
lift a generalized element from the quotient page to actual representatives.
In particular there is no boundedness hypothesis. -/
theorem lambdaPowerBockstein_relation_iff_homotopy_boundary
    (X : Syn) (n : ℕ) (degree : ℤ × ℤ) (r : ℤ) (hr : 0 ≤ r) (s : ℤ)
    {T : AddCommGrpCat.{0}} [Projective T]
    {x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X n) degree (s, 1)).V}
    {y : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X n) degree (s + r, 0)).V} :
    DifferentialRelation
      (ExtensionSpectralSequence.{1, 0, 0, 0}
        (lambdaPowerBocksteinCSSMap X n) degree) r (s, 1) x y ↔
      LambdaPowerBoundaryLifts X n degree r s x y := by
  constructor
  · intro h
    have hlifts := unbounded_lift_of_differentialRelation_one.{1, 0, 0, 0}
      (C := AddCommGrpCat.{0})
      (cm := lambdaPowerBocksteinCSSMap X n) (t := degree)
      (r := r) (hr := hr) (s := s)
      (T := T) (x := x) (y := y) h
    rcases hlifts with ⟨xl, yl, hx, hy, hd⟩
    refine ⟨xl, yl, hx, hy, ?_⟩
    have ha := unbounded_lift_ambient_map.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X n) degree s (s + r) (by omega) xl yl hd
    intro a
    have he := ConcreteCategory.congr_hom ha a
    have hnat := (synAdamsFunctoriality Syn).abutment_naturality
      (syn_functorial_cofiber.cofibδ (lambdaPow n X)) degree
      (((lambdaPowerBocksteinSourceCSS X n).F.F s degree).arrow.hom (xl.hom a))
    change _ = _ ≫ syn_functorial_cofiber.cofibδ (lambdaPow n X) at hnat
    change _ ≫ syn_functorial_cofiber.cofibδ (lambdaPow n X) = _
    exact hnat.symm.trans (congrArg
      ((synAdamsConvergence Syn
        ((shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X))).abutmentEquiv degree) he)
  · rintro ⟨xl, yl, hx, hy, hb⟩
    exact lambdaPowerBockstein_relation_of_homotopy_boundary
      X n degree r hr s (s + r) rfl hx hy hb

private theorem zero_relation_iff_boundary
    (E : SpectralSequence AddCommGrpCat.{0} (ℤ × ℤ)) (r : ℤ) (k : ℤ × ℤ)
    {T : AddCommGrpCat.{0}} (y : T ⟶ (E.ssData (k + E.diffDeg r)).V) :
    DifferentialRelation E r k 0 y ↔
      Subobject.Factors ((E.ssData (k + E.diffDeg r)).B
        (↑(r - E.r₀).toNat : WithTop ℕ)) y := by
  constructor
  · intro h
    have hz : DifferentialRelation E r k (0 : T ⟶ _) 0 := by
      exact ⟨0, zero_comp, 0, zero_comp, by simp only [zero_comp]⟩
    simpa only [sub_zero] using h.targets_sub_factors_boundary E r k hz
  · intro h
    let D := E.ssData (k + E.diffDeg r)
    let q : WithTop ℕ := ↑(r - E.r₀).toNat
    let b := (D.B q).factorThru y h
    let i := Subobject.ofLE (D.B q) (D.Z q) (D.B_le_Z q)
    refine ⟨0, zero_comp, b ≫ i, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun f => b ≫ f) (Subobject.ofLE_arrow (D.B_le_Z q))).trans
          ((D.B q).factorThru_arrow y h))
    · change (0 : T ⟶ _) ≫ _ ≫ _ = (b ≫ i) ≫ cokernel.π i
      simp only [zero_comp, Category.assoc, cokernel.condition, comp_zero]

/-- Essentiality has an entirely representative-level test: the specified
classes admit actual boundary lifts, and the same target admits no such
lift with zero source class. Thus a nonzero ambient representative alone
is never mistaken for a nonzero ESS differential. -/
theorem lambdaPowerBockstein_essential_iff_homotopy_boundary
    (X : Syn) (n : ℕ) (degree : ℤ × ℤ) (r : ℤ) (hr : 0 ≤ r) (s : ℤ)
    {T : AddCommGrpCat.{0}} [Projective T]
    {x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X n) degree (s, 1)).V}
    {y : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X n) degree (s + r, 0)).V} :
    EssentialDifferentialRelation
      (ExtensionSpectralSequence.{1, 0, 0, 0}
        (lambdaPowerBocksteinCSSMap X n) degree) r (s, 1) x y ↔
      LambdaPowerBoundaryLifts X n degree r s x y ∧
        ¬ LambdaPowerBoundaryLifts X n degree r s 0 y := by
  unfold EssentialDifferentialRelation
  rw [← zero_relation_iff_boundary,
    lambdaPowerBockstein_relation_iff_homotopy_boundary X n degree r hr s,
    lambdaPowerBockstein_relation_iff_homotopy_boundary X n degree r hr s]

/-- Actual filtered representatives for the finite boundary give actual
filtered representatives for the first boundary, retaining both specified
ambient classes through the canonical restriction map. -/
theorem lambdaBoundaryToOne_lifts (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (r : ℤ) (hr : 0 ≤ r) (s : ℤ)
    {T : AddCommGrpCat.{0}} [Projective T]
    {x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X (n + 1)) degree (s, 1)).V}
    {y : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X (n + 1)) degree (s + r, 0)).V}
    (h : LambdaPowerBoundaryLifts X (n + 1) degree r s x y) :
    LambdaPowerBoundaryLifts X 1 degree r s
      (x ≫ (lambdaBoundaryToOneMorphism X n degree).φ (s, 1))
      (y ≫ (lambdaBoundaryToOneMorphism X n degree).φ (s + r, 0)) := by
  apply (lambdaPowerBockstein_relation_iff_homotopy_boundary X 1 degree r hr s).mp
  exact lambdaBoundaryToOne_relation X n degree r (s, 1)
    ((lambdaPowerBockstein_relation_iff_homotopy_boundary
      X (n + 1) degree r hr s).mpr h)

end KIPBase.Synthetic
