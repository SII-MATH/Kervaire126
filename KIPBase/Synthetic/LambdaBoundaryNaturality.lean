import KIPBase.Synthetic.ESSNaturality

/-!
# The finite-to-single lambda boundary map on the canonical ESS

The actual cofiber restriction square defines a filtered chain map on the
Adams abutments. Its induced morphism acts on the existing canonical ESS,
with its original E-infinity ambient objects and all its cycle/boundary
layers. No boundedness or comparison assumption is added.
-/

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]

/-- The actual restriction square on the two filtered abutment groups. -/
noncomputable def lambdaBoundaryToOneComplexMap (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) :
    FilteredComplexMorphism
      (unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap X (n + 1)) degree)
      (unboundedUnderlyingComplex (lambdaPowerBocksteinCSSMap X 1) degree) :=
  underlyingComplexMorphism
    (lambdaPowerBocksteinCSSMap X (n + 1)).aMap
    (lambdaPowerBocksteinCSSMap X (n + 1)).filtration_compat
    (lambdaPowerBocksteinCSSMap X 1).aMap
    (lambdaPowerBocksteinCSSMap X 1).filtration_compat
    (synAdamsConvergingMap (XModLambdaN.toOne X n)).aMap
    (synAdamsConvergingMap
      ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n))).aMap
    (lambdaPowerBockstein_toOne_abutment_square X n)
    (synAdamsConvergingMap (XModLambdaN.toOne X n)).filtration_compat
    (synAdamsConvergingMap
      ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n))).filtration_compat degree

@[simp] theorem lambdaBoundaryToOneComplexMap_source (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) :
    (lambdaBoundaryToOneComplexMap X n degree).f 1 =
      (synAdamsConvergingMap (XModLambdaN.toOne X n)).aMap degree := by
  simp [lambdaBoundaryToOneComplexMap, underlyingComplexMorphism]

@[simp] theorem lambdaBoundaryToOneComplexMap_target (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) :
    (lambdaBoundaryToOneComplexMap X n degree).f 0 =
      (synAdamsConvergingMap
        ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n))).aMap degree := by
  simp [lambdaBoundaryToOneComplexMap, underlyingComplexMorphism]

/-- In the source column, the graded map is induced by the actual
restriction on Adams abutments. -/
theorem lambdaBoundaryToOneComplexMap_source_graded (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (s : ℤ) :
    (lambdaBoundaryToOneComplexMap X n degree).assocGradedMap s 1 =
      Filtration.inducedAssocGradedMap
        (synAdamsConvergingMap (XModLambdaN.toOne X n)).aMap
        (synAdamsConvergingMap (XModLambdaN.toOne X n)).filtration_compat s degree := by
  apply (cancel_epi (cokernel.π _)).mp
  dsimp only [FilteredComplexMorphism.assocGradedMap, Filtration.inducedAssocGradedMap]
  erw [cokernel.π_desc]

/-- In the target column, the graded map is induced by the suspended
lambda power in the actual cofiber restriction square. -/
theorem lambdaBoundaryToOneComplexMap_target_graded (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (s : ℤ) :
    (lambdaBoundaryToOneComplexMap X n degree).assocGradedMap s 0 =
      Filtration.inducedAssocGradedMap
        (synAdamsConvergingMap
          ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n))).aMap
        (synAdamsConvergingMap
          ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n))).filtration_compat
        s degree := by
  apply (cancel_epi (cokernel.π _)).mp
  dsimp only [FilteredComplexMorphism.assocGradedMap, Filtration.inducedAssocGradedMap]
  erw [cokernel.π_desc]

/-- The map of the actual canonical boundary extension spectral sequences
induced by restriction from the finite lambda quotient to the first quotient. -/
noncomputable def lambdaBoundaryToOneMorphism (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) :
    canonicalLambdaPowerBocksteinESS X (n + 1) degree ⟶
      canonicalLambdaPowerBocksteinESS X 1 degree :=
  ESSNaturality.spectralMap
    (lambdaPowerBocksteinCSSMap X (n + 1)) (lambdaPowerBocksteinCSSMap X 1)
    degree (lambdaBoundaryToOneComplexMap X n degree)

/-- The quotient-induced map on each actual page; the raw ESS page number
is retained. -/
noncomputable def lambdaBoundaryToOnePageMap (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (r : ℤ) (k : ℤ × ℤ) :
    (canonicalLambdaPowerBocksteinESS X (n + 1) degree).Page r k ⟶
      (canonicalLambdaPowerBocksteinESS X 1 degree).Page r k :=
  (lambdaBoundaryToOneMorphism X n degree).toSSDataMorphism.pageMap k (↑(r - 0).toNat)

/-- Naturality of all actual boundary ESS differentials, as an equality
of page maps rather than only of homotopy representatives. -/
theorem lambdaBoundaryToOnePageMap_comm_d (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (r : ℤ) (k : ℤ × ℤ) :
    lambdaBoundaryToOnePageMap X n degree r k ≫
        (canonicalLambdaPowerBocksteinESS X 1 degree).d r k =
      (canonicalLambdaPowerBocksteinESS X (n + 1) degree).d r k ≫
        lambdaBoundaryToOnePageMap X n degree r (k + (r, -1)) := by
  exact ESSNaturality.spectralMap_pageMap_comm_d
    (lambdaPowerBocksteinCSSMap X (n + 1)) (lambdaPowerBocksteinCSSMap X 1)
    degree (lambdaBoundaryToOneComplexMap X n degree) r k

/-- On the source column, the zeroth-page comparison is the
associated-graded map induced by the actual quotient restriction. -/
theorem lambdaBoundaryToOne_e0SourceGraded (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (s : ℤ) :
    lambdaBoundaryToOnePageMap X n degree 0 (s, 1) ≫
        ((canonicalLambdaPowerBocksteinData X 1).e0SourceIsoAssociatedGraded
          s degree).hom =
      ((canonicalLambdaPowerBocksteinData X (n + 1)).e0SourceIsoAssociatedGraded
          s degree).hom ≫
        Filtration.inducedAssocGradedMap
          (synAdamsConvergingMap (XModLambdaN.toOne X n)).aMap
          (synAdamsConvergingMap (XModLambdaN.toOne X n)).filtration_compat
          s degree := by
  have h := ESSNaturality.spectralMap_e0Iso
    (lambdaPowerBocksteinCSSMap X (n + 1)) (lambdaPowerBocksteinCSSMap X 1)
    degree (lambdaBoundaryToOneComplexMap X n degree) s 1
  rw [lambdaBoundaryToOneComplexMap_source_graded] at h
  convert h using 1 <;>
    simp only [lambdaBoundaryToOnePageMap, lambdaBoundaryToOneMorphism,
      canonicalLambdaPowerBocksteinData, syntheticExtensionCoreDataOfMap,
      synAdamsConvergingMap,
      SyntheticExtensionCoreData.e0SourceIsoAssociatedGraded,
      Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  all_goals rfl

private theorem castIso_inv {C : Type*} [Category C]
    {A B B' : C} (e : A ≅ B) (h : B = B')
    (he : (A ≅ B) = (A ≅ B')) :
    (he.mp e).inv = eqToHom h.symm ≫ e.inv := by
  subst B'
  simp

private theorem sourceIso_hom {X Y : Syn} {f : X ⟶ Y}
    (D : SyntheticExtensionCoreData f) (s : ℤ) (degree : ℤ × ℤ)
    (hi : D.sourceConvergence.reindex (syntheticAdamsIndex s degree) =
      (s, degree)) :
    (D.e0SourceIso s degree).hom =
      (D.e0SourceIsoAssociatedGraded s degree).hom ≫
        D.sourceFiltration.transportGraded hi.symm ≫
        (D.sourceConvergence.iso (syntheticAdamsIndex s degree)).inv := by
  simp only [SyntheticExtensionCoreData.e0SourceIso, Iso.trans_hom, Iso.symm_hom]
  apply congrArg (fun z => (D.e0SourceIsoAssociatedGraded s degree).hom ≫ z)
  have hB : D.sourceFiltration.associatedGraded
      (D.sourceConvergence.reindex (syntheticAdamsIndex s degree)).1
      (D.sourceConvergence.reindex (syntheticAdamsIndex s degree)).2 =
      D.sourceFiltration.associatedGraded s degree := by rw [hi]
  have he : (((SynAdamsSS Syn X).ssData
      (syntheticAdamsIndex s degree)).eInfty ≅
        D.sourceFiltration.associatedGraded
          (D.sourceConvergence.reindex (syntheticAdamsIndex s degree)).1
          (D.sourceConvergence.reindex (syntheticAdamsIndex s degree)).2) =
      (((SynAdamsSS Syn X).ssData
        (syntheticAdamsIndex s degree)).eInfty ≅
          D.sourceFiltration.associatedGraded s degree) := by rw [hi]
  exact castIso_inv (D.sourceConvergence.iso (syntheticAdamsIndex s degree)) hB he

private theorem inverse_convergence_square {C : Type*} [Category C] [Abelian C]
    {A B : ℤ × ℤ → C} {F : Filtration A} {G : Filtration B}
    (aMap : ∀ t, A t ⟶ B t)
    (compat : ∀ s t, ∃ a,
      a ≫ (G.F s t).arrow = (F.F s t).arrow ≫ aMap t)
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

/-- The source zeroth-page comparison commutes with the actual Adams
map on limiting pages. -/
theorem lambdaBoundaryToOne_e0Source (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (s : ℤ) :
    lambdaBoundaryToOnePageMap X n degree 0 (s, 1) ≫
        ((canonicalLambdaPowerBocksteinData X 1).e0SourceIso s degree).hom =
      ((canonicalLambdaPowerBocksteinData X (n + 1)).e0SourceIso s degree).hom ≫
        (synAdamsSS_functorial (XModLambdaN.toOne X n)).eInftyMap
          (syntheticAdamsIndex s degree) := by
  let f := synAdamsConvergingMap (XModLambdaN.toOne X n)
  have hs : (canonicalLambdaPowerBocksteinData X (n + 1)).sourceConvergence.reindex
      (syntheticAdamsIndex s degree) = (s, degree) := by
    rw [(canonicalLambdaPowerBocksteinData X (n + 1)).source_reindex,
      syntheticAdamsReindex_index]
  have ht : (canonicalLambdaPowerBocksteinData X 1).sourceConvergence.reindex
      (syntheticAdamsIndex s degree) = (s, degree) := by
    rw [(canonicalLambdaPowerBocksteinData X 1).source_reindex,
      syntheticAdamsReindex_index]
  have hn := inverse_convergence_square f.aMap f.filtration_compat
    (congrFun f.reindex_eq (syntheticAdamsIndex s degree)) hs ht
    ((lambdaPowerBocksteinSourceCSS X (n + 1)).conv.iso
      (syntheticAdamsIndex s degree))
    ((lambdaPowerBocksteinSourceCSS X 1).conv.iso
      (syntheticAdamsIndex s degree))
    (f.eMap (syntheticAdamsIndex s degree))
    (f.iso_compat (syntheticAdamsIndex s degree))
  have he : f.eMap (syntheticAdamsIndex s degree) =
      (synAdamsSS_functorial (XModLambdaN.toOne X n)).eInftyMap
        (syntheticAdamsIndex s degree) :=
    congrFun ((synAdamsFunctoriality Syn).eMap_eq (XModLambdaN.toOne X n)) _
  rw [sourceIso_hom _ s degree ht, sourceIso_hom _ s degree hs]
  rw [← Category.assoc, lambdaBoundaryToOne_e0SourceGraded, Category.assoc]
  erw [hn, he]
  simp only [Category.assoc]
  rfl

/-- On the target column, the zeroth-page comparison is the
associated-graded map induced by the suspended lambda-power map. -/
theorem lambdaBoundaryToOne_e0TargetGraded (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (s : ℤ) :
    lambdaBoundaryToOnePageMap X n degree 0 (s, 0) ≫
        ((canonicalLambdaPowerBocksteinData X 1).e0TargetIsoAssociatedGraded
          s degree).hom =
      ((canonicalLambdaPowerBocksteinData X (n + 1)).e0TargetIsoAssociatedGraded
          s degree).hom ≫
        Filtration.inducedAssocGradedMap
          (synAdamsConvergingMap
            ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n))).aMap
          (synAdamsConvergingMap
            ((shiftFunctor Syn (1 : ℤ)).map
              (lambdaPowerToOne X n))).filtration_compat s degree := by
  have h := ESSNaturality.spectralMap_e0Iso
    (lambdaPowerBocksteinCSSMap X (n + 1)) (lambdaPowerBocksteinCSSMap X 1)
    degree (lambdaBoundaryToOneComplexMap X n degree) s 0
  rw [lambdaBoundaryToOneComplexMap_target_graded] at h
  convert h using 1 <;>
    simp only [lambdaBoundaryToOnePageMap, lambdaBoundaryToOneMorphism,
      canonicalLambdaPowerBocksteinData, syntheticExtensionCoreDataOfMap,
      synAdamsConvergingMap,
      SyntheticExtensionCoreData.e0TargetIsoAssociatedGraded,
      Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  all_goals rfl

private theorem targetIso_hom {X Y : Syn} {f : X ⟶ Y}
    (D : SyntheticExtensionCoreData f) (s : ℤ) (degree : ℤ × ℤ)
    (hi : D.targetConvergence.reindex (syntheticAdamsIndex s degree) =
      (s, degree)) :
    (D.e0TargetIso s degree).hom =
      (D.e0TargetIsoAssociatedGraded s degree).hom ≫
        D.targetFiltration.transportGraded hi.symm ≫
        (D.targetConvergence.iso (syntheticAdamsIndex s degree)).inv := by
  simp only [SyntheticExtensionCoreData.e0TargetIso, Iso.trans_hom, Iso.symm_hom]
  apply congrArg (fun z => (D.e0TargetIsoAssociatedGraded s degree).hom ≫ z)
  have hB : D.targetFiltration.associatedGraded
      (D.targetConvergence.reindex (syntheticAdamsIndex s degree)).1
      (D.targetConvergence.reindex (syntheticAdamsIndex s degree)).2 =
      D.targetFiltration.associatedGraded s degree := by rw [hi]
  have he : (((SynAdamsSS Syn Y).ssData
      (syntheticAdamsIndex s degree)).eInfty ≅
        D.targetFiltration.associatedGraded
          (D.targetConvergence.reindex (syntheticAdamsIndex s degree)).1
          (D.targetConvergence.reindex (syntheticAdamsIndex s degree)).2) =
      (((SynAdamsSS Syn Y).ssData
        (syntheticAdamsIndex s degree)).eInfty ≅
          D.targetFiltration.associatedGraded s degree) := by rw [hi]
  exact castIso_inv (D.targetConvergence.iso (syntheticAdamsIndex s degree)) hB he

/-- The target zeroth-page comparison commutes with the actual Adams map
induced by the suspended lambda power. -/
theorem lambdaBoundaryToOne_e0Target (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (s : ℤ) :
    lambdaBoundaryToOnePageMap X n degree 0 (s, 0) ≫
        ((canonicalLambdaPowerBocksteinData X 1).e0TargetIso s degree).hom =
      ((canonicalLambdaPowerBocksteinData X (n + 1)).e0TargetIso s degree).hom ≫
        (synAdamsSS_functorial
          ((shiftFunctor Syn (1 : ℤ)).map
            (lambdaPowerToOne X n))).eInftyMap
          (syntheticAdamsIndex s degree) := by
  let f := synAdamsConvergingMap
    ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n))
  have hs : (canonicalLambdaPowerBocksteinData X (n + 1)).targetConvergence.reindex
      (syntheticAdamsIndex s degree) = (s, degree) := by
    rw [(canonicalLambdaPowerBocksteinData X (n + 1)).target_reindex,
      syntheticAdamsReindex_index]
  have ht : (canonicalLambdaPowerBocksteinData X 1).targetConvergence.reindex
      (syntheticAdamsIndex s degree) = (s, degree) := by
    rw [(canonicalLambdaPowerBocksteinData X 1).target_reindex,
      syntheticAdamsReindex_index]
  have hn := inverse_convergence_square f.aMap f.filtration_compat
    (congrFun f.reindex_eq (syntheticAdamsIndex s degree)) hs ht
    ((lambdaPowerBocksteinTargetCSS X (n + 1)).conv.iso
      (syntheticAdamsIndex s degree))
    ((lambdaPowerBocksteinTargetCSS X 1).conv.iso
      (syntheticAdamsIndex s degree))
    (f.eMap (syntheticAdamsIndex s degree))
    (f.iso_compat (syntheticAdamsIndex s degree))
  have he : f.eMap (syntheticAdamsIndex s degree) =
      (synAdamsSS_functorial
        ((shiftFunctor Syn (1 : ℤ)).map
          (lambdaPowerToOne X n))).eInftyMap
        (syntheticAdamsIndex s degree) :=
    congrFun ((synAdamsFunctoriality Syn).eMap_eq
      ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n))) _
  rw [targetIso_hom _ s degree ht, targetIso_hom _ s degree hs]
  rw [← Category.assoc, lambdaBoundaryToOne_e0TargetGraded, Category.assoc]
  erw [hn, he]
  simp only [Category.assoc]
  rfl

/-- The ambient comparison is given by the associated-graded map of the
actual filtered restriction square and the two convergence identifications. -/
theorem lambdaBoundaryToOneMorphism_ambient (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (s k : ℤ) :
    (lambdaBoundaryToOneMorphism X n degree).φ (s, k) ≫
        (unboundedExtensionVComplexIso
          (lambdaPowerBocksteinCSSMap X 1) degree s k).hom =
      (unboundedExtensionVComplexIso
        (lambdaPowerBocksteinCSSMap X (n + 1)) degree s k).hom ≫
          (lambdaBoundaryToOneComplexMap X n degree).assocGradedMap s k := by
  exact ESSNaturality.spectralMap_ambient
    (lambdaPowerBocksteinCSSMap X (n + 1)) (lambdaPowerBocksteinCSSMap X 1)
    degree (lambdaBoundaryToOneComplexMap X n degree) s k

/-- Both endpoints of a specified boundary relation are transported by the
same canonical map. The page and filtration indices are preserved. -/
theorem lambdaBoundaryToOne_relation (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (r : ℤ) (k : ℤ × ℤ)
    {T : AddCommGrpCat.{0}}
    {x : T ⟶ ((canonicalLambdaPowerBocksteinESS X (n + 1) degree).ssData k).V}
    {y : T ⟶ ((canonicalLambdaPowerBocksteinESS X (n + 1) degree).ssData
      (k + (r, -1))).V}
    (h : DifferentialRelation (canonicalLambdaPowerBocksteinESS X (n + 1) degree)
      r k x y) :
    DifferentialRelation (canonicalLambdaPowerBocksteinESS X 1 degree) r k
      (x ≫ (lambdaBoundaryToOneMorphism X n degree).φ k)
      (y ≫ (lambdaBoundaryToOneMorphism X n degree).φ (k + (r, -1))) :=
  ESSNaturality.spectralMap_relation
    (lambdaPowerBocksteinCSSMap X (n + 1)) (lambdaPowerBocksteinCSSMap X 1)
    degree (lambdaBoundaryToOneComplexMap X n degree) r k h

/-- Essentiality of the image implies essentiality of the original
relation. The forward implication is deliberately not asserted: restriction
can annihilate a target page class. -/
theorem lambdaBoundaryToOne_essential_reflect (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) (r : ℤ) (k : ℤ × ℤ)
    {T : AddCommGrpCat.{0}}
    {x : T ⟶ ((canonicalLambdaPowerBocksteinESS X (n + 1) degree).ssData k).V}
    {y : T ⟶ ((canonicalLambdaPowerBocksteinESS X (n + 1) degree).ssData
      (k + (r, -1))).V}
    (h : DifferentialRelation (canonicalLambdaPowerBocksteinESS X (n + 1) degree)
      r k x y)
    (h' : EssentialDifferentialRelation (canonicalLambdaPowerBocksteinESS X 1 degree)
      r k (x ≫ (lambdaBoundaryToOneMorphism X n degree).φ k)
        (y ≫ (lambdaBoundaryToOneMorphism X n degree).φ (k + (r, -1)))) :
    EssentialDifferentialRelation (canonicalLambdaPowerBocksteinESS X (n + 1) degree)
      r k x y := by
  refine ⟨h, ?_⟩
  intro hy
  let F := lambdaBoundaryToOneMorphism X n degree
  let a := (F.preserves_B (k + (r, -1)) (↑(r - 0).toNat)).choose
  have ha := (F.preserves_B (k + (r, -1)) (↑(r - 0).toNat)).choose_spec
  change Subobject.Factors
    (((canonicalLambdaPowerBocksteinESS X (n + 1) degree).ssData
      (k + (r, -1))).B (↑(r - 0).toNat)) y at hy
  obtain ⟨b, hb⟩ := (Subobject.factors_iff _ _).mp hy
  apply h'.2
  change Subobject.Factors
    (((canonicalLambdaPowerBocksteinESS X 1 degree).ssData
      (k + (r, -1))).B (↑(r - 0).toNat)) (y ≫ F.φ (k + (r, -1)))
  apply (Subobject.factors_iff _ _).mpr
  refine ⟨b ≫ a, ?_⟩
  change (b ≫ a) ≫
    (((canonicalLambdaPowerBocksteinESS X 1 degree).ssData
      (k + (r, -1))).B (↑(r - 0).toNat)).arrow = _
  rw [Category.assoc, ha, ← Category.assoc]
  exact congrArg (fun z => z ≫ F.φ (k + (r, -1))) hb

/-- Restriction from `nu X / lambda^(n+1)` to `nu X / lambda` commutes
with the canonical stable-page comparisons. On the `nu X` side the
resulting map is the canonical inclusion of page `n+2` into E2. -/
theorem nuModLambdaSuccGeneratorEInftyIsoPage_toOne
    (𝒮 : Type*) [StableHomotopy.StableHomotopyCategory 𝒮]
    (X : 𝒮) (n : ℕ) (s t : ℤ) :
    (synAdamsSS_functorial
        (XModLambdaN.toOne ((nu 𝒮 Syn).obj X) n)).eInftyMap (s, t, t) ≫
        (nuModLambdaSuccGeneratorEInftyIsoPage 𝒮 Syn X 0 s t).hom =
      (nuModLambdaSuccGeneratorEInftyIsoPage 𝒮 Syn X n s t).hom ≫
        synAdams_displayedPageToE2OfBoundariesEq
          ((nu 𝒮 Syn).obj X) n (s, t, t)
          (synAdams_nu_diagonal_boundaries 𝒮 Syn X s t n) := by
  let A := (nu 𝒮 Syn).obj X
  let QN := XModLambdaN A (n + 1)
  let Q1 := XModLambdaN A 1
  have hdN := synAdams_mod_lambda_degenerates 𝒮 Syn X (n + 1) (by omega)
  have hpN : max 2 ((((n + 1 : ℕ) : ℤ)) + 1) =
      ((n + 2 : ℕ) : ℤ) := by omega
  rw [hpN] at hdN
  have hd10 := synAdams_mod_lambda_degenerates 𝒮 Syn X 1 (by omega)
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
    (nuModLambdaIncl 𝒮 Syn X 1) n (s, t, t)
      (synAdams_nu_diagonal_boundaries 𝒮 Syn X s t n) hBQ1
  let qN := nuModLambdaAdamsPageMap 𝒮 Syn X (n + 1)
    ((n + 2 : ℕ) : ℤ) (s, t, t)
  let q1N := nuModLambdaAdamsPageMap 𝒮 Syn X 1
    ((n + 2 : ℕ) : ℤ) (s, t, t)
  let q10 := nuModLambdaAdamsPageMap 𝒮 Syn X 1 2 (s, t, t)
  let fN := synAdamsPageMap (XModLambdaN.toOne A n)
    ((n + 2 : ℕ) : ℤ) (s, t, t)
  have hq : qN ≫ fN = q1N := by
    dsimp only [qN, fN, q1N, nuModLambdaAdamsPageMap, nuModLambdaIncl]
    rw [← synAdamsPageMap_comp]
    exact congrArg
      (fun g => synAdamsPageMap g ((n + 2 : ℕ) : ℤ) (s, t, t))
      (XModLambdaN.incl_toOne A n)
  letI : IsIso qN := nuModLambdaAdamsPageMapIsIso_of_safe_range
    𝒮 Syn X (n + 1) (by omega) ((n + 2 : ℕ) : ℤ)
      (by omega) s t t (by omega) (by omega)
  letI : IsIso q10 := nuModLambdaAdamsE2PageMapIsIso
    𝒮 Syn X 1 (by omega) s t t (by omega)
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
        (synAdams_nu_diagonal_boundaries 𝒮 Syn X s t n))
  rw [← Category.assoc, hq]
  dsimp only [q1N] at hincl ⊢
  unfold nuModLambdaAdamsPageMap
  dsimp only [Q1, A] at hincl ⊢
  rw [← Category.assoc, hincl]
  have hq10eq : synAdamsPageMap (nuModLambdaIncl 𝒮 Syn X 1)
      2 (s, t, t) = q10 := rfl
  rw [hq10eq]
  simp

/-- The source bidegree used by the boundary E0 term is the diagonal
synthetic Adams tridegree.  Keeping this equality named prevents later
comparison proofs from unfolding it under categorical transports. -/
theorem syntheticAdamsIndex_boundaryDiagonal (s t : ℤ) :
    syntheticAdamsIndex s (t - s, t) = (s, t, t) := by
  ext <;> simp [syntheticAdamsIndex]

end KIPBase.Synthetic
