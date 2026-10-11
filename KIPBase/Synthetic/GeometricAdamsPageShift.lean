/-
  KIPBase.Synthetic.GeometricAdamsPageShift
  Page-level transport for geometric Adams towers under synthetic shifts.
-/
import KIPBase.Synthetic.GeometricAdamsShift

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]
    [SyntheticShiftCofiberCompatibility (Syn := Syn)]

namespace GeometricAdams.Input

variable {X : Syn}

/-- Postcomposition by an isomorphism is an additive equivalence of represented
hom groups. -/
noncomputable def postcomposeIsoAddEquiv (S : Syn) {A B : Syn} (e : A ≅ B) :
    (S ⟶ A) ≃+ (S ⟶ B) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  map_add' _ _ := by simp only [Preadditive.add_comp]
  left_inv f := by simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv f := by simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

/-- An additive equivalence of categories induces an additive equivalence on
each hom group. -/
noncomputable def functorHomAddEquiv (F : Syn ⥤ Syn) [F.IsEquivalence]
    [F.Additive] (A B : Syn) : (A ⟶ B) ≃+ (F.obj A ⟶ F.obj B) :=
  AddEquiv.ofBijective F.mapAddHom
    ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective A B)

/-- Map a represented hom group through a shift and then through a specified
comparison isomorphism on its target. -/
noncomputable def shiftHomAddEquiv (p : ℤ × ℤ) (S : Syn)
    {A B : Syn} (e : (SyntheticCategory.biShift p).obj A ≅ B) :
    (S ⟶ A) ≃+ ((SyntheticCategory.biShift p).obj S ⟶ B) :=
  (functorHomAddEquiv (SyntheticCategory.biShift p) S A).trans
    (postcomposeIsoAddEquiv _ e)

/-- Shifted representatives are equivalent to representatives in the shifted
tower. -/
noncomputable def representativeShiftEquiv (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ) :
    G.Representative S s r ≃+
      (G.map (SyntheticCategory.biShift p)).Representative
        ((SyntheticCategory.biShift p).obj S) s r :=
  shiftHomAddEquiv p S
    (G.relativeShiftIso p s (s + r) (Nat.le_add_right s r))

/-- Shifted adjacent-layer classes. -/
noncomputable def layerClassShiftEquiv (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s : ℕ) :
    (S ⟶ G.layer s) ≃+
      ((SyntheticCategory.biShift p).obj S ⟶
        (G.map (SyntheticCategory.biShift p)).layer s) :=
  shiftHomAddEquiv p S (G.layerShiftIso p s)

/-- Comparison on the suspended target layer of a geometric differential. -/
noncomputable def targetLayerShiftIso (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (s : ℕ) :
    (SyntheticCategory.biShift p).obj
        ((shiftFunctor Syn (1 : ℤ)).obj (G.layer s)) ≅
      (shiftFunctor Syn (1 : ℤ)).obj
        ((G.map (SyntheticCategory.biShift p)).layer s) :=
  ((SyntheticCategory.biShift p).commShiftIso (1 : ℤ)).app (G.layer s) ≪≫
    (shiftFunctor Syn (1 : ℤ)).mapIso (G.layerShiftIso p s)

/-- Shifted target-layer classes. -/
noncomputable def targetClassShiftEquiv (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s : ℕ) :
    (S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer s)) ≃+
      ((SyntheticCategory.biShift p).obj S ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((G.map (SyntheticCategory.biShift p)).layer s)) :=
  shiftHomAddEquiv p S (G.targetLayerShiftIso p s)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Reading the source of a representative commutes with shifting. -/
theorem source_representativeShiftEquiv (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (z : G.Representative S s r) :
    (G.map (SyntheticCategory.biShift p)).source
        ((SyntheticCategory.biShift p).obj S) s r hr
        (G.representativeShiftEquiv p S s r z) =
      G.layerClassShiftEquiv p S s (G.source S s r hr z) := by
  change ((SyntheticCategory.biShift p).map z ≫
      (G.relativeShiftIso p s (s + r) _).hom) ≫
        (G.map (SyntheticCategory.biShift p)).sourceProjection s (s + r) _ =
    (SyntheticCategory.biShift p).map (z ≫ G.sourceProjection s (s + r) _) ≫
      (G.layerShiftIso p s).hom
  rw [Category.assoc, ← G.relativeShiftIso_sourceProjection,
    ← Category.assoc, ← Functor.map_comp]

/-- Reading the differential target of a representative commutes with
shifting. -/
theorem target_representativeShiftEquiv (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ)
    (z : G.Representative S s r) :
    (G.map (SyntheticCategory.biShift p)).target
        ((SyntheticCategory.biShift p).obj S) s r
        (G.representativeShiftEquiv p S s r z) =
      G.targetClassShiftEquiv p S (s + r) (G.target S s r z) := by
  change ((SyntheticCategory.biShift p).map z ≫
      (G.relativeShiftIso p s (s + r) _).hom) ≫
        (G.map (SyntheticCategory.biShift p)).targetProjection s (s + r) _ =
    (SyntheticCategory.biShift p).map (z ≫ G.targetProjection s (s + r) _) ≫
      (((SyntheticCategory.biShift p).commShiftIso (1 : ℤ)).hom.app (G.layer (s + r)) ≫
        (shiftFunctor Syn (1 : ℤ)).map (G.layerShiftIso p (s + r)).hom)
  rw [Functor.map_comp, Category.assoc, Category.assoc,
    G.relativeShiftIso_targetProjection]

/-- The actual representative relation is preserved and reflected by every
compatible synthetic bidegree shift. -/
theorem representativeRelation_shift_iff (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (x : S ⟶ G.layer s)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) :
    (G.map (SyntheticCategory.biShift p)).RepresentativeRelation
        ((SyntheticCategory.biShift p).obj S) s r hr
        (G.layerClassShiftEquiv p S s x)
        (G.targetClassShiftEquiv p S (s + r) y) ↔
      G.RepresentativeRelation S s r hr x y := by
  constructor
  · rintro ⟨z', hz'x, hz'y⟩
    let z := (G.representativeShiftEquiv p S s r).symm z'
    refine ⟨z, ?_, ?_⟩
    · apply (G.layerClassShiftEquiv p S s).injective
      rw [← G.source_representativeShiftEquiv p S s r hr]
      simpa only [z, AddEquiv.apply_symm_apply] using hz'x
    · apply (G.targetClassShiftEquiv p S (s + r)).injective
      rw [← G.target_representativeShiftEquiv p S s r]
      simpa only [z, AddEquiv.apply_symm_apply] using hz'y
  · rintro ⟨z, rfl, rfl⟩
    refine ⟨G.representativeShiftEquiv p S s r z, ?_, ?_⟩
    · exact G.source_representativeShiftEquiv p S s r hr z
    · exact G.target_representativeShiftEquiv p S s r z

/-! ### Cycles and target ambiguity -/

/-- Membership in the source-cycle subgroup is preserved and reflected by
the layer comparison. -/
theorem layerClassShift_mem_sourceCycles_iff (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (x : S ⟶ G.layer s) :
    G.layerClassShiftEquiv p S s x ∈
        (G.map (SyntheticCategory.biShift p)).sourceCycles
          ((SyntheticCategory.biShift p).obj S) s r hr ↔
      x ∈ G.sourceCycles S s r hr := by
  constructor
  · rintro ⟨z', hz'⟩
    let z := (G.representativeShiftEquiv p S s r).symm z'
    refine ⟨z, ?_⟩
    apply (G.layerClassShiftEquiv p S s).injective
    rw [← G.source_representativeShiftEquiv p S s r hr]
    simpa only [z, AddEquiv.apply_symm_apply] using hz'
  · rintro ⟨z, rfl⟩
    exact ⟨G.representativeShiftEquiv p S s r z,
      G.source_representativeShiftEquiv p S s r hr z⟩

/-- Additive equivalence between the source cycles before and after a
compatible bidegree shift. -/
noncomputable def sourceCyclesShiftEquiv (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) :
    G.sourceCycles S s r hr ≃+
      (G.map (SyntheticCategory.biShift p)).sourceCycles
        ((SyntheticCategory.biShift p).obj S) s r hr where
  toFun x := ⟨G.layerClassShiftEquiv p S s x,
    (G.layerClassShift_mem_sourceCycles_iff p S s r hr x).2 x.property⟩
  invFun x := ⟨(G.layerClassShiftEquiv p S s).symm x,
    (G.layerClassShift_mem_sourceCycles_iff p S s r hr
      ((G.layerClassShiftEquiv p S s).symm x)).1 (by
        rw [(G.layerClassShiftEquiv p S s).apply_symm_apply]
        exact x.property)⟩
  map_add' x y := Subtype.ext (by
    change G.layerClassShiftEquiv p S s (x + y) =
      G.layerClassShiftEquiv p S s x + G.layerClassShiftEquiv p S s y
    exact map_add (G.layerClassShiftEquiv p S s) x.val y.val)
  left_inv x := Subtype.ext
    ((G.layerClassShiftEquiv p S s).symm_apply_apply x.val)
  right_inv x := Subtype.ext
    ((G.layerClassShiftEquiv p S s).apply_symm_apply x.val)

/-- Membership in the ambiguity at the differential target is preserved and
reflected by the target-layer comparison. -/
theorem targetClassShift_mem_targetAmbiguity_iff
    (G : GeometricAdams.Input X) (p : ℤ × ℤ) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) :
    G.targetClassShiftEquiv p S (s + r) y ∈
        (G.map (SyntheticCategory.biShift p)).targetAmbiguity
          ((SyntheticCategory.biShift p).obj S) s r hr ↔
      y ∈ G.targetAmbiguity S s r hr := by
  constructor
  · rintro ⟨z', hz', hy'⟩
    change (G.map (SyntheticCategory.biShift p)).source
      ((SyntheticCategory.biShift p).obj S) s r hr z' = 0 at hz'
    let z := (G.representativeShiftEquiv p S s r).symm z'
    refine ⟨z, ?_, ?_⟩
    · change G.source S s r hr z = 0
      apply (G.layerClassShiftEquiv p S s).injective
      rw [map_zero, ← G.source_representativeShiftEquiv p S s r hr]
      simpa only [z, AddEquiv.apply_symm_apply] using hz'
    · apply (G.targetClassShiftEquiv p S (s + r)).injective
      rw [← G.target_representativeShiftEquiv p S s r]
      simpa only [z, AddEquiv.apply_symm_apply] using hy'
  · rintro ⟨z, hz, rfl⟩
    refine ⟨G.representativeShiftEquiv p S s r z, ?_, ?_⟩
    · change (G.map (SyntheticCategory.biShift p)).source
          ((SyntheticCategory.biShift p).obj S) s r hr
          (G.representativeShiftEquiv p S s r z) = 0
      rw [G.source_representativeShiftEquiv p S s r hr, hz, map_zero]
    · exact G.target_representativeShiftEquiv p S s r z

/-! ### Incoming boundaries -/

/-- Shifted represented classes in an actual stage. -/
noncomputable def stageClassShiftEquiv (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s : ℕ) :
    (S ⟶ G.stage s) ≃+
      ((SyntheticCategory.biShift p).obj S ⟶
        (G.map (SyntheticCategory.biShift p)).stage s) :=
  functorHomAddEquiv (SyntheticCategory.biShift p) S (G.stage s)

/-- Projection from a stage to its adjacent layer commutes with shifting. -/
theorem stageProjection_stageClassShiftEquiv (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s : ℕ) (a : S ⟶ G.stage s) :
    (G.map (SyntheticCategory.biShift p)).stageProjection
        ((SyntheticCategory.biShift p).obj S) s
        (G.stageClassShiftEquiv p S s a) =
      G.layerClassShiftEquiv p S s (G.stageProjection S s a) := by
  change (SyntheticCategory.biShift p).map a ≫
      syn_functorial_cofiber.cofibι
        ((SyntheticCategory.biShift p).map
          (G.transition s (s + 1) (Nat.le_succ s))) =
    (SyntheticCategory.biShift p).map
        (a ≫ syn_functorial_cofiber.cofibι
          (G.transition s (s + 1) (Nat.le_succ s))) ≫
      (G.layerShiftIso p s).hom
  dsimp only [layerShiftIso, relativeShiftIso]
  rw [Functor.map_comp, Category.assoc,
    SyntheticShiftCofiberCompatibility.biShiftCofibIso_ι]

/-- The actual incoming-boundary subgroup is preserved and reflected by a
compatible bidegree shift. -/
theorem layerClassShift_mem_incomingBoundaries_iff
    (G : GeometricAdams.Input X) (p : ℤ × ℤ) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (x : S ⟶ G.layer s) :
    G.layerClassShiftEquiv p S s x ∈
        (G.map (SyntheticCategory.biShift p)).incomingBoundaries
          ((SyntheticCategory.biShift p).obj S) s r hr ↔
      x ∈ G.incomingBoundaries S s r hr := by
  let F := SyntheticCategory.biShift (Syn := Syn) p
  constructor
  · rintro ⟨a', ha', hproj'⟩
    change a' ≫ F.map (G.transition (s + 1 - r) s (by omega)) = 0 at ha'
    let a := (G.stageClassShiftEquiv p S s).symm a'
    have haeq : F.map a = a' :=
      (G.stageClassShiftEquiv p S s).apply_symm_apply a'
    refine ⟨a, ?_, ?_⟩
    · change a ≫ G.transition (s + 1 - r) s (by omega) = 0
      apply F.map_injective
      rw [F.map_comp, F.map_zero]
      rw [haeq]
      exact ha'
    · apply (G.layerClassShiftEquiv p S s).injective
      rw [← G.stageProjection_stageClassShiftEquiv p S s]
      simpa only [a, AddEquiv.apply_symm_apply] using hproj'
  · rintro ⟨a, ha, hproj⟩
    refine ⟨G.stageClassShiftEquiv p S s a, ?_, ?_⟩
    · change F.map a ≫ F.map (G.transition (s + 1 - r) s (by omega)) = 0
      change a ≫ G.transition (s + 1 - r) s (by omega) = 0 at ha
      rw [← F.map_comp, ha, F.map_zero]
    · rw [G.stageProjection_stageClassShiftEquiv p S s, hproj]

/-- The cycle equivalence identifies the incoming-boundary subgroups inside
the respective source-cycle groups. -/
theorem sourceCyclesShift_mem_pageBoundaries_iff
    (G : GeometricAdams.Input X) (p : ℤ × ℤ) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (x : G.sourceCycles S s r hr) :
    G.sourceCyclesShiftEquiv p S s r hr x ∈
        (G.map (SyntheticCategory.biShift p)).pageBoundaries
          ((SyntheticCategory.biShift p).obj S) s r hr ↔
      x ∈ G.pageBoundaries S s r hr := by
  change G.layerClassShiftEquiv p S s x.val ∈
      (G.map (SyntheticCategory.biShift p)).incomingBoundaries
        ((SyntheticCategory.biShift p).obj S) s r hr ↔
    x.val ∈ G.incomingBoundaries S s r hr
  exact G.layerClassShift_mem_incomingBoundaries_iff p S s r hr x.val

/-! ### Quotient pages -/

/-- An additive equivalence carrying one subgroup exactly onto another
descends to an additive equivalence of quotient groups. -/
noncomputable def quotientAddEquivOfAddEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) (K : AddSubgroup B)
    (h : ∀ a, e a ∈ K ↔ a ∈ H) : (A ⧸ H) ≃+ (B ⧸ K) := by
  let f : (A ⧸ H) →+ (B ⧸ K) :=
    QuotientAddGroup.map H K e.toAddMonoidHom (fun a ha ↦ (h a).2 ha)
  let g : (B ⧸ K) →+ (A ⧸ H) :=
    QuotientAddGroup.map K H e.symm.toAddMonoidHom (fun b hb ↦ by
      apply (h (e.symm b)).1
      simpa only [e.apply_symm_apply] using hb)
  exact
    { toFun := f
      invFun := g
      map_add' := f.map_add
      left_inv := by
        intro q
        induction q using QuotientAddGroup.induction_on with
        | H a =>
          change QuotientAddGroup.mk (e.symm (e a)) = QuotientAddGroup.mk a
          rw [e.symm_apply_apply]
      right_inv := by
        intro q
        induction q using QuotientAddGroup.induction_on with
        | H b =>
          change QuotientAddGroup.mk (e (e.symm b)) = QuotientAddGroup.mk b
          rw [e.apply_symm_apply] }

/-- The page quotient itself is invariant under every compatible synthetic
bidegree shift. -/
noncomputable def pageGroupShiftEquiv (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) :
    G.PageGroup S s r hr ≃+
      (G.map (SyntheticCategory.biShift p)).PageGroup
        ((SyntheticCategory.biShift p).obj S) s r hr :=
  quotientAddEquivOfAddEquiv (G.sourceCyclesShiftEquiv p S s r hr)
    (G.pageBoundaries S s r hr)
    ((G.map (SyntheticCategory.biShift p)).pageBoundaries
      ((SyntheticCategory.biShift p).obj S) s r hr)
    (G.sourceCyclesShift_mem_pageBoundaries_iff p S s r hr)

@[simp] theorem pageGroupShiftEquiv_mk (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (x : G.sourceCycles S s r hr) :
    G.pageGroupShiftEquiv p S s r hr (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (G.sourceCyclesShiftEquiv p S s r hr x) :=
  rfl

/-- The quotient by target ambiguity is invariant under the same shift. -/
noncomputable def targetQuotientShiftEquiv (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) :
    ((S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) ⧸
        G.targetAmbiguity S s r hr) ≃+
      ((((SyntheticCategory.biShift p).obj S ⟶
          (shiftFunctor Syn (1 : ℤ)).obj
            ((G.map (SyntheticCategory.biShift p)).layer (s + r)))) ⧸
        (G.map (SyntheticCategory.biShift p)).targetAmbiguity
          ((SyntheticCategory.biShift p).obj S) s r hr) :=
  quotientAddEquivOfAddEquiv (G.targetClassShiftEquiv p S (s + r))
    (G.targetAmbiguity S s r hr)
    ((G.map (SyntheticCategory.biShift p)).targetAmbiguity
      ((SyntheticCategory.biShift p).obj S) s r hr)
    (G.targetClassShift_mem_targetAmbiguity_iff p S s r hr)

@[simp] theorem targetQuotientShiftEquiv_mk (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) :
    G.targetQuotientShiftEquiv p S s r hr (QuotientAddGroup.mk y) =
      QuotientAddGroup.mk (G.targetClassShiftEquiv p S (s + r) y) :=
  rfl

/-! ### Compatibility of the geometric obstruction -/

/-- Before quotienting the source by incoming boundaries, the geometric
obstruction commutes with the cycle and target quotient comparisons. -/
theorem obstruction_sourceCyclesShiftEquiv (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (x : G.sourceCycles S s r hr) :
    (G.map (SyntheticCategory.biShift p)).obstruction
        ((SyntheticCategory.biShift p).obj S) s r hr
        (G.sourceCyclesShiftEquiv p S s r hr x) =
      G.targetQuotientShiftEquiv p S s r hr
        (G.obstruction S s r hr x) := by
  obtain ⟨z, hz⟩ := x.property
  let x₀ : G.sourceCycles S s r hr :=
    ⟨G.source S s r hr z, ⟨z, rfl⟩⟩
  have hx : x₀ = x := Subtype.ext hz
  let z' := G.representativeShiftEquiv p S s r z
  let x₀' :=
    (⟨(G.map (SyntheticCategory.biShift p)).source
        ((SyntheticCategory.biShift p).obj S) s r hr z', ⟨z', rfl⟩⟩ :
      (G.map (SyntheticCategory.biShift p)).sourceCycles
        ((SyntheticCategory.biShift p).obj S) s r hr)
  have hx' : G.sourceCyclesShiftEquiv p S s r hr x₀ = x₀' := by
    apply Subtype.ext
    exact (G.source_representativeShiftEquiv p S s r hr z).symm
  rw [← hx, hx',
    (G.map (SyntheticCategory.biShift p)).obstruction_source,
    G.obstruction_source, G.targetQuotientShiftEquiv_mk,
    G.target_representativeShiftEquiv]

/-- The fully quotiented page obstruction is natural under every compatible
synthetic bidegree shift. -/
theorem pageObstruction_shift (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (x : G.PageGroup S s r hr) :
    (G.map (SyntheticCategory.biShift p)).pageObstruction
        ((SyntheticCategory.biShift p).obj S) s r hr
        (G.pageGroupShiftEquiv p S s r hr x) =
      G.targetQuotientShiftEquiv p S s r hr
        (G.pageObstruction S s r hr x) := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
      simpa only [G.pageGroupShiftEquiv_mk,
        (G.map (SyntheticCategory.biShift p)).pageObstruction_mk,
        G.pageObstruction_mk] using
        G.obstruction_sourceCyclesShiftEquiv p S s r hr x

end GeometricAdams.Input

end

end KIPBase.Synthetic
