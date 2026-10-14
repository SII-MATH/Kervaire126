module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Stage.Comparison.Data
public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Stage.Proofs
public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Proofs
public import KIP126.Def.StableHomotopy.Context.CofiberFactorization.Proofs

@[expose] public section


/-! A concrete obstruction factorization for the two specified stage
products. Equality is proved on representatives whose long connecting
composite is zero. This is stronger than being an arbitrary finite-page
cycle; neither a product of two long layers nor a Leibniz law is proved. -/

namespace KIP126.Classical.Adams.LongLayerStageComparison
noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

set_option backward.isDefEq.respectTransparency false

theorem projectionNat_ι {U : C} (unit : 𝟙_ C ⟶ U) (X : C)
    (s n : ℕ) (h : s + 1 ≤ n) :
    HasFunctorialCofiber.cofibι (adamsTowerMap unit X s n (by omega)) ≫
      projectionNat unit X s n h = (adamsLayerTriangle unit X s).mor₂ :=
  cofiberFactorizationMap_ι _ _ (adamsTowerMap unit X (s + 1) n h)
    (adamsTowerMap_comp unit X s (s + 1) n (by omega) h)

theorem projectionNat_eq {U : C} (unit : 𝟙_ C ⟶ U) (X : C)
    (r : ℕ) (hr : 1 ≤ r) (s : ℕ) :
    projectionNat unit X s (s + r) (by omega) =
      adamsLongLayerProjection unit X r hr s := rfl

private theorem cofiber_iso_comp_transport
    {X X' Y Z A : C} {f : X ⟶ Y} {f' : X' ⟶ Y}
    {e : A ≅ HasFunctorialCofiber.cofib f}
    {e' : A ≅ HasFunctorialCofiber.cofib f'}
    {p : HasFunctorialCofiber.cofib f ⟶ Z}
    {p' : HasFunctorialCofiber.cofib f' ⟶ Z}
    (hX : X = X') (hf : HEq f f') (he : HEq e e') (hp : HEq p p') :
    e.hom ≫ p = e'.hom ≫ p' := by
  subst X'
  cases hf
  cases he
  cases hp
  rfl

variable [BraidedCategory C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

omit [BraidedCategory C] in
/-- This projected triangle component is exactly the already constructed
long-stage isomorphism followed by the existing long-layer projection. -/
theorem stageProjected_eq_actual (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    stageProjected H.unit r hr s t =
      (adamsSphereLongLayerStagePairingIso H.unit r hr s t).hom ≫
        adamsLongLayerProjection H.unit (𝟙_ C) r hr ((t + s : ℕ) : ℤ) := by
  apply cofiber_iso_comp_transport
    (e := Triangle.π₃.mapIso (adamsSphereLongLayerStageTriangleIso H.unit r s t))
    (f := adamsTowerMap H.unit (𝟙_ C) (t + s) (t + (s + r)) (by omega))
  · simp only [adamsTowerAt, ← Int.natCast_add, Int.toNat_natCast, Nat.add_assoc]
  · simp only [adamsTowerMapAt, ← Int.natCast_add, Int.toNat_natCast]
    simp only [adamsTowerMap, eqToHom_comp_heq_iff]
    symm
    rw [eqToHom_comp_heq_iff]
    congr 1
    omega
  · unfold adamsSphereLongLayerStagePairingIso
    exact (cast_heq _ _).symm
  · change HEq (projectionNat H.unit (𝟙_ C) (t + s) (t + (s + r)) (by omega))
      (adamsLongLayerProjection H.unit (𝟙_ C) r hr ((t + s : ℕ) : ℤ))
    have hp {a n m : ℕ} (hn : n = m) (hn' : a + 1 ≤ n) (hm' : a + 1 ≤ m) :
        HEq (projectionNat H.unit (𝟙_ C) a n hn') (projectionNat H.unit (𝟙_ C) a m hm') := by
      cases hn
      rfl
    exact hp (by omega : t + (s + r) = (t + s) + r) _ _

omit [BraidedCategory C] in
theorem stageProjected_ι (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    (HasFunctorialCofiber.cofibι (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega)) ▷
      adamsTower H.unit (𝟙_ C) t) ≫ stageProjected H.unit r hr s t =
      (adamsTowerSpherePairingIso H.unit s t).hom ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₂ := by
  unfold stageProjected
  rw [← Category.assoc, adamsSphereLongLayerStageTriangleIso_ι, Category.assoc,
    projectionNat_ι]

omit [MonoidalPreadditive C] in
theorem coefficientAction_ι (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    (HasFunctorialCofiber.cofibι (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega)) ▷
      adamsTower H.unit (𝟙_ C) t) ≫ coefficientAction H R r hr s t =
      (adamsTowerSpherePairingIso H.unit s t).hom ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₂ := by
  unfold coefficientAction
  erw [← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
    Category.id_comp, projectionNat_ι]
  exact adamsSphereLayerProduct_ι H R s t

/-- For every positive length, the two specific actual projections differ
by a map through the connecting morphism of the source long triangle. -/
theorem defect_factors (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    ∃ k : (adamsTower H.unit (𝟙_ C) (s + r) ⊗
        adamsTower H.unit (𝟙_ C) t)⟦(1 : ℤ)⟧ ⟶
      adamsLayerAt H.unit (𝟙_ C) ((t + s : ℕ) : ℤ),
      stageProjected H.unit r hr s t - coefficientAction H R r hr s t =
        (HasFunctorialCofiber.cofibδ (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega)) ▷
          adamsTower H.unit (𝟙_ C) t) ≫
        (Functor.commShiftIso (tensorRight (adamsTower H.unit (𝟙_ C) t))
          (1 : ℤ)).hom.app (adamsTower H.unit (𝟙_ C) (s + r)) ≫ k := by
  let T := Triangle.mk (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega))
    (HasFunctorialCofiber.cofibι (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega)))
    (HasFunctorialCofiber.cofibδ (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega)))
  have hz : ((tensorRight (adamsTower H.unit (𝟙_ C) t)).mapTriangle.obj T).mor₂ ≫
      (stageProjected H.unit r hr s t - coefficientAction H R r hr s t) = 0 := by
    change (HasFunctorialCofiber.cofibι (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega)) ▷
        adamsTower H.unit (𝟙_ C) t) ≫
      (stageProjected H.unit r hr s t - coefficientAction H R r hr s t) = 0
    rw [Preadditive.comp_sub, stageProjected_ι, coefficientAction_ι, sub_self]
  obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃
    ((tensorRight (adamsTower H.unit (𝟙_ C) t)).mapTriangle.obj T)
    ((tensorRight (adamsTower H.unit (𝟙_ C) t)).map_distinguished T
      (HasFunctorialCofiber.cofib_distinguished _)) _ hz
  exact ⟨k, hk.trans (Category.assoc _ _ _)⟩

/-- All represented inputs with zero long connecting composite satisfy the
strict comparison; no assertion is made for a general finite-page cycle. -/
theorem eq_on_representatives (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) {A B : C}
    (a : A ⟶ HasFunctorialCofiber.cofib
      (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega)))
    (b : B ⟶ adamsTower H.unit (𝟙_ C) t)
    (ha : a ≫ HasFunctorialCofiber.cofibδ
      (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega)) = 0) :
    (a ⊗ₘ b) ≫ stageProjected H.unit r hr s t =
      ((a ≫ projectionNat H.unit (𝟙_ C) s (s + r) (by omega)) ⊗ₘ
        (b ≫ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂)) ≫
        adamsSphereLayerProduct H R s t := by
  obtain ⟨k, hk⟩ := defect_factors H R r hr s t
  have hz : (a ⊗ₘ b) ≫ (HasFunctorialCofiber.cofibδ
      (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega)) ▷
        adamsTower H.unit (𝟙_ C) t) = 0 := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, ha,
      MonoidalPreadditive.zero_tensor]
  have he : (a ⊗ₘ b) ≫ stageProjected H.unit r hr s t =
      (a ⊗ₘ b) ≫ coefficientAction H R r hr s t := by
    apply sub_eq_zero.mp
    rw [← Preadditive.comp_sub, hk, ← Category.assoc (a ⊗ₘ b), hz, Limits.zero_comp]
  simpa only [coefficientAction, ← Category.assoc,
    tensorHom_comp_tensorHom] using he

/-- The strict comparison stated directly with the original long-layer
stage isomorphism and both original projections. All positive lengths,
filtrations, and represented source objects are retained. -/
theorem actual_eq_on_representatives (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) {A B : C}
    (a : A ⟶ adamsLongLayer H.unit (𝟙_ C) r hr s)
    (b : B ⟶ adamsTower H.unit (𝟙_ C) t)
    (ha : a ≫ HasFunctorialCofiber.cofibδ
      (adamsTowerMap H.unit (𝟙_ C) s (s + r) (by omega)) = 0) :
    (a ⊗ₘ b) ≫ (adamsSphereLongLayerStagePairingIso H.unit r hr s t).hom ≫
        adamsLongLayerProjection H.unit (𝟙_ C) r hr ((t + s : ℕ) : ℤ) =
      ((a ≫ adamsLongLayerProjection H.unit (𝟙_ C) r hr s) ⊗ₘ
        (b ≫ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂)) ≫
        adamsSphereLayerProduct H R s t := by
  simpa only [stageProjected_eq_actual H r hr s t,
    projectionNat_eq H.unit (𝟙_ C) r hr s] using
    eq_on_representatives H R r hr s t a b ha

end
end KIP126.Classical.Adams.LongLayerStageComparison
