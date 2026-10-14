module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Stage.Data
public import KIP126.Def.StableHomotopy.Context.TensorPairing.Proofs
public import KIP126.Def.StableHomotopy.Context.Connecting.Desuspension.Proofs
public import KIP126.Def.StableHomotopy.Context.Suspension.Proofs
public import KIP126.Def.ClassicalAdams.TowerLongLayer.Page.Proofs

@[expose] public section


namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated] [MonoidalPreadditive C]

@[simp] theorem adamsSphereLongLayerStageTriangleIso_hom₁ (r s t : ℕ) :
    (adamsSphereLongLayerStageTriangleIso unit r s t).hom.hom₁ =
      (adamsTowerSpherePairingIso unit (s + r) t).hom := by
  simp only [adamsSphereLongLayerStageTriangleIso, isoTriangleOfIso₁₂_hom_hom₁]

@[simp] theorem adamsSphereLongLayerStageTriangleIso_hom₂ (r s t : ℕ) :
    (adamsSphereLongLayerStageTriangleIso unit r s t).hom.hom₂ =
      (adamsTowerSpherePairingIso unit s t).hom := by
  simp only [adamsSphereLongLayerStageTriangleIso, isoTriangleOfIso₁₂_hom_hom₂]

/-- Multiplication of a tower-to-long-layer image is exactly the constructed
sphere-tower multiplication followed by the actual cofiber inclusion. -/
theorem adamsSphereLongLayerStageTriangleIso_ι (r s t : ℕ) :
    (HasFunctorialCofiber.cofibι (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega)) ▷
        adamsTower unit (𝟙_ C) t) ≫
      (adamsSphereLongLayerStageTriangleIso unit r s t).hom.hom₃ =
    (adamsTowerSpherePairingIso unit s t).hom ≫
      HasFunctorialCofiber.cofibι
        (adamsTowerMap unit (𝟙_ C) (t + s) (t + (s + r)) (by omega)) := by
  have h := (adamsSphereLongLayerStageTriangleIso unit r s t).hom.comm₂
  rw [adamsSphereLongLayerStageTriangleIso_hom₂] at h
  exact h

/-- The connecting map of the constructed product is the first connecting
map tensored with the tower-stage class. This genuine one-sided formula is
valid at every length, including four; it assumes no page derivation law. -/
theorem adamsSphereLongLayerStageTriangleIso_δ (r s t : ℕ) :
    (adamsSphereLongLayerStageTriangleIso unit r s t).hom.hom₃ ≫
      HasFunctorialCofiber.cofibδ
        (adamsTowerMap unit (𝟙_ C) (t + s) (t + (s + r)) (by omega)) =
    (HasFunctorialCofiber.cofibδ (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega)) ▷
      adamsTower unit (𝟙_ C) t) ≫
      (Functor.commShiftIso (tensorRight (adamsTower unit (𝟙_ C) t)) (1 : ℤ)).hom.app
        (adamsTower unit (𝟙_ C) (s + r)) ≫
      (adamsTowerSpherePairingIso unit (s + r) t).hom⟦(1 : ℤ)⟧' := by
  have h := (adamsSphereLongLayerStageTriangleIso unit r s t).hom.comm₃
  rw [adamsSphereLongLayerStageTriangleIso_hom₁] at h
  exact h.symm.trans (Category.assoc _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The actual connecting homomorphism of a represented long-layer product
is computed by the previously proved spectrum-level formula. No interpretation
of a database row or assumed higher-page multiplication occurs here. -/
theorem adamsSphereLongLayerStageTriangleIso_connecting (r s t : ℕ) (n m : ℤ)
    (a : HomotopyGroup n
      (HasFunctorialCofiber.cofib (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega))))
    (b : HomotopyGroup m (adamsTower unit (𝟙_ C) t)) :
    connectingHomomorphism
      (HoCofiberSequence.ofMorphism
        (adamsTowerMap unit (𝟙_ C) (t + s) (t + (s + r)) (by omega))) (n + m)
      (homotopyTensorPairing n m (n + m) rfl
        (adamsSphereLongLayerStageTriangleIso unit r s t).hom.hom₃ a b) =
    homotopyDesuspend (adamsTower unit (𝟙_ C) (t + (s + r))) (n + m)
      (homotopyTensorPairing n m (n + m) rfl
        ((HasFunctorialCofiber.cofibδ (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega)) ▷
            adamsTower unit (𝟙_ C) t) ≫
          (Functor.commShiftIso (tensorRight (adamsTower unit (𝟙_ C) t)) (1 : ℤ)).hom.app
            (adamsTower unit (𝟙_ C) (s + r)) ≫
          (adamsTowerSpherePairingIso unit (s + r) t).hom⟦(1 : ℤ)⟧') a b) := by
  rw [connectingHomomorphism_eq_desuspend]
  congr 1
  simp only [HoCofiberSequence.ofMorphism, homotopyTensorPairing, tensorHomPairing_apply, Category.assoc,
    adamsSphereLongLayerStageTriangleIso_δ]

set_option backward.isDefEq.respectTransparency false

/-- The actual stage pairing preserves the kernel of the long connecting
homomorphism in its first input, at every length and homotopy degree. -/
theorem adamsSphereLongLayerStageTriangleIso_connecting_eq_zero
    (r s t : ℕ) (n m : ℤ)
    (a : HomotopyGroup n
      (HasFunctorialCofiber.cofib (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega))))
    (b : HomotopyGroup m (adamsTower unit (𝟙_ C) t))
    (ha : connectingHomomorphism
      (HoCofiberSequence.ofMorphism (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega)))
      n a = 0) :
    connectingHomomorphism
      (HoCofiberSequence.ofMorphism
        (adamsTowerMap unit (𝟙_ C) (t + s) (t + (s + r)) (by omega))) (n + m)
      (homotopyTensorPairing n m (n + m) rfl
        (adamsSphereLongLayerStageTriangleIso unit r s t).hom.hom₃ a b) = 0 := by
  have ha' : a ≫ HasFunctorialCofiber.cofibδ
      (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega)) = 0 := by
    apply (homotopyDesuspend_bijective (adamsTower unit (𝟙_ C) (s + r)) n).injective
    rw [map_zero]
    exact (connectingHomomorphism_eq_desuspend (HoCofiberSequence.ofMorphism
      (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega))) n a).symm.trans ha
  rw [adamsSphereLongLayerStageTriangleIso_connecting]
  have hz : homotopyTensorPairing n m (n + m) rfl
      ((HasFunctorialCofiber.cofibδ
          (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega)) ▷
          adamsTower unit (𝟙_ C) t) ≫
        (Functor.commShiftIso (tensorRight (adamsTower unit (𝟙_ C) t))
          (1 : ℤ)).hom.app (adamsTower unit (𝟙_ C) (s + r)) ≫
        (adamsTowerSpherePairingIso unit (s + r) t).hom⟦(1 : ℤ)⟧') a b = 0 := by
    simp only [homotopyTensorPairing, tensorHomPairing_apply, Category.assoc]
    rw [← Category.assoc (a ⊗ₘ b)]
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, ha',
      MonoidalPreadditive.zero_tensor, Limits.zero_comp, Limits.comp_zero]
  simp only [hz, map_zero]

omit [∀ Y : C, (tensorRight Y).IsTriangulated] in
private theorem stageConnecting_eq_zero_transport
    {X X' Y A B : C} {f : X ⟶ Y} {f' : X' ⟶ Y}
    {e : A ⊗ B ≅ HasFunctorialCofiber.cofib f}
    {e' : A ⊗ B ≅ HasFunctorialCofiber.cofib f'}
    (hX : X = X') (hf : HEq f f') (he : HEq e e')
    (n m : ℤ) (a : HomotopyGroup n A) (b : HomotopyGroup m B)
    (h : connectingHomomorphism (HoCofiberSequence.ofMorphism f) (n + m)
      (homotopyTensorPairing n m (n + m) rfl e.hom a b) = 0) :
    connectingHomomorphism (HoCofiberSequence.ofMorphism f') (n + m)
      (homotopyTensorPairing n m (n + m) rfl e'.hom a b) = 0 := by
  subst X'
  cases hf
  cases he
  exact h

/-- The long-layer stage pairing preserves zero connecting classes after
its genuine integer-stage transports. -/
theorem adamsSphereLongLayerStagePairingIso_connecting_eq_zero
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) (n m k : ℤ) (hk : k = n + m)
    (a : HomotopyGroup n (adamsLongLayer unit (𝟙_ C) r hr s))
    (b : HomotopyGroup m (adamsTower unit (𝟙_ C) t))
    (ha : connectingHomomorphism (HoCofiberSequence.ofMorphism
      (adamsTowerMapAt unit (𝟙_ C) s ((s : ℤ) + r) (by omega))) n a = 0) :
    connectingHomomorphism (HoCofiberSequence.ofMorphism
      (adamsTowerMapAt unit (𝟙_ C) ((t + s : ℕ) : ℤ)
        (((t + s : ℕ) : ℤ) + r) (by omega))) k
      (homotopyTensorPairing n m k hk
        (adamsSphereLongLayerStagePairingIso unit r hr s t).hom a b) = 0 := by
  subst k
  apply stageConnecting_eq_zero_transport
    (e := Triangle.π₃.mapIso (adamsSphereLongLayerStageTriangleIso unit r s t))
    (f := adamsTowerMap unit (𝟙_ C) (t + s) (t + (s + r)) (by omega))
  · simp only [adamsTowerAt, ← Int.natCast_add, Int.toNat_natCast, Nat.add_assoc]
  · simp only [adamsTowerMapAt, ← Int.natCast_add, Int.toNat_natCast]
    simp only [adamsTowerMap, eqToHom_comp_heq_iff]
    symm
    rw [eqToHom_comp_heq_iff]
    congr 1
    omega
  · unfold adamsSphereLongLayerStagePairingIso
    exact (cast_heq _ _).symm
  · exact adamsSphereLongLayerStageTriangleIso_connecting_eq_zero unit r s t n m a b ha

/-- A genuine tower-stage multiple of a long-layer class with zero connecting
homomorphism has zero actual page differential. This one-sided result uses
no multiplication of two long layers or higher-page Leibniz assumption. -/
theorem adamsDifferential_longLayerStagePairing_eq_zero
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) (n m : ℤ)
    (a : HomotopyGroup n (adamsLongLayer unit (𝟙_ C) r hr s))
    (b : HomotopyGroup m (adamsTower unit (𝟙_ C) t))
    (ha : connectingHomomorphism (HoCofiberSequence.ofMorphism
      (adamsTowerMapAt unit (𝟙_ C) s ((s : ℤ) + r) (by omega))) n a = 0) :
    adamsDifferential unit (𝟙_ C) r hr ((t + s : ℕ) : ℤ)
      (n + m + ((t + s : ℕ) : ℤ))
      (adamsLongLayerToPage unit (𝟙_ C) r hr ((t + s : ℕ) : ℤ)
        (n + m + ((t + s : ℕ) : ℤ))
        (homotopyTensorPairing n m
          (n + m + ((t + s : ℕ) : ℤ) - ((t + s : ℕ) : ℤ)) (by omega)
          (adamsSphereLongLayerStagePairingIso unit r hr s t).hom a b)) = 0 := by
  rw [adamsDifferential_longLayerToPage]
  have hz : adamsLongLayerK unit (𝟙_ C) r hr ((t + s : ℕ) : ℤ)
      (n + m + ((t + s : ℕ) : ℤ))
      (homotopyTensorPairing n m
        (n + m + ((t + s : ℕ) : ℤ) - ((t + s : ℕ) : ℤ)) (by omega)
        (adamsSphereLongLayerStagePairingIso unit r hr s t).hom a b) = 0 :=
    adamsSphereLongLayerStagePairingIso_connecting_eq_zero unit r hr s t n m _
      (by omega) a b ha
  rw [hz, homotopyGroup_cast_zero (by omega), map_zero]

end
end KIP126.Classical.Adams
