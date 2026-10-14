module

public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Composite.Proofs
public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Proofs
public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Homotopy.Data
public import KIP126.Def.StableHomotopy.Context.TensorPairing.Proofs
public import KIP126.Def.ClassicalAdams.TowerLongLayer.Proofs

@[expose] public section


/-! The specified coefficient product preserves actual boundaries when its
second input has zero connecting image. The quotient class of the product
therefore depends only on that connecting image. General finite-page cycles
may have nonzero connecting image; full boundary compatibility is separate. -/
namespace KIP126.Classical.Adams.BoundaryTowerAction

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C]
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

set_option backward.isDefEq.respectTransparency false

theorem tower_kernel_left {H : C} (unit : 𝟙_ C ⟶ H)
    (s z t : ℕ) (h : z ≤ s) {A B : C}
    (a : A ⟶ adamsTower unit (𝟙_ C) s)
    (b : B ⟶ adamsTower unit (𝟙_ C) t)
    (ha : a ≫ adamsTowerMap unit (𝟙_ C) z s h = 0) :
    (a ⊗ₘ b) ≫ (adamsTowerSpherePairingIso unit s t).hom ≫
      adamsTowerMap unit (𝟙_ C) (t + z) (t + s) (by omega) = 0 := by
  rw [adamsTowerSpherePairingIso_map_left unit z s t h]
  have hh : (a ⊗ₘ b) ≫
      (adamsTowerMap unit (𝟙_ C) z s h ▷ adamsTower unit (𝟙_ C) t) = 0 := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, ha]
    simp
  rw [← Category.assoc, hh, Limits.zero_comp]

/-- Full nonnegative filtration range, including clipping of the lower tower
index at zero.  No right-variable tower compatibility is used. -/
theorem tower_boundary_kernel_left {H : C} (unit : 𝟙_ C ⟶ H)
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) {A B : C}
    (a : A ⟶ adamsTower unit (𝟙_ C) s)
    (b : B ⟶ adamsTower unit (𝟙_ C) t)
    (ha : a ≫ adamsTowerMapAt unit (𝟙_ C) ((s : ℤ) - r + 1) s (by omega) = 0) :
    (a ⊗ₘ b) ≫ (adamsTowerSpherePairingIso unit s t).hom ≫
      adamsTowerMapAt unit (𝟙_ C)
        (((t+s : ℕ) : ℤ) - r + 1) ((t+s : ℕ) : ℤ) (by omega) = 0 := by
  let z := ((s : ℤ) - r + 1).toNat
  let w := (((t+s : ℕ) : ℤ) - r + 1).toNat
  have hz : z ≤ s := by dsimp [z]; omega
  have hw : w ≤ t + z := by dsimp [w, z]; omega
  have hha : a ≫ adamsTowerMap unit (𝟙_ C) z s hz = 0 := ha
  have hh := tower_kernel_left unit s z t hz a b hha
  have hc := congrArg (fun f => f ≫
    adamsTowerMap unit (𝟙_ C) w (t+z) hw) hh
  simpa only [Category.assoc, adamsTowerMap_comp, Limits.zero_comp,
    adamsTowerMapAt, adamsTowerAt, Int.toNat_natCast] using hc

variable [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- A genuine boundary in the first slot multiplied by a tower image in the
second slot is again a genuine boundary for the fixed coefficient product.
The second slot is an arbitrary tower class, not an arbitrary finite-page
cycle or long-layer class. -/
theorem coefficient_mem_boundaries (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) (u v : ℤ)
    (a : HomotopyGroup (u-s) (adamsTower H.unit (𝟙_ C) s))
    (b : HomotopyGroup (v-t) (adamsTower H.unit (𝟙_ C) t))
    (ha : adamsI H.unit (𝟙_ C) (u-s) ((s : ℤ)-r+1) s (by omega) a = 0) :
    homotopyTensorPairing (u-s) (v-t) ((u+v)-((t+s : ℕ) : ℤ)) (by omega)
      (adamsSphereLayerProduct H R s t)
      (adamsJ H.unit (𝟙_ C) s u a) (adamsJ H.unit (𝟙_ C) t v b) ∈
        adamsBoundaries H.unit (𝟙_ C) r hr ((t+s : ℕ) : ℤ) (u+v) := by
  let c := homotopyTensorPairing (u-s) (v-t) ((u+v)-((t+s : ℕ) : ℤ)) (by omega)
    (adamsTowerSpherePairingIso H.unit s t).hom a b
  refine ⟨c, ?_, ?_⟩
  · change c ≫ adamsTowerMapAt H.unit (𝟙_ C)
      (((t+s : ℕ) : ℤ)-r+1) ((t+s : ℕ) : ℤ) (by omega) = 0
    have hk := tower_boundary_kernel_left H.unit r hr s t a b ha
    let w := eqToHom (congrArg (Sphere (C := C))
      (by omega : (u+v)-((t+s : ℕ) : ℤ) = (u-s)+(v-t))) ≫
      (sphereTensorIsoFromRightShift (C := C) (u-s) (v-t)).inv
    have hw := congrArg (fun f => w ≫ f) hk
    simpa only [c, w, homotopyTensorPairing, tensorHomPairing_apply, Category.assoc,
      Limits.comp_zero] using hw

  · change c ≫ (adamsLayerTriangle H.unit (𝟙_ C) ((t+s : ℕ) : ℤ)).mor₂ =
      homotopyTensorPairing (u-s) (v-t) ((u+v)-((t+s : ℕ) : ℤ)) (by omega)
        (adamsSphereLayerProduct H R s t)
        (a ≫ (adamsLayerTriangle H.unit (𝟙_ C) s).mor₂)
        (b ≫ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂)
    exact homotopyTensorPairing_naturality _ _ _ _
      (adamsTowerSpherePairingIso H.unit s t).hom
      (adamsSphereLayerProduct H R s t)
      (adamsLayerTriangle H.unit (𝟙_ C) s).mor₂
      (adamsLayerTriangle H.unit (𝟙_ C) t).mor₂
      (adamsLayerTriangle H.unit (𝟙_ C) ((t+s : ℕ) : ℤ)).mor₂
      (adamsSphereLayerProduct_ι H R s t).symm a b

/-- The same actual boundary statement for the public fixed E1 product. -/
theorem e1Product_mem_boundaries (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) (u v : ℤ)
    (a : HomotopyGroup (u-s) (adamsTower H.unit (𝟙_ C) s))
    (b : HomotopyGroup (v-t) (adamsTower H.unit (𝟙_ C) t))
    (ha : adamsI H.unit (𝟙_ C) (u-s) ((s : ℤ)-r+1) s (by omega) a = 0) :
    adamsSphereE1Product H R s t u v
      (adamsJ H.unit (𝟙_ C) s u a) (adamsJ H.unit (𝟙_ C) t v b) ∈
        adamsBoundaries H.unit (𝟙_ C) r hr ((s : ℤ)+(t : ℤ)) (u+v) := by
  have hst : ((t+s : ℕ) : ℤ) = (s : ℤ)+(t : ℤ) := by omega
  have h := coefficient_mem_boundaries H R r hr s t u v a b ha
  have transport (p q : ℤ) (hpq : p = q)
      (hp : (u+v)-p = (u-s)+(v-t)) (hq : (u+v)-q = (u-s)+(v-t))
      (f : adamsLayerAt H.unit (𝟙_ C) s ⊗ adamsLayerAt H.unit (𝟙_ C) t ⟶
        adamsLayerAt H.unit (𝟙_ C) p)
      (hf : homotopyTensorPairing (u-s) (v-t) ((u+v)-p) hp f
        (adamsJ H.unit (𝟙_ C) s u a) (adamsJ H.unit (𝟙_ C) t v b) ∈
          adamsBoundaries H.unit (𝟙_ C) r hr p (u+v)) :
      homotopyTensorPairing (u-s) (v-t) ((u+v)-q) hq
        (f ≫ eqToHom (congrArg (adamsLayerAt H.unit (𝟙_ C)) hpq))
        (adamsJ H.unit (𝟙_ C) s u a) (adamsJ H.unit (𝟙_ C) t v b) ∈
          adamsBoundaries H.unit (𝟙_ C) r hr q (u+v) := by
    subst q
    simpa only [eqToHom_refl, Category.comp_id] using hf
  exact transport _ _ hst (by omega) (by omega) _ h

/-- The fixed coefficient product maps the actual boundary submodule times
`ker K` into the actual boundary submodule, on every positive page. This
uses exactness to obtain tower representatives; no chosen representatives
or boundary-preservation condition are supplied. -/
theorem boundary_mul_kerK (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) (u v : ℤ)
    (x : adamsE1 H.unit (𝟙_ C) s u)
    (y : adamsE1 H.unit (𝟙_ C) t v)
    (hx : x ∈ adamsBoundaries H.unit (𝟙_ C) r hr s u)
    (hy : adamsK H.unit (𝟙_ C) t v y = 0) :
    adamsSphereE1Product H R s t u v x y ∈
      adamsBoundaries H.unit (𝟙_ C) r hr ((s : ℤ)+(t : ℤ)) (u+v) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb⟩ := (les_homotopy_exact_g
    (HoCofiberSequence.ofMorphism
      (adamsTowerMapAt H.unit (𝟙_ C) t ((t : ℤ)+1) (by omega)))
    (v-t) y).mp hy
  change adamsJ H.unit (𝟙_ C) t v b = y at hb
  rw [← hb]
  exact e1Product_mem_boundaries H R r hr s t u v a b ha

/-- A useful long-layer specialization. The zero long connecting image is
an explicit condition stronger than merely representing a finite-page cycle. -/
theorem boundary_mul_longLayer_zeroK (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) (u v : ℤ)
    (x : adamsE1 H.unit (𝟙_ C) s u)
    (y : HomotopyGroup (v-t) (adamsLongLayer H.unit (𝟙_ C) r hr t))
    (hx : x ∈ adamsBoundaries H.unit (𝟙_ C) r hr s u)
    (hy : adamsLongLayerK H.unit (𝟙_ C) r hr t v y = 0) :
    adamsSphereE1Product H R s t u v x
      (adamsLongLayerToE1 H.unit (𝟙_ C) r hr t v y) ∈
        adamsBoundaries H.unit (𝟙_ C) r hr ((s : ℤ)+(t : ℤ)) (u+v) := by
  apply boundary_mul_kerK H R r hr s t u v x _ hx
  rw [← adamsLongLayerK_lift, hy, map_zero]

/-- For a fixed genuine boundary input, the output modulo genuine boundaries
only depends on the other input's connecting image. This removes the
choice of a tower-image correction; it does not assert that the remaining
connecting-image obstruction vanishes. -/
theorem boundary_mul_sameK (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) (u v : ℤ)
    (x : adamsE1 H.unit (𝟙_ C) s u)
    (y y' : adamsE1 H.unit (𝟙_ C) t v)
    (hx : x ∈ adamsBoundaries H.unit (𝟙_ C) r hr s u)
    (hy : adamsK H.unit (𝟙_ C) t v y = adamsK H.unit (𝟙_ C) t v y') :
    adamsSphereE1Product H R s t u v x y -
        adamsSphereE1Product H R s t u v x y' ∈
      adamsBoundaries H.unit (𝟙_ C) r hr ((s : ℤ)+(t : ℤ)) (u+v) := by
  have hk : adamsK H.unit (𝟙_ C) t v (y-y') = 0 := by
    rw [map_sub, hy, sub_self]
  simpa only [map_sub] using boundary_mul_kerK H R r hr s t u v x (y-y') hx hk

end
end KIP126.Classical.Adams.BoundaryTowerAction
