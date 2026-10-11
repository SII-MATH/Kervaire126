module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.BoundaryTower.Proofs
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section


namespace KIP126.Classical.Adams.BoundaryConnectingAction
noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
set_option backward.isDefEq.respectTransparency false

/-- Exactness in the actual long triangle, with no finite-page representative
or coordinate assumption. -/
theorem longK_range {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
    (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    LinearMap.range (adamsLongLayerK unit X r hr s t) =
      LinearMap.ker (adamsI unit X (t-s-1) s (s+r) (by omega)) := by
  ext z
  exact (lesHomotopyExactH
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s+r) (by omega)))
    (t-s) z).symm

/-- The residual connecting-image domain is exactly an intersection of
actual tower-map kernel and range. Both inclusions use the original long
and one-step triangles; no candidate coverage or page product is input. -/
theorem projectedLongK_range {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
    (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    LinearMap.range ((adamsK unit X s t).comp (adamsLongLayerToE1 unit X r hr s t)) =
      LinearMap.ker (adamsI unit X (t-s-1) s (s+1) (by omega)) ⊓
      LinearMap.range (adamsI unit X (t-s-1) (s+1) (s+r) (by omega)) := by
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    constructor
    · change adamsI unit X (t-s-1) s (s+1) (by omega)
        (adamsK unit X s t (adamsLongLayerToE1 unit X r hr s t b)) = 0
      exact (lesHomotopyExactH
        (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s+1) (by omega)))
        (t-s) _).mpr ⟨_, rfl⟩
    · exact ⟨adamsLongLayerK unit X r hr s t b, adamsLongLayerK_lift unit X r hr s t b⟩
  · rintro ⟨hz, a, ha⟩
    have hia : adamsI unit X (t-s-1) s (s+r) (by omega) a = 0 := by
      rw [← adamsI_comp unit X (t-s-1) s (s+1) (s+r) (by omega) (by omega), ha]
      exact hz
    obtain ⟨b, hb⟩ := (lesHomotopyExactH
      (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s+r) (by omega)))
      (t-s) a).mp hia
    change adamsLongLayerK unit X r hr s t b = a at hb
    refine ⟨b, ?_⟩
    change adamsK unit X s t (adamsLongLayerToE1 unit X r hr s t b) = z
    rw [← adamsLongLayerK_lift, hb, ha]

variable [BraidedCategory C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- For a genuine boundary x, its fixed coefficient product with an arbitrary
long-layer representative descends uniquely to the actual projected
connecting-image group. The codomain is the ambient E1/B_r quotient, NOT
an assumed actual page: cycle closure and vanishing are not asserted. -/
theorem existsUnique_boundary_action (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) (u v : ℤ)
    (x : adamsE1 H.unit (𝟙_ C) s u)
    (hx : x ∈ adamsBoundaries H.unit (𝟙_ C) r hr s u) :
    let k := (adamsK H.unit (𝟙_ C) t v).comp
      (adamsLongLayerToE1 H.unit (𝟙_ C) r hr t v)
    let targetB := adamsBoundaries H.unit (𝟙_ C) r hr ((s : ℤ)+(t : ℤ)) (u+v)
    ∃! f : LinearMap.range k →ₗ[ℤ]
        (adamsE1 H.unit (𝟙_ C) ((s : ℤ)+(t : ℤ)) (u+v) ⧸ targetB),
      ∀ b, f ⟨k b, ⟨b, rfl⟩⟩ = targetB.mkQ
        (adamsSphereE1Product H R s t u v x
          (adamsLongLayerToE1 H.unit (𝟙_ C) r hr t v b)) := by
  dsimp only
  let k := (adamsK H.unit (𝟙_ C) t v).comp
    (adamsLongLayerToE1 H.unit (𝟙_ C) r hr t v)
  let targetB := adamsBoundaries H.unit (𝟙_ C) r hr ((s : ℤ)+(t : ℤ)) (u+v)
  let g := targetB.mkQ.comp ((adamsSphereE1Product H R s t u v x).comp
    (adamsLongLayerToE1 H.unit (𝟙_ C) r hr t v))
  have hkg : LinearMap.ker k ≤ LinearMap.ker g := by
    intro b hb
    change targetB.mkQ _ = 0
    apply (Submodule.Quotient.mk_eq_zero targetB).mpr
    exact BoundaryTowerAction.boundary_mul_kerK H R r hr s t u v x _ hx hb
  let f := ((LinearMap.ker k).liftQ g hkg).comp k.quotKerEquivRange.symm.toLinearMap
  have hf (b) : f ⟨k b, ⟨b, rfl⟩⟩ = g b := by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  apply LinearMap.ext
  rintro ⟨z, b, rfl⟩
  exact (hf' b).trans (hf b).symm

/-- Long representatives whose connecting images agree after the actual
r-1 tower maps give the same product modulo B_r. This includes arbitrary
nonzero long connecting images, unlike a zero-connecting restriction. -/
theorem boundary_mul_same_projected_longK
    (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) (u v : ℤ)
    (x : adamsE1 H.unit (𝟙_ C) s u)
    (hx : x ∈ adamsBoundaries H.unit (𝟙_ C) r hr s u)
    (b b' : HomotopyGroup (v-t) (adamsLongLayer H.unit (𝟙_ C) r hr t))
    (hb : adamsI H.unit (𝟙_ C) (v-t-1) ((t:ℤ)+1) ((t:ℤ)+r) (by omega)
        (adamsLongLayerK H.unit (𝟙_ C) r hr t v b) =
      adamsI H.unit (𝟙_ C) (v-t-1) ((t:ℤ)+1) ((t:ℤ)+r) (by omega)
        (adamsLongLayerK H.unit (𝟙_ C) r hr t v b')) :
    adamsSphereE1Product H R s t u v x
        (adamsLongLayerToE1 H.unit (𝟙_ C) r hr t v b) -
      adamsSphereE1Product H R s t u v x
        (adamsLongLayerToE1 H.unit (𝟙_ C) r hr t v b') ∈
      adamsBoundaries H.unit (𝟙_ C) r hr ((s : ℤ)+(t : ℤ)) (u+v) := by
  apply BoundaryTowerAction.boundary_mul_sameK H R r hr s t u v x _ _ hx
  simpa only [adamsLongLayerK_lift] using hb

end
end KIP126.Classical.Adams.BoundaryConnectingAction
