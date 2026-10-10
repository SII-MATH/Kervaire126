import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Multiplication.Proofs
import KIP126.Def.ClassicalAdams.TowerLayer.Connecting.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- The product of two representatives whose actual connecting maps vanish
again has zero connecting map. Exactness supplies lifts to the existing tower;
the unit restriction of the specified product multiplies those lifts.
No compatibility of the two tensor suspension structures is required. -/
theorem adamsSphereLayerProduct_comp_δ_eq_zero (s t : ℕ) {A B : C}
    (x : A ⟶ adamsLayerAt H.unit (𝟙_ C) s)
    (y : B ⟶ adamsLayerAt H.unit (𝟙_ C) t)
    (hx : x ≫ (adamsLayerTriangle H.unit (𝟙_ C) s).mor₃ = 0)
    (hy : y ≫ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃ = 0) :
    ((x ⊗ₘ y) ≫ adamsSphereLayerProduct H R s t) ≫
      (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃ = 0 := by
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₃ _
    (adamsLayerTriangle_distinguished H.unit (𝟙_ C) s) x hx
  obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₃ _
    (adamsLayerTriangle_distinguished H.unit (𝟙_ C) t) y hy
  have ht {U V W X Y Z : C} (a : U ⟶ V) (b : W ⟶ X)
      (q : V ⟶ Y) (q' : X ⟶ Z) :
      ((a ≫ q) ⊗ₘ (b ≫ q')) = (a ⊗ₘ b) ≫ (q ⊗ₘ q') :=
    (tensorHom_comp_tensorHom _ _ _ _).symm
  have hp : (x ⊗ₘ y) ≫ adamsSphereLayerProduct H R s t =
      ((a ⊗ₘ b) ≫ (adamsTowerSpherePairingIso H.unit s t).hom) ≫
        (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₂ := by
    rw [ha, hb]
    exact (congrArg (fun f => f ≫ adamsSphereLayerProduct H R s t)
      (ht a b _ _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (fun f => (a ⊗ₘ b) ≫ f)
          (adamsSphereLayerProduct_ι H R s t)).trans (Category.assoc _ _ _).symm))
  exact (congrArg (fun f => f ≫
    (adamsLayerTriangle H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)).mor₃) hp).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun f =>
        ((a ⊗ₘ b) ≫ (adamsTowerSpherePairingIso H.unit s t).hom) ≫ f)
          (comp_distTriang_mor_zero₂₃ _
            (adamsLayerTriangle_distinguished H.unit (𝟙_ C) ((t + s : ℕ) : ℤ)))).trans
              Limits.comp_zero))

/-- After any specified sphere precomposition, the preceding product is a
cycle in the actual internal tower construction on every finite page.
This does not assert nonzero survival or define the graded sphere product. -/
theorem adamsSphereLayerProduct_mem_cycles (r : ℕ) (hr : 1 ≤ r) (s t : ℕ)
    (u : ℤ) {A B : C} (w : Sphere (u - ((t + s : ℕ) : ℤ)) ⟶ A ⊗ B)
    (x : A ⟶ adamsLayerAt H.unit (𝟙_ C) s)
    (y : B ⟶ adamsLayerAt H.unit (𝟙_ C) t)
    (hx : x ≫ (adamsLayerTriangle H.unit (𝟙_ C) s).mor₃ = 0)
    (hy : y ≫ (adamsLayerTriangle H.unit (𝟙_ C) t).mor₃ = 0) :
    w ≫ ((x ⊗ₘ y) ≫ adamsSphereLayerProduct H R s t) ∈
      adamsCycles H.unit (𝟙_ C) r hr ((t + s : ℕ) : ℤ) u := by
  apply adamsCycles_mem_of_comp_δ_eq_zero
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => w ≫ f)
      (adamsSphereLayerProduct_comp_δ_eq_zero H R s t x y hx hy)).trans Limits.comp_zero)

end
end KIP126.Classical.Adams
