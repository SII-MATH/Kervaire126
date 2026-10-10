import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated] [MonoidalPreadditive C]

/-- Complete the proved first-input pairing square to an isomorphism of
actual layer triangles. The third component is chosen by the triangulated
completion theorem, not postulated. No uniqueness or coherent choice is claimed. -/
def adamsSphereLayerPairingTriangleIso (s t : ℕ) :
    (tensorRight (adamsTower unit (𝟙_ C) t)).mapTriangle.obj
        (adamsLayerTriangle unit (𝟙_ C) s) ≅
      adamsLayerTriangle unit (𝟙_ C) ((t + s : ℕ) : ℤ) :=
  isoTriangleOfIso₁₂ _ _
    ((tensorRight (adamsTower unit (𝟙_ C) t)).map_distinguished _
      (adamsLayerTriangle_distinguished unit (𝟙_ C) s))
    (adamsLayerTriangle_distinguished unit (𝟙_ C) ((t + s : ℕ) : ℤ))
    (adamsTowerSpherePairingIso unit (s + 1) t)
    (adamsTowerSpherePairingIso unit s t) (by
      change (adamsTowerMapAt unit (𝟙_ C) s ((s : ℤ) + 1) (by omega) ▷
          adamsTower unit (𝟙_ C) t) ≫ (adamsTowerSpherePairingIso unit s t).hom =
        (adamsTowerSpherePairingIso unit (s + 1) t).hom ≫
          adamsTowerMapAt unit (𝟙_ C) ((t + s : ℕ) : ℤ)
            (((t + s : ℕ) : ℤ) + 1) (by omega)
      rw [adamsTowerMapAt_nat_succ, adamsTowerMapAt_nat_succ]
      exact (adamsTowerSpherePairingIso_step_left unit s t).symm)

/-- A layer-stage pairing on the existing Adams layers. This is not yet a
layer-layer product or a spectral-sequence multiplication. -/
def adamsSphereLayerPairingIso (s t : ℕ) :
    adamsLayerAt unit (𝟙_ C) s ⊗ adamsTower unit (𝟙_ C) t ≅
      adamsLayerAt unit (𝟙_ C) ((t + s : ℕ) : ℤ) :=
  Triangle.π₃.mapIso (adamsSphereLayerPairingTriangleIso unit s t)

end
end KIP126.Classical.Adams
