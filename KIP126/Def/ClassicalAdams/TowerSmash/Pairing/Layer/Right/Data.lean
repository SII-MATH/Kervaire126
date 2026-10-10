import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Layer.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Transport.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated] [MonoidalPreadditive C]
  [∀ Y : C, (tensorLeft Y).CommShift ℤ]
  [∀ Y : C, (tensorLeft Y).IsTriangulated]

/-- Complete the proved second-input square using left tensor exactness.
This choice is not asserted to be coherent with the first-input completion. -/
def adamsSphereTowerLayerPairingTriangleIso (h : UnitFiberInclusionCommutes unit)
    (s t : ℕ) :
    (tensorLeft (adamsTower unit (𝟙_ C) s)).mapTriangle.obj
        (adamsLayerTriangle unit (𝟙_ C) t) ≅
      adamsLayerTriangle unit (𝟙_ C) ((t + s : ℕ) : ℤ) :=
  isoTriangleOfIso₁₂ _ _
    ((tensorLeft (adamsTower unit (𝟙_ C) s)).map_distinguished _
      (adamsLayerTriangle_distinguished unit (𝟙_ C) t))
    (adamsLayerTriangle_distinguished unit (𝟙_ C) ((t + s : ℕ) : ℤ))
    (adamsTowerSpherePairingIso unit s (t + 1) ≪≫
      eqToIso (congrArg (adamsTower unit (𝟙_ C)) (Nat.succ_add t s)))
    (adamsTowerSpherePairingIso unit s t) (by
      change (adamsTower unit (𝟙_ C) s ◁
          adamsTowerMapAt unit (𝟙_ C) t ((t : ℤ) + 1) (by omega)) ≫
          (adamsTowerSpherePairingIso unit s t).hom =
        adamsTowerSpherePairingNextRight unit s t ≫
          adamsTowerMapAt unit (𝟙_ C) ((t + s : ℕ) : ℤ)
            (((t + s : ℕ) : ℤ) + 1) (by omega)
      rw [adamsTowerMapAt_nat_succ, adamsTowerMapAt_nat_succ]
      exact (adamsTowerSpherePairingIso_step_right unit h s t).symm)

/-- A stage-layer pairing on the existing layers, conditional on the
two-factor equality. A layer-layer multiplication is not defined here. -/
def adamsSphereTowerLayerPairingIso (h : UnitFiberInclusionCommutes unit) (s t : ℕ) :
    adamsTower unit (𝟙_ C) s ⊗ adamsLayerAt unit (𝟙_ C) t ≅
      adamsLayerAt unit (𝟙_ C) ((t + s : ℕ) : ℤ) :=
  Triangle.π₃.mapIso (adamsSphereTowerLayerPairingTriangleIso unit h s t)

end
end KIP126.Classical.Adams
