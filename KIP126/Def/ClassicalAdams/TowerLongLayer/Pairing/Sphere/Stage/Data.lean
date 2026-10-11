module

public import KIP126.Def.ClassicalAdams.TowerLongLayer.Data
public import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Transport.Composite.Proofs

@[expose] public section


namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated] [MonoidalPreadditive C]

/-- Complete the already proved arbitrary-length tower square after tensoring
by an actual sphere-tower stage. This is an actual triangle isomorphism, not
an input pairing, and the construction applies in particular to `r = 4`.
No coherence between independently completed triangles is asserted. -/
def adamsSphereLongLayerStageTriangleIso (r : ℕ) (s t : ℕ) :
    (tensorRight (adamsTower unit (𝟙_ C) t)).mapTriangle.obj
      (Triangle.mk (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega))
        (HasFunctorialCofiber.cofibι (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega)))
        (HasFunctorialCofiber.cofibδ (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega)))) ≅
      Triangle.mk (adamsTowerMap unit (𝟙_ C) (t + s) (t + (s + r)) (by omega))
        (HasFunctorialCofiber.cofibι (adamsTowerMap unit (𝟙_ C) (t + s) (t + (s + r)) (by omega)))
        (HasFunctorialCofiber.cofibδ (adamsTowerMap unit (𝟙_ C) (t + s) (t + (s + r)) (by omega))) :=
  isoTriangleOfIso₁₂ _ _
    ((tensorRight (adamsTower unit (𝟙_ C) t)).map_distinguished _
      (HasFunctorialCofiber.cofib_distinguished _))
    (HasFunctorialCofiber.cofib_distinguished _)
    (adamsTowerSpherePairingIso unit (s + r) t)
    (adamsTowerSpherePairingIso unit s t)
    (adamsTowerSpherePairingIso_map_left unit s (s + r) t (by omega)).symm

/-- A long layer can genuinely be multiplied by a tower-stage representative.
This is the one-sided geometric part needed for actions of homotopy classes
with actual filtered lifts. It is not a product of two long layers. -/
def adamsSphereLongLayerStagePairingIso (r : ℕ) (hr : 1 ≤ r) (s t : ℕ) :
    adamsLongLayer unit (𝟙_ C) r hr s ⊗ adamsTower unit (𝟙_ C) t ≅
      adamsLongLayer unit (𝟙_ C) r hr ((t + s : ℕ) : ℤ) := by
  let e := Triangle.π₃.mapIso (adamsSphereLongLayerStageTriangleIso unit r s t)
  change HasFunctorialCofiber.cofib (adamsTowerMap unit (𝟙_ C) s (s + r) (by omega)) ⊗
    adamsTower unit (𝟙_ C) t ≅
      HasFunctorialCofiber.cofib (adamsTowerMap unit (𝟙_ C) (t + s) (t + (s + r)) (by omega)) at e
  convert e using 1 <;> simp only [adamsLongLayer, adamsTowerMapAt, adamsTowerAt,
    ← Int.natCast_add, Int.toNat_natCast]
  all_goals congr 1
  all_goals simp only [adamsTowerMap, eqToHom_comp_heq_iff, Nat.add_assoc]
  all_goals symm
  all_goals rw [eqToHom_comp_heq_iff]
  all_goals (congr 1; omega)

end
end KIP126.Classical.Adams
