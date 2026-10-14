module

public import KIP126.Def.ClassicalAdams.Suspension.Construction.Proofs

@[expose] public section


/-! Assemble the existing TowerComparison without adding a compatibility input. -/

namespace KIP126.Classical.Adams.Suspension.Construction

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- Complete full integer tower data by the actual cofiber layer comparisons. -/
def towerComparisonOfTower (H : Mod2EilenbergMacLane (C := C)) (X : C)
    (tower : ∀ s : ℤ, adamsTowerAt H.unit (X⟦(1 : ℤ)⟧) s ≅
      (adamsTowerAt H.unit X s)⟦(1 : ℤ)⟧)
    (hzero : tower 0 = Iso.refl (X⟦(1 : ℤ)⟧))
    (hcomm : ∀ (s t : ℤ) (hst : s ≤ t),
      (tower t).hom ≫ (adamsTowerMapAt H.unit X s t hst)⟦(1 : ℤ)⟧' =
        adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s t hst ≫ (tower s).hom) :
    TowerComparison H X where
  tower := tower
  tower_zero := hzero
  tower_comm := hcomm
  layer s := cofiberIso
    (adamsTowerMapAt H.unit X s (s + 1) (by omega))
    (adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s (s + 1) (by omega))
    (tower (s + 1)) (tower s) (hcomm s (s + 1) (by omega)).symm
  layer_inclusion s := cofiberIso_inclusion _ _ _ _ _
  layer_connecting s := cofiberIso_connecting _ _ _ _ _

variable (H : Mod2EilenbergMacLane (C := C))
  [(tensorLeft H.HF2).CommShift ℤ] [(mod2UnitNatTrans H).CommShift ℤ]

/-- A suspension comparison for every object of the same category. All fields
are constructed from the specified tensor/unit shift structures and cofibers. -/
def towerComparison (X : C) : TowerComparison H X :=
  towerComparisonOfTower H X (fun s => towerIso H X s.toNat) rfl
    (towerIso_mapAt H X)

end
end KIP126.Classical.Adams.Suspension.Construction
