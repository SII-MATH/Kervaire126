import KIP126.Def.StableHomotopy.Cohomology.Connecting.Data
import KIP126.Def.StableHomotopy.Cohomology.Coaction.Unit.Proofs

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- Inner-unit insertion commutes with the homology boundary of every
distinguished triangle, derived from the unit's shift-compatible naturality. -/
theorem mod2CoactionMap_connecting (T : HoCofiberSequence (C := C)) (n : ℤ)
    (x : Mod2Homology H n T.Z) :
    mod2HomologyConnecting H (T.map (tensorLeft H.HF2)) n (mod2CoactionMap H T.Z n x) =
      mod2CoactionMap H T.X (n - 1) (mod2HomologyConnecting H T n x) := by
  let F := tensorLeft H.HF2
  let α : F ⟶ F ⋙ F := F.leftUnitor.inv ≫ Functor.whiskerRight (mod2UnitNatTrans H) F
  have h := connectingHomomorphism_map_naturality T F (F ⋙ F) α n x
  change connectingHomomorphism ((T.map F).map F) n _ = _
  rw [connectingHomomorphism_map_comp]
  convert! h using 1 <;>
    simp [α, F, mod2CoactionMap, mod2Coaction, mod2UnitNatTrans, mod2HomologyConnecting] <;> rfl

/-- Outer-unit insertion satisfies the same boundary naturality. -/
theorem mod2OuterUnitMap_connecting (T : HoCofiberSequence (C := C)) (n : ℤ)
    (x : Mod2Homology H n T.Z) :
    mod2HomologyConnecting H (T.map (tensorLeft H.HF2)) n (mod2OuterUnitMap H T.Z n x) =
      mod2OuterUnitMap H T.X (n - 1) (mod2HomologyConnecting H T n x) := by
  let F := tensorLeft H.HF2
  let α : F ⟶ F ⋙ F := F.rightUnitor.inv ≫ Functor.whiskerLeft F (mod2UnitNatTrans H)
  have h := connectingHomomorphism_map_naturality T F (F ⋙ F) α n x
  change connectingHomomorphism ((T.map F).map F) n _ = _
  rw [connectingHomomorphism_map_comp]
  convert! h using 1 <;>
    simp [α, F, mod2OuterUnitMap, mod2UnitNatTrans, mod2HomologyConnecting] <;> rfl

end KIP126.StableHomotopy.Cohomology
