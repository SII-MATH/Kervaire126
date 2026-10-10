import KIP126.Def.ClassicalAdams.TowerLongLayer.Data
import KIP126.Def.StableHomotopy.Context.CofiberFactorization.Iso.Proofs

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The specified one-step projection is an isomorphism, even though the
weak chosen-cofiber interface does not make it the identity morphism. -/
instance adamsLongLayerProjection_one_isIso (s : ℤ) :
    IsIso (adamsLongLayerProjection unit X 1 le_rfl s) := by
  have ha : IsIso (adamsTowerMapAt unit X (s + 1) (s + 1) le_rfl) := by
    rw [adamsTowerMapAt_self]
    infer_instance
  change IsIso (cofiberFactorizationMap
    (adamsTowerMapAt unit X s (s + 1) (by omega))
    (adamsTowerMapAt unit X s (s + 1) (by omega))
    (adamsTowerMapAt unit X (s + 1) (s + 1) le_rfl) _)
  exact cofiberFactorizationMap_isIso
    (adamsTowerMapAt unit X s (s + 1) (by omega))
    (adamsTowerMapAt unit X s (s + 1) (by omega))
    (adamsTowerMapAt unit X (s + 1) (s + 1) le_rfl) _

end KIP126.Classical.Adams
