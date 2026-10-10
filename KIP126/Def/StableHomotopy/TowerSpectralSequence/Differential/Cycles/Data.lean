import KIP126.Def.StableHomotopy.TowerSpectralSequence.Differential.Value.Proofs

/-! Bundle the specified quotient-valued differential formula on cycles
using its separately stated linearity properties. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

/-- The actual J(lift(K(x))) value as an integer-linear map on cycles. -/
noncomputable def differentialOnCycles (q : ℕ) (hq : 1 ≤ q) (k n : ℤ) :
    cycles T P q hq k n →ₗ[ℤ] page T P q hq (k + q) (n - 1) where
  toFun := differentialValue T P q hq k n
  map_add' := differentialValue_add T P q hq k n
  map_smul' := differentialValue_smul T P q hq k n

end KIP126.StableHomotopy.TowerSpectralSequence
