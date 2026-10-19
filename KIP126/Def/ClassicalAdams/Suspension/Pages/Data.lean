module

public import KIP126.Def.ClassicalAdams.Suspension.Proofs

@[expose] public section


/-! Actual cycle and quotient-page maps induced by the specified tower
desuspension. Their well-definedness uses the exact-couple I/J/K formulas. -/

namespace KIP126.Classical.Adams.Suspension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {X : C}
  (S : TowerComparison H X)

/-- Restrict the actual first-page desuspension to every finite cycle module. -/
def TowerComparison.desuspendCycles (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycles H.unit (X⟦(1 : ℤ)⟧) r hr s t →ₗ[ℤ]
      adamsCycles H.unit X r hr s (t - 1) :=
  ((S.desuspendFirstPage s t).toIntLinearMap.comp
    (adamsCycles H.unit (X⟦(1 : ℤ)⟧) r hr s t).subtype).codRestrict _
      (fun a => S.desuspendFirstPage_mem_cycles r hr s t a.property)

/-- The induced map on the actual quotient by the preserved boundaries. -/
def TowerComparison.desuspendPage (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsPage H.unit (X⟦(1 : ℤ)⟧) r hr s t →ₗ[ℤ]
      adamsPage H.unit X r hr s (t - 1) :=
  (adamsCycleBoundaries H.unit (X⟦(1 : ℤ)⟧) r hr s t).mapQ
    (adamsCycleBoundaries H.unit X r hr s (t - 1)) (S.desuspendCycles r hr s t) (by
      intro a ha
      exact S.desuspendFirstPage_mem_boundaries r hr s t ha)

end
end KIP126.Classical.Adams.Suspension
