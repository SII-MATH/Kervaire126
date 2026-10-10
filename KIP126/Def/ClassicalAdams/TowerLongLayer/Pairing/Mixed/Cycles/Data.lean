import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Mixed.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X Y Z : C}
  {r : ℕ} {hr : 1 ≤ r} {p q : ℤ × ℤ}
  (P : MixedAdamsLongLayerPairing unit X Y Z r hr p q)

/-- Corestrict the supplied first-page pairing to the actual cycle modules,
using closure proved from its long-layer lift. -/
def MixedAdamsLongLayerPairing.onCycles (hP : P.ProjectionCompatible) :
    adamsCycles unit X r hr p.1 p.2 →ₗ[ℤ]
      adamsCycles unit Y r hr q.1 q.2 →ₗ[ℤ]
        adamsCycles unit Z r hr (p.1 + q.1) (p.2 + q.2) where
  toFun x := ((P.first x.val).comp (adamsCycles unit Y r hr q.1 q.2).subtype).codRestrict _
    (fun y => P.mem_cycles hP x.val x.property y.val y.property)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact LinearMap.congr_fun (P.first.map_add x.val y.val) z.val
  map_smul' a x := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact LinearMap.congr_fun (P.first.map_smul a x.val) z.val

/-- Pair cycle representatives, then project only the output to its page. -/
def MixedAdamsLongLayerPairing.cyclesToPage (hP : P.ProjectionCompatible) :
    adamsCycles unit X r hr p.1 p.2 →ₗ[ℤ]
      adamsCycles unit Y r hr q.1 q.2 →ₗ[ℤ]
        adamsPage unit Z r hr (p.1 + q.1) (p.2 + q.2) :=
  (P.onCycles hP).compr₂ (adamsCycleBoundaries unit Z r hr (p.1 + q.1) (p.2 + q.2)).mkQ

end
end KIP126.Classical.Adams
