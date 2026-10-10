import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Mixed.Page.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Internal.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X Y Z : C}
  {n : ℕ} {p q : ℤ × ℤ}
  (P : MixedAdamsLongLayerPairing unit X Y Z (n + 2) (by omega) p q)

/-- The same descended pairing on the three existing internal SSData pages.
The raw finite SSData level `n` is the Adams page `n+2`, so the input uses
long layers of length `n+2`; no additional reindexing choice is made. -/
def MixedAdamsLongLayerPairing.onInternalPage (hP : P.ProjectionCompatible)
    (hB : P.BoundaryCompatible) :
    (adamsTowerSSData unit X p.1 p.2).page (n : WithTop ℕ) →ₗ[ℤ]
      (adamsTowerSSData unit Y q.1 q.2).page (n : WithTop ℕ) →ₗ[ℤ]
        (adamsTowerSSData unit Z (p.1 + q.1) (p.2 + q.2)).page (n : WithTop ℕ) := by
  let F := ((P.onPage hP hB).compl₁₂ (adamsTowerSSDataPageIso unit X p.1 p.2 n).hom.hom
    (adamsTowerSSDataPageIso unit Y q.1 q.2 n).hom.hom).compr₂ₛₗ
      (adamsTowerSSDataPageIso unit Z (p.1 + q.1) (p.2 + q.2) n).inv.hom
  exact { F.toAddMonoidHom with
    map_smul' := fun a x => by
      exact (congrArg F.toAddMonoidHom
        (int_smul_eq_zsmul ((adamsTowerSSData unit X p.1 p.2).page
          (n : WithTop ℕ)).isModule a x)).trans (F.toAddMonoidHom.map_zsmul a x) }

end
end KIP126.Classical.Adams
