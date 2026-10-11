module

public import KIP126.Def.ClassicalAdams.Suspension.Pages.Data

@[expose] public section


/-! The actual suspension quotient map, transported through the existing
representative-preserving identification with the internal Adams pages. -/

namespace KIP126.Classical.Adams.Suspension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {X : C}

/-- The displayed internal page map is the actual quotient desuspension,
conjugated by the canonical representative-preserving page isomorphisms. -/
def TowerComparison.desuspendInternalPage (S : TowerComparison H X)
    (r : ℤ) (p : ℤ × ℤ) :
    (adamsTowerInternalSpectralSequence H.unit (X⟦(1 : ℤ)⟧)).Page r p ⟶
      (adamsTowerInternalSpectralSequence H.unit X).Page r (p.1, p.2 - 1) :=
  (adamsTowerSSDataPageIso H.unit (X⟦(1 : ℤ)⟧) p.1 p.2 (r - 2).toNat).hom ≫
    ModuleCat.ofHom (S.desuspendPage ((r - 2).toNat + 2) (by omega) p.1 p.2) ≫
      (adamsTowerSSDataPageIso H.unit X p.1 (p.2 - 1) (r - 2).toNat).inv

/-- Two successive actual desuspensions. Both maps are fixed by the supplied
layer comparisons and quotient projections. -/
def TowerComparison.desuspendTwiceInternalPage (S : TowerComparison H X)
    (S' : TowerComparison H (X⟦(1 : ℤ)⟧)) (r : ℤ) (p : ℤ × ℤ) :
    (adamsTowerInternalSpectralSequence H.unit ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)).Page r p ⟶
      (adamsTowerInternalSpectralSequence H.unit X).Page r (p.1, p.2 - 1 - 1) :=
  S'.desuspendInternalPage r p ≫ S.desuspendInternalPage r (p.1, p.2 - 1)

end
end KIP126.Classical.Adams.Suspension
