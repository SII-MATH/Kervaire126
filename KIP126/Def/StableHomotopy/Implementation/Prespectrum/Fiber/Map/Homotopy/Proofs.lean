module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Map.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Laws.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

@[simp, reassoc] theorem fiberHomotopyMap_projection {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (H : StrictHomotopy (f ≫ b) (a ≫ g)) :
    fiberHomotopyMap f g a b H ≫ fiberProjection g = fiberProjection f ≫ a := rfl

@[simp, reassoc] theorem fiberHomotopyMap_nullPath {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (H : StrictHomotopy (f ≫ b) (a ≫ g)) :
    fiberHomotopyMap f g a b H ≫ fiberNullPath g =
      (fiberSquareNullhomotopy f g a b H).hom := rfl

/-- On the connecting loop, the supplied based square homotopy contributes
only an initial constant path. -/
theorem fiberConnecting_homotopyMap {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (H : StrictHomotopy (f ≫ b) (a ≫ g)) :
    fiberConnecting f ≫ fiberHomotopyMap f g a b H =
      loopAdd (zeroMap _ _) (loopMap b) ≫ fiberConnecting g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · exact a.point n
  · apply ContinuousMap.ext
    intro s
    change ((H.levelPath n (X.level n).point).symm.trans
      (((fiberProjectionStrictNullhomotopy f).postcomp b).levelPath n
        ((fiberConnecting f).level n p))) s =
      ((Path.refl (Y'.level n).point).trans ((loopMap b).level n p)) s
    simp only [Path.trans_apply]
    split_ifs
    · exact congrArg (fun q : C(unitInterval, Y'.level n) => q (unitInterval.symm _))
        (H.hom.point n)
    · rfl

/-- Homotopy squares commute with the actual connecting maps in the
original source category; no triangle axiom is assumed. -/
theorem source_fiberConnecting_homotopyMap {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (H : StrictHomotopy (f ≫ b) (a ≫ g)) :
    sourceLocalization.map (fiberConnecting f) ≫
        sourceLocalization.map (fiberHomotopyMap f g a b H) =
      sourceLocalization.map (loopMap b) ≫ sourceLocalization.map (fiberConnecting g) := by
  rw [← CategoryTheory.Functor.map_comp, fiberConnecting_homotopyMap,
    CategoryTheory.Functor.map_comp, source_zero_loopAdd]

end KIP126.StableHomotopy.Implementation.Prespectrum
