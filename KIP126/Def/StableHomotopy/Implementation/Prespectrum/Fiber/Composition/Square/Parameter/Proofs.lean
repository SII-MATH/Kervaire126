module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Square.Parameter.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology KIP126.Topology.Cube
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

theorem fiberCompositePaddingSquare_start {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (θ : I)
    (z : (fiber (fiberCompositeProjection f g)).level n) (s : I) :
    fiberCompositePaddingSquare f g n (((θ,z),s),0) = g.level n (z.val.2 s).val.1 := by
  change (z.val.2 s).val.2 (unitInterval.qRight (0,θ)) = _
  rw [unitInterval.qRight_zero_left]
  exact (z.val.2 s).property.1

theorem fiberCompositePaddingSquare_end {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (θ : I)
    (z : (fiber (fiberCompositeProjection f g)).level n) (s : I) :
    fiberCompositePaddingSquare f g n (((θ,z),s),1) = (Z.level n).point := by
  change (z.val.2 s).val.2 (unitInterval.qRight (1,θ)) = _
  rw [unitInterval.qRight_one_left]
  exact (z.val.2 s).property.2

theorem fiberCompositePaddingSquare_top {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (θ : I)
    (z : (fiber (fiberCompositeProjection f g)).level n) (t : I) :
    fiberCompositePaddingSquare f g n (((θ,z),1),t) = (Z.level n).point :=
  congrArg (fun a : (fiber g).level n => a.val.2 (unitInterval.qRight (t,θ))) z.property.2

theorem fiberCompositeMoveSquare_start {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (θ : I)
    (z : (fiber (fiberCompositeProjection f g)).level n) (s : I) :
    fiberCompositeMoveSquare f g n (((θ,z),s),0) = g.level n (z.val.2 s).val.1 := by
  change (z.val.2 (Set.Icc.convexComb s (Set.Icc.convexComb s 1 (advancedCoordinate 0)) θ)).val.2
    (Set.Icc.convexComb (advancedCoordinate 0) (delayedCoordinate 0) θ) = _
  simp only [advancedCoordinate_zero,delayedCoordinate_zero,Set.Icc.convexComb_zero,
    Set.Icc.convexComb_eq]
  exact (z.val.2 s).property.1

theorem fiberCompositeMoveSquare_end {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (θ : I)
    (z : (fiber (fiberCompositeProjection f g)).level n) (s : I) :
    fiberCompositeMoveSquare f g n (((θ,z),s),1) = (Z.level n).point := by
  change (z.val.2 (Set.Icc.convexComb s (Set.Icc.convexComb s 1 (advancedCoordinate 1)) θ)).val.2
    (Set.Icc.convexComb (advancedCoordinate 1) (delayedCoordinate 1) θ) = _
  simp only [advancedCoordinate_one,delayedCoordinate_one,Set.Icc.convexComb_one,
    Set.Icc.convexComb_eq]
  exact (z.val.2 _).property.2

theorem fiberCompositeMoveSquare_top {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (θ : I)
    (z : (fiber (fiberCompositeProjection f g)).level n) (t : I) :
    fiberCompositeMoveSquare f g n (((θ,z),1),t) = (Z.level n).point := by
  change (z.val.2 (Set.Icc.convexComb 1 (Set.Icc.convexComb 1 1 (advancedCoordinate t)) θ)).val.2
    (Set.Icc.convexComb (advancedCoordinate t) (delayedCoordinate t) θ) = _
  simp only [Set.Icc.convexComb_eq]
  exact congrArg (fun a : (fiber g).level n => a.val.2 _) z.property.2

theorem fiberCompositeMoveSquare_zero {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (z : (fiber (fiberCompositeProjection f g)).level n) (s t : I) :
    fiberCompositeMoveSquare f g n (((0,z),s),t) =
      fiberCompositePaddingSquare f g n (((0,z),s),t) := by
  change (z.val.2 (Set.Icc.convexComb s (Set.Icc.convexComb s 1 (advancedCoordinate t)) 0)).val.2
    (Set.Icc.convexComb (advancedCoordinate t) (delayedCoordinate t) 0) = _
  simp only [Set.Icc.convexComb_zero]
  change (z.val.2 s).val.2 (advancedCoordinate t) = (z.val.2 s).val.2 (unitInterval.qRight (t,0))
  congr 1
  simp [advancedCoordinate,unitInterval.qRight]

/-- The final deformed square reads exactly the image of the source path. -/
theorem fiberCompositeMoveSquare_one {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (z : (fiber (fiberCompositeProjection f g)).level n) (s t : I) :
    fiberCompositeMoveSquare f g n (((1,z),s),t) =
      g.level n (z.val.2 (Set.Icc.convexComb s 1 (advancedCoordinate t))).val.1 := by
  change (z.val.2 (Set.Icc.convexComb s (Set.Icc.convexComb s 1 (advancedCoordinate t)) 1)).val.2
    (Set.Icc.convexComb (advancedCoordinate t) (delayedCoordinate t) 1) = _
  simp only [Set.Icc.convexComb_one]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [delayedCoordinate_eq_zero ht]
    exact (z.val.2 _).property.1
  · rw [advancedCoordinate_eq_one (le_of_lt (lt_of_not_ge ht)),Set.Icc.convexComb_one]
    exact (congrArg (fun a : (fiber g).level n => a.val.2 (delayedCoordinate t)) z.property.2).trans
      ((congrArg (fun a : (fiber g).level n => g.level n a.val.1) z.property.2).trans
        (g.point n)).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
