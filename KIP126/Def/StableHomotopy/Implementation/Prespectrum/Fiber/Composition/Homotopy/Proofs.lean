module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology KIP126.Topology.Cube
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

theorem fiberCompositePaddingHomotopy_one {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberCompositePaddingHomotopy f g ≫ pathEvaluation _ 1 =
      𝟙 (fiber (fiberCompositeProjection f g)) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      change (z.val.2 0).val.2 (unitInterval.qRight (t,1)) = z.val.1.val.2 t
      rw [unitInterval.qRight_one_right]
      exact congrArg (fun a : (fiber g).level n => a.val.2 t) z.property.1
  · apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      change (z.val.2 s).val.2 (unitInterval.qRight (t,1)) = (z.val.2 s).val.2 t
      rw [unitInterval.qRight_one_right]

theorem fiberCompositeMoveHomotopy_zero {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberCompositeMoveHomotopy f g ≫ pathEvaluation _ 0 =
      fiberCompositePaddingHomotopy f g ≫ pathEvaluation _ 0 := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact fiberCompositeMoveSquare_zero f g n z 0 t
  · apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact fiberCompositeMoveSquare_zero f g n z s t

theorem fiberCompositeMoveHomotopy_one {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberCompositeMoveHomotopy f g ≫ pathEvaluation _ 1 =
      (fiberCompositeRetraction f g ≫ fiberCompositeComparison f g) ≫
        (fiberCompositePaddingHomotopy f g ≫ pathEvaluation _ 0) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      change fiberCompositeMoveSquare f g n (((1,z),0),t) =
        g.level n (z.val.2 (Set.Icc.convexComb 0 1 (unitInterval.qRight (t,0)))).val.1
      rw [fiberCompositeMoveSquare_one]
      congr 3
      simp [advancedCoordinate,unitInterval.qRight]
  · apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      change fiberCompositeMoveSquare f g n (((1,z),s),t) =
        g.level n (z.val.2 (Set.Icc.convexComb s 1 (unitInterval.qRight (t,0)))).val.1
      rw [fiberCompositeMoveSquare_one]
      congr 3
      simp [advancedCoordinate,unitInterval.qRight]

end KIP126.StableHomotopy.Implementation.Prespectrum
