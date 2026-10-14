module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[simp] theorem fiberConnecting_projection {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberConnecting f ≫ fiberProjection f = zeroMap _ _ := rfl

@[simp] theorem fiberNullPath_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberNullPath f ≫ pathEvaluation Y 0 = fiberProjection f ≫ f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  exact z.property.1

@[simp] theorem fiberNullPath_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiberNullPath f ≫ pathEvaluation Y 1 = zeroMap _ _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  exact z.property.2

/-- The actual consecutive arrows compose to zero after stable localization. -/
theorem source_fiberProjection_comp {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLocalization.map (fiberProjection f) ≫ sourceLocalization.map f =
      sourceLocalization.map (zeroMap (fiber f) Y) := by
  rw [← Functor.map_comp,← fiberNullPath_zero,← fiberNullPath_one f,
    Functor.map_comp,Functor.map_comp,source_pathEvaluation_eq Y 0 1]

end KIP126.StableHomotopy.Implementation.Prespectrum
