module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Rotation.Sign.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Additive.Proofs
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.Rotate

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Pretriangulated
universe u

/-- The counit of the actual suspension-loop adjunction is invertible,
because the already constructed source loop functor is fully faithful. -/
noncomputable def sourceSuspensionLoopCounitIso :
    sourceLoopFunctor.{u} ⋙ sourceSuspensionFunctor ≅ 𝟭 SourceCategory :=
  asIso sourceSuspensionLoopAdjunction.counit

/-- The actual fiber boundary in suspension coordinates. The negative sign
matches the positive retained-path inclusion under inverse rotation. -/
noncomputable def sourceFiberBoundary {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLocalization.obj Y ⟶ (sourceLocalization.obj (fiber f))⟦(1 : ℤ)⟧ :=
  -((sourceSuspensionLoopCounitIso.app (sourceLocalization.obj Y)).inv ≫
    sourceSuspensionFunctor.map (sourceLocalization.map (fiberConnecting f)))

/-- The genuine triangle attached to an actual strict map, with its actual
fiber and the specified suspension-coordinate boundary. -/
noncomputable def sourceFiberTriangle {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    Triangle SourceCategory.{u} :=
  Triangle.mk (sourceLocalization.map (fiberProjection f)) (sourceLocalization.map f)
    (sourceFiberBoundary f)

/-- Suspend the actual iteration inverse and use the actual adjunction
counit to identify the third object of the rotated fiber triangle. -/
noncomputable def sourceFiberIterationSuspensionIso {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    (sourceLocalization.obj (fiber (fiberProjection f)))⟦(1 : ℤ)⟧ ≅ sourceLocalization.obj Y :=
  sourceSuspensionFunctor.mapIso (sourceFiberIterationIso f).symm ≪≫
    sourceSuspensionLoopCounitIso.app (sourceLocalization.obj Y)

end KIP126.StableHomotopy.Implementation.Prespectrum
