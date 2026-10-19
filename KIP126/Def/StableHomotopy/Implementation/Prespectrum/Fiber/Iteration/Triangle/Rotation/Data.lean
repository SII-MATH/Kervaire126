module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Triangle.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Pretriangulated
universe u

/-- Rotating the actual fiber triangle of the projection gives the
original actual fiber triangle. The first two components are identities;
the third suspends the displayed iteration inverse and uses the actual counit. -/
noncomputable def sourceFiberTriangleRotateIso {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    (sourceFiberTriangle (fiberProjection f)).rotate ≅ sourceFiberTriangle f :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (sourceFiberIterationSuspensionIso f)
    (by
      change sourceLocalization.map (fiberProjection f) ≫ 𝟙 _ =
        𝟙 _ ≫ sourceLocalization.map (fiberProjection f)
      simp)
    (by
      change sourceFiberBoundary (fiberProjection f) ≫
        (sourceFiberIterationSuspensionIso f).hom = 𝟙 _ ≫ sourceLocalization.map f
      rw [Category.id_comp]
      exact sourceFiberIterationSuspensionIso_boundary f)
    (by
      change (-((sourceLocalization.map (fiberProjection (fiberProjection f)))⟦(1 : ℤ)⟧')) ≫
        (𝟙 (sourceLocalization.obj (fiber f)))⟦(1 : ℤ)⟧' =
          (sourceFiberIterationSuspensionIso f).hom ≫ sourceFiberBoundary f
      rw [(shiftFunctor SourceCategory (1 : ℤ)).map_id,Category.comp_id]
      exact (sourceFiberIterationSuspensionIso_connecting f).symm)

end KIP126.StableHomotopy.Implementation.Prespectrum
