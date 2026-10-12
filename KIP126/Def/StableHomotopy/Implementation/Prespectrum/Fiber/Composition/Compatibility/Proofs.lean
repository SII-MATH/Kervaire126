module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Equivalence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Triangle.Map.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[simp, reassoc] theorem fiberCompositeInclusion_projection {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberCompositeInclusion f g ≫ fiberProjection (f ≫ g) = fiberProjection f := rfl

@[simp, reassoc] theorem fiberCompositeProjection_projection {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberCompositeProjection f g ≫ fiberProjection g = fiberProjection (f ≫ g) ≫ f := rfl

@[simp, reassoc] theorem fiberCompositeConnecting_retraction {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberConnecting (fiberCompositeProjection f g) ≫ fiberCompositeRetraction f g =
      loopMap (fiberProjection g) ≫ fiberConnecting f := rfl

/-- The fourth triangle's boundary is the first boundary after the second
fiber projection, with the sign fixed by the original fiber convention. -/
theorem sourceFiberCompositeIso_boundary {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    sourceFiberBoundary (fiberCompositeProjection f g) ≫
        (sourceFiberCompositeIso f g).inv⟦(1 : ℤ)⟧' =
      sourceLocalization.map (fiberProjection g) ≫ sourceFiberBoundary f := by
  apply sourceFiberBoundary_natural
  change sourceLocalization.map (fiberConnecting (fiberCompositeProjection f g)) ≫
    sourceLocalization.map (fiberCompositeRetraction f g) = _
  rw [← Functor.map_comp,fiberCompositeConnecting_retraction,Functor.map_comp,
    sourceLoopFunctor_map]
  rfl

theorem sourceFiberCompositeIso_inv_inclusion {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (sourceFiberCompositeIso f g).inv ≫ sourceLocalization.map (fiberCompositeInclusion f g) =
      sourceLocalization.map (fiberProjection (fiberCompositeProjection f g)) := by
  rw [← sourceFiberCompositeIso_projection,← Category.assoc,Iso.inv_hom_id,Category.id_comp]

end KIP126.StableHomotopy.Implementation.Prespectrum
