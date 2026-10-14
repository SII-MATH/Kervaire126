module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Compatibility.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Pretriangulated
universe u

/-- The actual fourth fiber triangle of a composable pair. Its maps are
the retained-path inclusion, projection, and the original signed boundary. -/
noncomputable def sourceFiberCompositeTriangle {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) : Triangle SourceCategory.{u} :=
  Triangle.mk (sourceLocalization.map (fiberCompositeInclusion f g))
    (sourceLocalization.map (fiberCompositeProjection f g))
    (sourceLocalization.map (fiberProjection g) ≫ sourceFiberBoundary f)

/-- The fourth triangle is isomorphic to an actual standard fiber
triangle, using the explicit strict retained-square homotopy inverse. -/
noncomputable def sourceFiberCompositeTriangleIso {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    sourceFiberTriangle (fiberCompositeProjection f g) ≅ sourceFiberCompositeTriangle f g :=
  Triangle.isoMk _ _ (sourceFiberCompositeIso f g).symm (Iso.refl _) (Iso.refl _)
    (by
      change sourceLocalization.map (fiberProjection (fiberCompositeProjection f g)) ≫ 𝟙 _ = _
      rw [Category.comp_id]
      exact (sourceFiberCompositeIso_inv_inclusion f g).symm)
    (by
      change sourceLocalization.map (fiberCompositeProjection f g) ≫ 𝟙 _ =
        𝟙 _ ≫ sourceLocalization.map (fiberCompositeProjection f g)
      simp)
    (by
      change sourceFiberBoundary (fiberCompositeProjection f g) ≫
        (sourceFiberCompositeIso f g).inv⟦(1 : ℤ)⟧' = 𝟙 _ ≫ _
      rw [Category.id_comp]
      exact sourceFiberCompositeIso_boundary f g)

/-- The first face of the actual composition diagram. -/
noncomputable def sourceFiberCompositeInclusionTriangleMap {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) : sourceFiberTriangle f ⟶ sourceFiberTriangle (f ≫ g) :=
  sourceFiberTriangleMap f (f ≫ g) (𝟙 _) (sourceLocalization.map g)
    (sourceLocalization.map (fiberCompositeInclusion f g))
    (by rw [Category.comp_id,← Functor.map_comp,fiberCompositeInclusion_projection])
    (by rw [Category.id_comp,Functor.map_comp])
    (by
      change sourceLocalization.map (fiberConnecting f) ≫
        sourceLocalization.map (fiberMap f (f ≫ g) (𝟙 _) g _) = _
      rw [← Functor.map_comp,fiberConnecting_map,Functor.map_comp,sourceLoopFunctor_map]
      rfl)

/-- The second face of the actual composition diagram. -/
noncomputable def sourceFiberCompositeProjectionTriangleMap {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) : sourceFiberTriangle (f ≫ g) ⟶ sourceFiberTriangle g :=
  sourceFiberTriangleMap (f ≫ g) g (sourceLocalization.map f) (𝟙 _)
    (sourceLocalization.map (fiberCompositeProjection f g))
    (by rw [← Functor.map_comp,← Functor.map_comp,fiberCompositeProjection_projection])
    (by rw [Category.comp_id,Functor.map_comp])
    (by
      change sourceLocalization.map (fiberConnecting (f ≫ g)) ≫
        sourceLocalization.map (fiberMap (f ≫ g) g f (𝟙 _) _) = _
      rw [← Functor.map_comp,fiberConnecting_map,sourceLoopFunctor.map_id,Category.id_comp]
      rfl)

end KIP126.StableHomotopy.Implementation.Prespectrum
