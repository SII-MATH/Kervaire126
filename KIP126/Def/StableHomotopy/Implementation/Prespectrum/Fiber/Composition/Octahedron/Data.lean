module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Triangle.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Triangulated.Data
public import Mathlib.CategoryTheory.Triangulated.Triangulated

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated
universe u
set_option backward.isDefEq.respectTransparency false

/-- The retained-path construction supplies the actual unrotated
octahedron for the standard fiber triangles of a strict composable pair. -/
noncomputable def sourceFiberCompositeOctahedron' {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Octahedron' (sourceLocalization.map_comp f g).symm
      (show sourceFiberTriangle f ∈ distTriang SourceCategory from sourceFiberDistinguished_fiber f)
      (show sourceFiberTriangle g ∈ distTriang SourceCategory from sourceFiberDistinguished_fiber g)
      (show sourceFiberTriangle (f ≫ g) ∈ distTriang SourceCategory from
        sourceFiberDistinguished_fiber (f ≫ g)) where
  m₁ := sourceLocalization.map (fiberCompositeInclusion f g)
  m₃ := sourceLocalization.map (fiberCompositeProjection f g)
  comm₁ := by rw [← Functor.map_comp,fiberCompositeInclusion_projection]
  comm₂ := (sourceFiberCompositeInclusionTriangleMap f g).comm₃
  comm₃ := by
    have h := (sourceFiberCompositeProjectionTriangleMap f g).comm₃
    change sourceFiberBoundary (f ≫ g) ≫
      (sourceLocalization.map (fiberCompositeProjection f g))⟦(1 : ℤ)⟧' =
        𝟙 _ ≫ sourceFiberBoundary g at h
    simpa only [Category.id_comp] using h
  comm₄ := by rw [← Functor.map_comp,fiberCompositeProjection_projection,Functor.map_comp]
  mem := sourceFiberDistinguished_composite f g

/-- The shifted fourth triangle has the signs required for the usual
octahedron: change the sign of its middle object after three rotations. -/
noncomputable def sourceFiberCompositeOctahedronTriangleIso {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Triangle.mk ((sourceLocalization.map (fiberCompositeInclusion f g))⟦(1 : ℤ)⟧')
      ((sourceLocalization.map (fiberCompositeProjection f g))⟦(1 : ℤ)⟧')
      ((-((sourceLocalization.map (fiberProjection g))⟦(1 : ℤ)⟧')) ≫
        (sourceFiberBoundary f)⟦(1 : ℤ)⟧') ≅
      (sourceFiberCompositeTriangle f g).rotate.rotate.rotate :=
  Triangle.isoMk _ _ (Iso.refl _) (-(Iso.refl _)) (Iso.refl _)
    (by simp [sourceFiberCompositeTriangle])
    (by simp [sourceFiberCompositeTriangle])
    (by simp [sourceFiberCompositeTriangle,Functor.map_comp])

/-- The actual strict composition diagram satisfies Mathlib's usual
octahedron axiom for the rotated standard fiber triangles. -/
noncomputable def sourceFiberCompositeOctahedron {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Octahedron (sourceLocalization.map_comp f g).symm
      (rot_of_distTriang _ (show sourceFiberTriangle f ∈ distTriang SourceCategory from
        sourceFiberDistinguished_fiber f))
      (rot_of_distTriang _ (show sourceFiberTriangle g ∈ distTriang SourceCategory from
        sourceFiberDistinguished_fiber g))
      (rot_of_distTriang _ (show sourceFiberTriangle (f ≫ g) ∈ distTriang SourceCategory from
        sourceFiberDistinguished_fiber (f ≫ g))) where
  m₁ := (sourceLocalization.map (fiberCompositeInclusion f g))⟦(1 : ℤ)⟧'
  m₃ := (sourceLocalization.map (fiberCompositeProjection f g))⟦(1 : ℤ)⟧'
  comm₁ := (sourceFiberCompositeInclusionTriangleMap f g).comm₃
  comm₂ := by
    change _ ≫ (-((sourceLocalization.map (fiberProjection (f ≫ g)))⟦(1 : ℤ)⟧')) =
      -((sourceLocalization.map (fiberProjection f))⟦(1 : ℤ)⟧')
    rw [Preadditive.comp_neg,← Functor.map_comp,← sourceLocalization.map_comp,
      fiberCompositeInclusion_projection]
  comm₃ := by
    change sourceFiberBoundary (f ≫ g) ≫
      (sourceLocalization.map (fiberCompositeProjection f g))⟦(1 : ℤ)⟧' = sourceFiberBoundary g
    have h := (sourceFiberCompositeProjectionTriangleMap f g).comm₃
    change sourceFiberBoundary (f ≫ g) ≫
      (sourceLocalization.map (fiberCompositeProjection f g))⟦(1 : ℤ)⟧' =
        𝟙 _ ≫ sourceFiberBoundary g at h
    simpa only [Category.id_comp] using h
  comm₄ := by
    change (-((sourceLocalization.map (fiberProjection (f ≫ g)))⟦(1 : ℤ)⟧')) ≫
      (sourceLocalization.map f)⟦(1 : ℤ)⟧' =
        (sourceLocalization.map (fiberCompositeProjection f g))⟦(1 : ℤ)⟧' ≫
          (-((sourceLocalization.map (fiberProjection g))⟦(1 : ℤ)⟧'))
    simp only [Preadditive.neg_comp,Preadditive.comp_neg,
      ← (shiftFunctor SourceCategory (1 : ℤ)).map_comp,
      ← sourceLocalization.map_comp,fiberCompositeProjection_projection]
  mem := isomorphic_distinguished _
    (rot_of_distTriang _ (rot_of_distTriang _ (rot_of_distTriang _
      (show sourceFiberCompositeTriangle f g ∈ distTriang SourceCategory from
        sourceFiberDistinguished_composite f g)))) _
    (sourceFiberCompositeOctahedronTriangleIso f g)

end KIP126.StableHomotopy.Implementation.Prespectrum
