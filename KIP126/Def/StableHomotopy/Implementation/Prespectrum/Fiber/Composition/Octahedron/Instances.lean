module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Octahedron.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Roofs.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated
universe u
set_option backward.isDefEq.respectTransparency false

/-- The original ordinary stable localization is triangulated for its
fixed suspension and the isomorphism closure of actual fiber triangles.
Every composable source diagram is represented by a strict composable
pair, whose octahedron was constructed from retained path squares. -/
noncomputable instance sourceIsTriangulated : IsTriangulated SourceCategory.{u} := by
  apply IsTriangulated.mk'
  intro A B C a b
  obtain ⟨X,Y,Z,f,g,e₁,e₂,e₃,h₁,h₂⟩ := source_composable_exists_strict a b
  have hf : (sourceFiberTriangle f).rotate ∈ distTriang SourceCategory :=
    rot_of_distTriang _ (sourceFiberDistinguished_fiber f)
  have hg : (sourceFiberTriangle g).rotate ∈ distTriang SourceCategory :=
    rot_of_distTriang _ (sourceFiberDistinguished_fiber g)
  have hfg : Triangle.mk (sourceLocalization.map f ≫ sourceLocalization.map g)
      (sourceFiberBoundary (f ≫ g))
      (-((sourceLocalization.map (fiberProjection (f ≫ g)))⟦(1 : ℤ)⟧')) ∈
        distTriang SourceCategory := by
    rw [← sourceLocalization.map_comp]
    exact rot_of_distTriang (sourceFiberTriangle (f ≫ g))
      (show sourceFiberTriangle (f ≫ g) ∈ distTriang SourceCategory from
        sourceFiberDistinguished_fiber (f ≫ g))
  refine ⟨sourceLocalization.obj X,sourceLocalization.obj Y,sourceLocalization.obj Z,
    (sourceLocalization.obj (fiber f))⟦(1 : ℤ)⟧,
    (sourceLocalization.obj (fiber g))⟦(1 : ℤ)⟧,
    (sourceLocalization.obj (fiber (f ≫ g)))⟦(1 : ℤ)⟧,
    sourceLocalization.map f,sourceLocalization.map g,e₁,e₂,e₃,h₁,h₂,
    sourceFiberBoundary f,-((sourceLocalization.map (fiberProjection f))⟦(1 : ℤ)⟧'),hf,
    sourceFiberBoundary g,-((sourceLocalization.map (fiberProjection g))⟦(1 : ℤ)⟧'),hg,
    sourceFiberBoundary (f ≫ g),-((sourceLocalization.map (fiberProjection (f ≫ g)))⟦(1 : ℤ)⟧'),
    hfg,?_⟩
  simpa only [sourceLocalization.map_comp] using
    Nonempty.intro (sourceFiberCompositeOctahedron f g)

end KIP126.StableHomotopy.Implementation.Prespectrum
