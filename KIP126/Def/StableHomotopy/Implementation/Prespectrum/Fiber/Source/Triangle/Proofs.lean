module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Map.Existence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Triangle.Map.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Triangle.Rotation.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Pretriangulated

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every commuting square on the second and third objects of actual fiber
triangles extends to a genuine triangle morphism. -/
theorem sourceFiberTriangleMap_exists {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : sourceLocalization.obj X ⟶ sourceLocalization.obj X')
    (b : sourceLocalization.obj Y ⟶ sourceLocalization.obj Y')
    (hf : sourceLocalization.map f ≫ b = a ≫ sourceLocalization.map g) :
    ∃ φ : sourceFiberTriangle f ⟶ sourceFiberTriangle g, φ.hom₂ = a ∧ φ.hom₃ = b := by
  obtain ⟨c, hp, hc⟩ := source_fiberMap_exists f g a b hf
  exact ⟨sourceFiberTriangleMap f g a b c hp.symm hf hc, rfl, rfl⟩

/-- Every commuting square on the first two objects of the actual fiber
triangles extends to a triangle morphism. This is the actual fiber case of
the triangle morphism axiom, proved before imposing any such axiom. -/
theorem sourceFiberTriangle_morphism_exists {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : sourceLocalization.obj (fiber f) ⟶ sourceLocalization.obj (fiber g))
    (b : sourceLocalization.obj X ⟶ sourceLocalization.obj X')
    (hp : sourceLocalization.map (fiberProjection f) ≫ b =
      a ≫ sourceLocalization.map (fiberProjection g)) :
    ∃ φ : sourceFiberTriangle f ⟶ sourceFiberTriangle g, φ.hom₁ = a ∧ φ.hom₂ = b := by
  obtain ⟨φ, ha, hb⟩ := sourceFiberTriangleMap_exists (fiberProjection f) (fiberProjection g) a b hp
  refine ⟨(sourceFiberTriangleRotateIso f).inv ≫ (rotate SourceCategory).map φ ≫
    (sourceFiberTriangleRotateIso g).hom, ?_, ?_⟩
  · change 𝟙 _ ≫ φ.hom₂ ≫ 𝟙 _ = a
    simpa only [Category.id_comp, Category.comp_id] using ha
  · change 𝟙 _ ≫ φ.hom₃ ≫ 𝟙 _ = b
    simpa only [Category.id_comp, Category.comp_id] using hb

end KIP126.StableHomotopy.Implementation.Prespectrum
