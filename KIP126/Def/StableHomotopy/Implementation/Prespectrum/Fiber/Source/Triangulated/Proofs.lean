module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Triangulated.Predicates
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Triangle.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Pretriangulated

universe u

set_option backward.isDefEq.respectTransparency false

theorem sourceFiberDistinguished_fiber {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceFiberDistinguished (sourceFiberTriangle f) :=
  ⟨X, Y, f, ⟨Iso.refl _⟩⟩

theorem sourceFiberDistinguished_iso {T U : Triangle SourceCategory.{u}}
    (e : T ≅ U) (hU : sourceFiberDistinguished U) : sourceFiberDistinguished T := by
  obtain ⟨X, Y, f, ⟨d⟩⟩ := hU
  exact ⟨X, Y, f, ⟨e ≪≫ d⟩⟩

/-- Inverse rotation stays in the actual fiber class, by the proved signed
rotation isomorphism for the fiber of the projection. -/
theorem sourceFiberDistinguished_invRotate {T : Triangle SourceCategory.{u}}
    (hT : sourceFiberDistinguished T) : sourceFiberDistinguished T.invRotate := by
  obtain ⟨X, Y, f, ⟨e⟩⟩ := hT
  exact ⟨fiber f, X, fiberProjection f,
    ⟨(invRotate SourceCategory).mapIso (e ≪≫ (sourceFiberTriangleRotateIso f).symm) ≪≫
      (rotCompInvRot.app (sourceFiberTriangle (fiberProjection f))).symm⟩⟩

/-- Isomorphisms on the second and third objects of actual fiber triangles
extend to a genuine triangle isomorphism. -/
theorem sourceFiberTriangle_iso_exists {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : sourceLocalization.obj X ≅ sourceLocalization.obj X')
    (b : sourceLocalization.obj Y ≅ sourceLocalization.obj Y')
    (h : sourceLocalization.map f ≫ b.hom = a.hom ≫ sourceLocalization.map g) :
    Nonempty (sourceFiberTriangle f ≅ sourceFiberTriangle g) := by
  obtain ⟨k, hp, hc⟩ := source_fiberIso_exists f g a b h
  exact ⟨Triangle.isoMk _ _ k a b hp.symm h (sourceFiberBoundary_natural f g b.hom k.hom hc)⟩

/-- The actual fiber class has square completion on its first two objects. -/
theorem sourceFiberDistinguished_morphism_exists {T U : Triangle SourceCategory.{u}}
    (hT : sourceFiberDistinguished T) (hU : sourceFiberDistinguished U)
    (a : T.obj₁ ⟶ U.obj₁) (b : T.obj₂ ⟶ U.obj₂)
    (h : T.mor₁ ≫ b = a ≫ U.mor₁) :
    ∃ φ : T ⟶ U, φ.hom₁ = a ∧ φ.hom₂ = b := by
  obtain ⟨X, Y, f, ⟨e⟩⟩ := hT
  obtain ⟨X', Y', g, ⟨d⟩⟩ := hU
  let a' := e.inv.hom₁ ≫ a ≫ d.hom.hom₁
  let b' := e.inv.hom₂ ≫ b ≫ d.hom.hom₂
  have hp : sourceLocalization.map (fiberProjection f) ≫ b' =
      a' ≫ sourceLocalization.map (fiberProjection g) := by
    change (sourceFiberTriangle f).mor₁ ≫ (e.inv.hom₂ ≫ b ≫ d.hom.hom₂) =
      (e.inv.hom₁ ≫ a ≫ d.hom.hom₁) ≫ (sourceFiberTriangle g).mor₁
    rw [← Category.assoc, e.inv.comm₁, Category.assoc, Category.assoc,
      ← Category.assoc T.mor₁, h]
    simp only [Category.assoc, d.hom.comm₁]
  obtain ⟨φ, ha, hb⟩ := sourceFiberTriangle_morphism_exists f g a' b' hp
  refine ⟨e.hom ≫ φ ≫ d.inv, ?_, ?_⟩
  · change e.hom.hom₁ ≫ φ.hom₁ ≫ d.inv.hom₁ = a
    rw [ha]
    change (Triangle.π₁.mapIso e).hom ≫
      ((Triangle.π₁.mapIso e).inv ≫ a ≫ (Triangle.π₁.mapIso d).hom) ≫
        (Triangle.π₁.mapIso d).inv = a
    simp
  · change e.hom.hom₂ ≫ φ.hom₂ ≫ d.inv.hom₂ = b
    rw [hb]
    change (Triangle.π₂.mapIso e).hom ≫
      ((Triangle.π₂.mapIso e).inv ≫ b ≫ (Triangle.π₂.mapIso d).hom) ≫
        (Triangle.π₂.mapIso d).inv = b
    simp

/-- An isomorphism of the second-arrow diagrams identifies triangles in the
actual fiber class. No pretriangulated axiom is assumed. -/
theorem sourceFiberDistinguished_iso_exists {T U : Triangle SourceCategory.{u}}
    (hT : sourceFiberDistinguished T) (hU : sourceFiberDistinguished U)
    (a : T.obj₂ ≅ U.obj₂) (b : T.obj₃ ≅ U.obj₃)
    (h : T.mor₂ ≫ b.hom = a.hom ≫ U.mor₂) : Nonempty (T ≅ U) := by
  obtain ⟨X, Y, f, ⟨e⟩⟩ := hT
  obtain ⟨X', Y', g, ⟨d⟩⟩ := hU
  let a' := (Triangle.π₂.mapIso e).symm ≪≫ a ≪≫ Triangle.π₂.mapIso d
  let b' := (Triangle.π₃.mapIso e).symm ≪≫ b ≪≫ Triangle.π₃.mapIso d
  have hf : sourceLocalization.map f ≫ b'.hom = a'.hom ≫ sourceLocalization.map g := by
    change (sourceFiberTriangle f).mor₂ ≫ (e.inv.hom₃ ≫ b.hom ≫ d.hom.hom₃) =
      (e.inv.hom₂ ≫ a.hom ≫ d.hom.hom₂) ≫ (sourceFiberTriangle g).mor₂
    rw [← Category.assoc, e.inv.comm₂, Category.assoc, Category.assoc,
      ← Category.assoc T.mor₂, h]
    simp only [Category.assoc, d.hom.comm₂]
  obtain ⟨k⟩ := sourceFiberTriangle_iso_exists f g a' b' hf
  exact ⟨e ≪≫ k ≪≫ d.symm⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
