module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Triangulated.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Cocone.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Contractible.Iso.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Pretriangulated

universe u

set_option backward.isDefEq.respectTransparency false

theorem sourceFiberDistinguished_contractible (A : SourceCategory.{u}) :
    sourceFiberDistinguished (contractibleTriangle A) :=
  source_contractibleTriangle_iso_exists A

/-- The cocone existence axiom is supplied by actual fibers of suspended
connecting maps and the proved roofs in the original localization. -/
theorem sourceFiberDistinguished_cocone {A B : SourceCategory.{u}} (a : A ⟶ B) :
    ∃ (C : SourceCategory.{u}) (b : B ⟶ C) (c : C ⟶ A⟦(1 : ℤ)⟧),
      sourceFiberDistinguished (Triangle.mk a b c) := by
  obtain ⟨C,b,c,U,V,k,hk⟩ := source_morphism_exists_fiber_triangle a
  exact ⟨C,b,c,U,V,k,hk⟩

/-- Positive rotation follows from actual cocones, inverse rotation, and
the isomorphism theorem for the second-arrow diagrams of actual fibers. -/
theorem sourceFiberDistinguished_rotate {T : Triangle SourceCategory.{u}}
    (hT : sourceFiberDistinguished T) : sourceFiberDistinguished T.rotate := by
  obtain ⟨C,b,c,hS⟩ := sourceFiberDistinguished_cocone T.mor₂
  let S := Triangle.mk T.mor₂ b c
  obtain ⟨e⟩ := sourceFiberDistinguished_iso_exists
    (sourceFiberDistinguished_invRotate hS) hT (Iso.refl _) (Iso.refl _)
    (by simp)
  exact sourceFiberDistinguished_iso
    ((rotate SourceCategory).mapIso e.symm ≪≫ invRotCompRot.app S) hS

theorem sourceFiberDistinguished_rotate_iff (T : Triangle SourceCategory.{u}) :
    sourceFiberDistinguished T ↔ sourceFiberDistinguished T.rotate := by
  refine ⟨sourceFiberDistinguished_rotate, fun h => ?_⟩
  exact sourceFiberDistinguished_iso (rotCompInvRot.app T)
    (sourceFiberDistinguished_invRotate h)

end KIP126.StableHomotopy.Implementation.Prespectrum
