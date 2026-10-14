module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Triangulated.Rotation.Proofs
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Pretriangulated

universe u

/-- The original stable localization with its fixed suspension and actual
fiber triangles has the pretriangulated structure proved above. -/
noncomputable instance sourcePretriangulated : Pretriangulated SourceCategory.{u} where
  distinguishedTriangles := {T | sourceFiberDistinguished T}
  isomorphic_distinguished := fun _ h _ e => sourceFiberDistinguished_iso e h
  contractible_distinguished := sourceFiberDistinguished_contractible
  distinguished_cocone_triangle := sourceFiberDistinguished_cocone
  rotate_distinguished_triangle := sourceFiberDistinguished_rotate_iff
  complete_distinguished_triangle_morphism := by
    intro T U hT hU a b h
    obtain ⟨φ,ha,hb⟩ := sourceFiberDistinguished_morphism_exists hT hU a b h
    exact ⟨φ.hom₃, by simpa only [hb] using φ.comm₂,
      by simpa only [ha] using φ.comm₃⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
