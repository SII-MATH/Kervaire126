module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Octahedron.Instances

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Pretriangulated

set_option backward.isDefEq.respectTransparency false

/-- In an actual distinguished source triangle, locality of the second
and third objects implies locality of the first. -/
theorem SourceIsHF2Local.triangle_first (T : Triangle SourceCategory.{0})
    (hT : T ∈ distTriang SourceCategory) (h₂ : SourceIsHF2Local T.obj₂)
    (h₃ : SourceIsHF2Local T.obj₃) : SourceIsHF2Local T.obj₁ := by
  change Prespectrum.sourceFiberDistinguished T at hT
  obtain ⟨X,Y,f,⟨e⟩⟩ := hT
  have hX : X.IsHF2Local := SourceIsHF2Local.of_iso (Triangle.π₂.mapIso e).symm h₂
  have hY : Y.IsHF2Local := SourceIsHF2Local.of_iso (Triangle.π₃.mapIso e).symm h₃
  apply SourceIsHF2Local.of_iso (Triangle.π₁.mapIso e)
  exact Prespectrum.IsHF2Local.fiber f hX hY

/-- In an actual distinguished source triangle, locality of the first
two objects implies locality of the third. -/
theorem SourceIsHF2Local.triangle_third (T : Triangle SourceCategory.{0})
    (hT : T ∈ distTriang SourceCategory) (h₁ : SourceIsHF2Local T.obj₁)
    (h₂ : SourceIsHF2Local T.obj₂) : SourceIsHF2Local T.obj₃ :=
  SourceIsHF2Local.triangle_first T.rotate.rotate
    (rot_of_distTriang _ (rot_of_distTriang _ hT)) h₁.suspension h₂.suspension

/-- Every map between local source objects has an actual distinguished
cocone whose third object is local. -/
theorem SourceIsHF2Local.cocone {A B : SourceCategory.{0}} (f : A ⟶ B)
    (hA : SourceIsHF2Local A) (hB : SourceIsHF2Local B) :
    ∃ (C : SourceCategory.{0}) (_ : SourceIsHF2Local C)
      (g : B ⟶ C) (h : C ⟶ A⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang SourceCategory := by
  obtain ⟨C,g,h,hT⟩ := distinguished_cocone_triangle f
  exact ⟨C, SourceIsHF2Local.triangle_third _ hT hA hB, g,h,hT⟩

end KIP126.StableHomotopy.Implementation
