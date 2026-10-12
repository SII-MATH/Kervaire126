module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Triangulated.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Sequence
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Product.Proofs
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Pretriangulated
universe u
set_option backward.isDefEq.respectTransparency false

/-- The original abelian stable homotopy functor is homological for the
actual fiber-triangle structure. This uses the proved cubical fiber exact
sequence and transports it across the defining triangle isomorphisms. -/
instance sourceStableHomotopyAddFunctor_isHomological (d : ℤ) :
    (sourceStableHomotopyAddFunctor.{u} d).IsHomological := by
  apply Functor.IsHomological.mk'
  intro T hT
  obtain ⟨X,Y,f,⟨e⟩⟩ := hT
  refine ⟨Prespectrum.sourceFiberTriangle f,e,?_⟩
  rw [ShortComplex.ab_exact_iff_function_exact]
  change Function.Exact
    ((sourceStableHomotopyAddFunctor d).map (sourceLocalization.map (Prespectrum.fiberProjection f)))
    ((sourceStableHomotopyAddFunctor d).map (sourceLocalization.map f))
  rw [sourceStableHomotopyAddFunctor_map,sourceStableHomotopyAddFunctor_map]
  exact Prespectrum.fiberProjection_map_exact f d

/-- The maps induced on the unchanged stable groups by the first two
arrows of any actual distinguished triangle are exact. -/
theorem sourceStableHomotopyAddFunctor_exact (d : ℤ)
    (T : Triangle SourceCategory.{u}) (hT : T ∈ distTriang SourceCategory) :
    Function.Exact ((sourceStableHomotopyAddFunctor d).map T.mor₁)
      ((sourceStableHomotopyAddFunctor d).map T.mor₂) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    ((sourceStableHomotopyAddFunctor d).map_distinguished_exact T hT)

/-- All three consecutive positions of the long exact sequence use the
original stable-group functor, the actual triangle boundary, and the
fixed suspension. Removing the rotation minus sign does not change its kernel. -/
theorem sourceStableHomotopyAddFunctor_longExact (d : ℤ)
    (T : Triangle SourceCategory.{u}) (hT : T ∈ distTriang SourceCategory) :
    Function.Exact ((sourceStableHomotopyAddFunctor d).map T.mor₁)
      ((sourceStableHomotopyAddFunctor d).map T.mor₂) ∧
    Function.Exact ((sourceStableHomotopyAddFunctor d).map T.mor₂)
      ((sourceStableHomotopyAddFunctor d).map T.mor₃) ∧
    Function.Exact ((sourceStableHomotopyAddFunctor d).map T.mor₃)
      ((sourceStableHomotopyAddFunctor d).map (T.mor₁⟦(1 : ℤ)⟧')) := by
  refine ⟨sourceStableHomotopyAddFunctor_exact d T hT,
    sourceStableHomotopyAddFunctor_exact d T.rotate (rot_of_distTriang T hT),?_⟩
  have h := sourceStableHomotopyAddFunctor_exact d T.rotate.rotate
    (rot_of_distTriang T.rotate (rot_of_distTriang T hT))
  change Function.Exact ((sourceStableHomotopyAddFunctor d).map T.mor₃)
    ((sourceStableHomotopyAddFunctor d).map (-T.mor₁⟦(1 : ℤ)⟧')) at h
  intro x
  have hx := h x
  rw [Functor.map_neg] at hx
  change -(((sourceStableHomotopyAddFunctor d).map (T.mor₁⟦(1 : ℤ)⟧')) x) = 0 ↔ _ at hx
  simpa only [neg_eq_zero] using hx

/-- For a strict map, the long exact triangle sequence retains exactly
the original cubical projection map, original map, actual signed boundary,
and the original cubical map of its suspension. -/
theorem source_fiberTriangle_stableHomotopy_longExact {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (d : ℤ) :
    Function.Exact (Prespectrum.stableHomotopyAddHom (Prespectrum.fiberProjection f) d)
      (Prespectrum.stableHomotopyAddHom f d) ∧
    Function.Exact (Prespectrum.stableHomotopyAddHom f d)
      ((sourceStableHomotopyAddFunctor d).map (Prespectrum.sourceFiberBoundary f)) ∧
    Function.Exact ((sourceStableHomotopyAddFunctor d).map (Prespectrum.sourceFiberBoundary f))
      (Prespectrum.stableHomotopyAddHom (Prespectrum.suspensionMap (Prespectrum.fiberProjection f)) d) := by
  have h := sourceStableHomotopyAddFunctor_longExact d (Prespectrum.sourceFiberTriangle f)
    (Prespectrum.sourceFiberDistinguished_fiber f)
  change Function.Exact
      ((sourceStableHomotopyAddFunctor d).map (sourceLocalization.map (Prespectrum.fiberProjection f)))
      ((sourceStableHomotopyAddFunctor d).map (sourceLocalization.map f)) ∧
    Function.Exact ((sourceStableHomotopyAddFunctor d).map (sourceLocalization.map f))
      ((sourceStableHomotopyAddFunctor d).map (Prespectrum.sourceFiberBoundary f)) ∧
    Function.Exact ((sourceStableHomotopyAddFunctor d).map (Prespectrum.sourceFiberBoundary f))
      ((sourceStableHomotopyAddFunctor d).map
        (Prespectrum.sourceSuspensionFunctor.map (sourceLocalization.map (Prespectrum.fiberProjection f)))) at h
  simp only [Prespectrum.sourceSuspensionFunctor_map,sourceStableHomotopyAddFunctor_map] at h
  exact h

end KIP126.StableHomotopy.Implementation
