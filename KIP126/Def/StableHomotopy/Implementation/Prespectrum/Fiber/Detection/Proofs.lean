module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Sequence
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Detection.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The actual homotopy fiber of a stable equivalence has zero stable groups. -/
theorem fiber_stableHomotopy_subsingleton_of_stableEquivalence
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) (hf : stableEquivalences f) (d : ℤ) :
    Subsingleton (StableHomotopy (fiber f) d) := by
  have hz (z : StableHomotopy (fiber f) d) : z = 0 := by
    have hp : stableHomotopyAddHom (fiberProjection f) d z = 0 :=
      (hf d).injective ((fiberProjection_map_exact f d).apply_apply_eq_zero z |>.trans
        (map_zero (stableHomotopyAddHom f d)).symm)
    obtain ⟨y, rfl⟩ := (fiberBoundary_projection_exact f d z).mp hp
    obtain ⟨x, rfl⟩ := (hf (d+1)).surjective y
    exact (fiberBoundary_exact f d).apply_apply_eq_zero x
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Trivial stable groups of the actual fiber imply that the original map is
a stable equivalence; both injectivity and surjectivity follow from exactness. -/
theorem stableEquivalence_of_fiber_stableHomotopy_subsingleton
    {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ d : ℤ, Subsingleton (StableHomotopy (fiber f) d)) :
    stableEquivalences f := by
  intro d
  constructor
  · intro x y hxy
    change stableHomotopyAddHom f d x = stableHomotopyAddHom f d y at hxy
    have h : stableHomotopyAddHom f d (x-y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := (fiberProjection_map_exact f d (x-y)).mp h
    letI := hf d
    have hz0 : z = 0 := Subsingleton.elim _ _
    apply sub_eq_zero.mp
    rw [← hz, hz0, map_zero]
  · have hall : Function.Surjective (stableHomotopyAddHom f ((d-1)+1)) := by
      intro y'
      letI := hf (d-1)
      exact (fiberBoundary_exact f (d-1) y').mp (Subsingleton.elim _ _)
    have hd : d - 1 + 1 = d := by omega
    rw [hd] at hall
    exact hall

/-- A strict map is a stable equivalence exactly when its actual homotopy
fiber is stably trivial. -/
theorem stableEquivalence_iff_fiber_stableHomotopy_subsingleton
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences f ↔
      ∀ d : ℤ, Subsingleton (StableHomotopy (fiber f) d) :=
  ⟨fiber_stableHomotopy_subsingleton_of_stableEquivalence f,
    stableEquivalence_of_fiber_stableHomotopy_subsingleton f⟩

/-- The actual fiber detects stable equivalences as zero objects in the
original ordinary localization. -/
theorem stableEquivalence_iff_source_fiber_isZero {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) :
    stableEquivalences f ↔ IsZero (sourceLocalization.obj (fiber f)) := by
  rw [source_isZero_iff_stableHomotopy_subsingleton,
    stableEquivalence_iff_fiber_stableHomotopy_subsingleton]

end KIP126.StableHomotopy.Implementation.Prespectrum
