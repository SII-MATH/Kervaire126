module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Sequence
public import Mathlib.GroupTheory.QuotientGroup.Finite

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- Vanishing of the two adjacent original stable groups forces vanishing
of the actual homotopy fiber's stable group. -/
theorem fiber_stableHomotopy_subsingleton {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (d : ℤ) [Subsingleton (StableHomotopy Y (d+1))]
    [Subsingleton (StableHomotopy X d)] :
    Subsingleton (StableHomotopy (fiber f) d) := by
  have hz (z : StableHomotopy (fiber f) d) : z = 0 := by
    obtain ⟨y, rfl⟩ := (fiberBoundary_projection_exact f d z).mp (Subsingleton.elim _ _)
    rw [show y = 0 from Subsingleton.elim _ _, map_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The actual homotopy fiber of maps between bounded-below prespectra
vanishes below the expected shifted lower bound. -/
theorem fiber_stableHomotopy_vanishes_below {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (a b : ℤ)
    (hX : ∀ d : ℤ, d < a → Subsingleton (StableHomotopy X d))
    (hY : ∀ d : ℤ, d < b → Subsingleton (StableHomotopy Y d))
    (d : ℤ) (hd : d < min a (b-1)) :
    Subsingleton (StableHomotopy (fiber f) d) := by
  letI := hX d (lt_of_lt_of_le hd (min_le_left _ _))
  letI := hY (d+1) (by have := min_le_right a (b-1); omega)
  exact fiber_stableHomotopy_subsingleton f d

/-- Finiteness of the adjacent original stable groups gives finiteness of
the actual homotopy fiber group, without an abstract triangle premise. -/
theorem fiber_stableHomotopy_finite {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (d : ℤ) [Finite (StableHomotopy Y (d+1))] [Finite (StableHomotopy X d)] :
    Finite (StableHomotopy (fiber f) d) := by
  classical
  letI := Fintype.ofFinite (StableHomotopy Y (d+1))
  letI := Fintype.ofFinite (StableHomotopy X d)
  letI := AddGroup.fintypeOfKerLeRange (fiberBoundary f d)
    (stableHomotopyAddHom (fiberProjection f) d) (by
      intro z hz
      exact (fiberBoundary_projection_exact f d z).mp hz)
  infer_instance

/-- The next target group surjects onto the kernel of the actual fiber
projection; hence finiteness of that target group makes this kernel finite. -/
theorem fiberProjection_stableHomotopy_finite_kernel {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (d : ℤ) [Finite (StableHomotopy Y (d+1))] :
    Finite (stableHomotopyAddHom (fiberProjection f) d).ker := by
  let g : StableHomotopy Y (d+1) → (stableHomotopyAddHom (fiberProjection f) d).ker :=
    fun y => ⟨fiberBoundary f d y, (fiberBoundary_projection_exact f d).apply_apply_eq_zero y⟩
  apply Finite.of_surjective g
  intro z
  obtain ⟨y, hy⟩ := (fiberBoundary_projection_exact f d z.val).mp z.property
  exact ⟨y, Subtype.ext hy⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
