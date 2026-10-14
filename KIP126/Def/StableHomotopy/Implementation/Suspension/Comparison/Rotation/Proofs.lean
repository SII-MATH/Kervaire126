module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Data
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Interchange.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open Topology KIP126.Topology.Cube
open scoped unitInterval Topology.Homotopy

universe u

/-- Successive orientations alternate the clockwise and counterclockwise
quarter rotations, each through maps preserving the square boundary. -/
theorem suspensionDesuspension_signed_rotation_exists (n : ℕ) :
    ∃ R : C(I × (I × I), I × I),
      (∀ p, R (0, p) = p) ∧
      (∀ p, R (1, p) = (suspensionDesuspensionSign n p.2,
        suspensionDesuspensionSign (n + 1) p.1)) ∧
      (∀ s p, (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) →
        (R (s, p)).1 = 0 ∨ (R (s, p)).1 = 1 ∨ (R (s, p)).2 = 0 ∨ (R (s, p)).2 = 1) := by
  induction n with
  | zero =>
    obtain ⟨R, h0, h1, hb⟩ := exists_square_quarter_rotation
    exact ⟨R, h0, h1, hb⟩
  | succ n ih =>
    obtain ⟨R, h0, h1, hb⟩ := ih
    let R' : C(I × (I × I), I × I) :=
      ⟨fun z => (R (z.1, z.2.swap)).swap,
        continuous_swap.comp (R.continuous.comp
          (continuous_fst.prodMk (continuous_swap.comp continuous_snd)))⟩
    refine ⟨R', ?_, ?_, ?_⟩
    · intro p
      change (R (0, p.swap)).swap = p
      rw [h0]
      rfl
    · intro p
      change (R (1, p.swap)).swap = _
      rw [h1]
      apply Prod.ext <;> try rfl
      change suspensionDesuspensionSign n p.1 = suspensionDesuspensionSign (n + 1 + 1) p.1
      simp only [suspensionDesuspensionSign_succ, unitInterval.symm_symm]
    · intro s p hp
      have hps : p.swap.1 = 0 ∨ p.swap.1 = 1 ∨ p.swap.2 = 0 ∨ p.swap.2 = 1 := by
        simpa only [Prod.fst_swap, Prod.snd_swap, or_comm, or_left_comm, or_assoc] using hp
      have h := hb s p.swap hps
      change (R (s, p.swap)).2 = 0 ∨ (R (s, p.swap)).2 = 1 ∨
        (R (s, p.swap)).1 = 0 ∨ (R (s, p.swap)).1 = 1
      tauto

/-- Rotate the two actual suspension coordinates, including the alternating
orientation needed by the comparison and its inverse on stable classes. -/
theorem suspensionDesuspension_interchange_exists (X : Prespectrum.{u}) (n : ℕ) :
    ∃ H : C(I × ((X.level n).suspension × I), (X.level (n + 1)).suspension),
      (∀ x s t, H (0, (BasedSpace.suspensionProjection _ (x, s), t)) =
        BasedSpace.suspensionProjection _ (X.bond n (x, t), s)) ∧
      (∀ x s t, H (1, (BasedSpace.suspensionProjection _ (x, s), t)) =
        BasedSpace.suspensionProjection _ (X.bond n (x, suspensionDesuspensionSign n s),
          suspensionDesuspensionSign (n + 1) t)) ∧
      (∀ u z t, z = (X.level n).suspension.point ∨ t = 0 ∨ t = 1 →
        H (u, (z, t)) = (X.level (n + 1)).suspension.point) := by
  obtain ⟨R, h0, h1, hb⟩ := suspensionDesuspension_signed_rotation_exists n
  obtain ⟨H, hH, hHb⟩ := BasedSpace.suspensionRotationFamily_exists
    (X.level n) (X.level (n + 1)) (X.bond n)
    (X.bond_point n) (X.bond_zero n) (X.bond_one n) R hb
  refine ⟨H, ?_, ?_, hHb⟩
  · intro x s t
    rw [hH, h0]
  · intro x s t
    rw [hH, h1]

end KIP126.StableHomotopy.Implementation.Prespectrum
