module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Level.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Classical

universe u v

set_option backward.isDefEq.respectTransparency false

@[simp] theorem mappingCylinderMk_point {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (t : I) :
    mappingCylinderMk f n (.inl ((X.level n).point,t)) = (mappingCylinderLevel f n).point := by
  apply Quotient.sound
  simp [mappingCylinderNormalize]

@[simp] theorem mappingCylinderMk_top {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : X.level n) :
    mappingCylinderMk f n (.inl (x,1)) = mappingCylinderMk f n (.inr (f.level n x)) := by
  apply Quotient.sound
  by_cases hx : x = (X.level n).point
  · subst x
    simp [mappingCylinderNormalize, f.point]
  · simp [mappingCylinderNormalize, hx]

/-- The quotient has precisely the displayed normalization fibers. -/
theorem mappingCylinderMk_eq_iff {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (a b : mappingCylinderRaw f n) :
    mappingCylinderMk f n a = mappingCylinderMk f n b ↔
      mappingCylinderNormalize f n a = mappingCylinderNormalize f n b :=
  Quotient.eq''

/-- The two geometric gluing equations suffice for descent. -/
theorem mappingCylinder_normalize_invariant {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) {Z : Type v} (g : mappingCylinderRaw f n → Z)
    (hp : ∀ t, g (.inl ((X.level n).point,t)) = g (.inr (Y.level n).point))
    (ht : ∀ x, g (.inl (x,1)) = g (.inr (f.level n x)))
    (a : mappingCylinderRaw f n) : g (mappingCylinderNormalize f n a) = g a := by
  rcases a with ⟨x,t⟩ | y
  · by_cases hx : x = (X.level n).point
    · subst x
      simpa [mappingCylinderNormalize] using (hp t).symm
    · by_cases h : t = 1
      · subst t
        simpa [mappingCylinderNormalize, hx] using (ht x).symm
      · simp [mappingCylinderNormalize, hx, h]
  · rfl

theorem mappingCylinderMk_surjective {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    Function.Surjective (mappingCylinderMk f n) := @Quotient.mk'_surjective _ (Setoid.ker (mappingCylinderNormalize f n))

end KIP126.StableHomotopy.Implementation.Prespectrum
