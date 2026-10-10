import KIP126.Def.StableHomotopy.InverseSequence.Data

/-!
Integer-indexed descending towers with their actual finite composites.
Only the objects and adjacent arrows are input. The ordered maps are
recursively constructed, and a natural-number inverse sequence is extended
constantly through all nonpositive integer stages.
-/

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v

/-- A descending tower specified by its actual adjacent arrows. -/
structure DescendingTower (C : Type u) [Category.{v} C] where
  obj : ℤ → C
  step : ∀ k : ℤ, obj (k + 1) ⟶ obj k

namespace DescendingTower

variable {C : Type u} [Category.{v} C] (T : DescendingTower C)

/-- Compose exactly `length` adjacent arrows ending at the integer stage `k`. -/
def composite (k : ℤ) : (length : ℕ) → T.obj (k + (length : ℤ)) ⟶ T.obj k
  | 0 => eqToHom (congrArg T.obj (by simp))
  | length + 1 =>
    eqToHom (congrArg T.obj
      (by omega : k + ((length + 1 : ℕ) : ℤ) = (k + (length : ℤ)) + 1)) ≫
      T.step (k + (length : ℤ)) ≫ composite k length

/-- The actual ordered map is the composite of the intervening adjacent arrows. -/
def map (s t : ℤ) (h : s ≤ t) : T.obj t ⟶ T.obj s :=
  eqToHom (congrArg T.obj (by omega : t = s + ((t - s).toNat : ℤ))) ≫
    T.composite s (t - s).toNat

end DescendingTower

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Extend the specified inverse sequence constantly to nonpositive stages.
For `k < 0` the transition is the equality map on its actual zeroth object;
for `k ≥ 0` it is the given adjacent transition with integer-index casts. -/
def InverseSequence.toDescendingTower (D : InverseSequence C) : DescendingTower C where
  obj k := D.obj k.toNat
  step k := if hk : 0 ≤ k then
    eqToHom (congrArg D.obj (by omega : (k + 1).toNat = k.toNat + 1)) ≫
      D.step k.toNat
    else
      eqToHom (congrArg D.obj (by omega : (k + 1).toNat = k.toNat))

end KIP126.StableHomotopy
