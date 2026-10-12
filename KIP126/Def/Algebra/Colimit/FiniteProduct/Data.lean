module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace KIP126.Core.DirectLimit

universe u v

variable {J : Type v} (G : J → ℕ → Type u) [∀ j i, Monoid (G j i)]
    (f : ∀ j i k, i ≤ k → G j i →* G j k)
    [∀ j, DirectedSystem (G j) (fun i k h => f j i k h)]

/-- Pointwise transition maps for a family of actual sequential systems. -/
def piTransition (i k : ℕ) (h : i ≤ k) : (∀ j, G j i) →* ∀ j, G j k where
  toFun x j := f j i k h (x j)
  map_one' := funext fun j => map_one (f j i k h)
  map_mul' x y := funext fun j => map_mul (f j i k h) (x j) (y j)

instance piDirectedSystem :
    DirectedSystem (fun i => ∀ j, G j i) (fun i k h => piTransition G f i k h) where
  map_self {i} x := funext fun j => DirectedSystem.map_self (f := fun i k h => f j i k h) (x j)
  map_map {k m i} him hmk x :=
    funext fun j => DirectedSystem.map_map (f := fun i k h => f j i k h) him hmk (x j)

/-- Coordinate projection from the colimit of a pointwise product system. -/
def piComponent (j : J) :
    _root_.DirectLimit (fun i => ∀ j, G j i) (piTransition G f) →
      _root_.DirectLimit (G j) (f j) :=
  _root_.DirectLimit.lift (piTransition G f) (fun i x => ⟦⟨i,x j⟩⟧)
    (fun i k h x => _root_.DirectLimit.eq_of_le ⟨i,x j⟩ k h)

/-- The canonical comparison from a sequential colimit of products to the
product of the sequential colimits. -/
def piComparison :
    _root_.DirectLimit (fun i => ∀ j, G j i) (piTransition G f) →
      ∀ j, _root_.DirectLimit (G j) (f j) :=
  fun x j => piComponent G f j x

end KIP126.Core.DirectLimit
