module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Group.Hom.Basic

@[expose] public section

namespace KIP126.Core.DirectLimit

universe u

/-- If every successive transition is a homomorphism followed by the
same power operation, that power is invertible on the actual direct limit. -/
theorem pow_bijective_of_successor_eq_pow {G : ℕ → Type u} [∀ i, CommGroup (G i)]
    (f : ∀ i j, i ≤ j → G i →* G j)
    [DirectedSystem G (fun i j h => f i j h)] (p : ℕ)
    (r : ∀ i, G i →* G (i + 1))
    (hr : ∀ i x, f i (i + 1) (Nat.le_succ i) x = (r i x) ^ p) :
    Function.Bijective (fun x : _root_.DirectLimit G f => x ^ p) := by
  constructor
  · change Function.Injective (powMonoidHom p : _root_.DirectLimit G f →* _)
    apply (injective_iff_map_eq_one
      (powMonoidHom p : _root_.DirectLimit G f →* _root_.DirectLimit G f)).mpr
    intro x
    induction x using _root_.DirectLimit.induction with
    | ih i x =>
      intro hx
      change (⟦⟨i,x⟩⟧ : _root_.DirectLimit G f) ^ p = 1 at hx
      rw [_root_.DirectLimit.npow_def] at hx
      obtain ⟨j,hij,hj⟩ := (_root_.DirectLimit.exists_eq_one (f := f) ⟨i,x ^ p⟩).mp hx
      rw [_root_.DirectLimit.eq_of_le (f := f) ⟨i,x⟩ j hij]
      apply (_root_.DirectLimit.exists_eq_one (f := f) _).mpr
      refine ⟨j+1,Nat.le_succ j,?_⟩
      rw [hr, ← map_pow, ← map_pow, hj, map_one]
  · intro x
    induction x using _root_.DirectLimit.induction with
    | ih i x =>
      refine ⟨⟦⟨i+1,r i x⟩⟧,?_⟩
      change (⟦⟨i+1,r i x⟩⟧ : _root_.DirectLimit G f) ^ p = ⟦⟨i,x⟩⟧
      rw [_root_.DirectLimit.npow_def, ← hr]
      exact (_root_.DirectLimit.eq_of_le (f := f) ⟨i,x⟩ (i+1) (Nat.le_succ i)).symm

end KIP126.Core.DirectLimit
