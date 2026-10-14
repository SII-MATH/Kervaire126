module

public import KIP126.Def.Algebra.InverseSequence.Surjective.Proofs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Function.Iterate

@[expose] public section

namespace KIP126.Core.InverseSequence

open Function
open scoped BigOperators

universe u v

variable {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]

/-- A finite geometric sum for an additive endomorphism telescopes. -/
theorem sub_map_sum_iterate (s : B →+ B) (b : B) (N : ℕ) :
    (∑ k ∈ Finset.range N, (s^[k]) b) - s (∑ k ∈ Finset.range N, (s^[k]) b) =
      b - (s^[N]) b := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, map_add, Function.iterate_succ_apply']
    calc
      _ = ((∑ k ∈ Finset.range N, (s^[k]) b) - s (∑ k ∈ Finset.range N, (s^[k]) b)) +
        ((s^[N]) b - s ((s^[N]) b)) := by abel
      _ = b - s ((s^[N]) b) := by rw [ih]; abel

/-- Surjectivity of a difference operator passes to an extension whose
quotient is killed by a fixed iterate of the endomorphism. This is the
uniform eventual-image form of the Mittag-Leffler argument. -/
theorem surjective_sub_of_eventual_range
    (i : A →+ B) (t : A →+ A) (s : B →+ B)
    (hcomm : ∀ a, s (i a) = i (t a))
    (ht : Function.Surjective (fun a => a - t a)) (N : ℕ)
    (hN : ∀ b, ∃ a, i a = (s^[N]) b) :
    Function.Surjective (fun b => b - s b) := by
  intro b
  obtain ⟨a, ha⟩ := hN b
  obtain ⟨c, hc⟩ := ht a
  change c - t c = a at hc
  refine ⟨(∑ k ∈ Finset.range N, (s^[k]) b) + i c, ?_⟩
  change _ - s (_ + i c) = b
  rw [map_add, hcomm]
  calc
    _ = ((∑ k ∈ Finset.range N, (s^[k]) b) - s (∑ k ∈ Finset.range N, (s^[k]) b)) +
      (i c - i (t c)) := by abel
    _ = (b - (s^[N]) b) + i (c - t c) := by rw [sub_map_sum_iterate, map_sub]
    _ = b := by rw [hc, ha]; abel

/-- A uniformly stable image identified with a constant group eliminates
the derived-limit difference obstruction for the whole inverse sequence.
No finiteness or splitting of the displayed inclusions is needed. -/
theorem surjective_sub_shift_of_uniform_constant_image
    (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
    (A : Type v) [AddCommGroup A]
    (f : ∀ n, G (n + 1) →+ G n) (i : ∀ n, A →+ G n)
    (hcomm : ∀ n a, f n (i (n + 1) a) = i n a)
    (N : ℕ)
    (hN : ∀ (b : ∀ n, G n) n, ∃ a,
      i n a = ((fun x : ∀ n, G n => fun k => f k (x (k + 1)))^[N]) b n) :
    Function.Surjective (fun x : ∀ n, G n => fun n => x n - f n (x (n + 1))) := by
  classical
  let ip : (ℕ → A) →+ (∀ n, G n) :=
    { toFun := fun a n => i n (a n)
      map_zero' := by funext n; exact map_zero (i n)
      map_add' := by intros; funext n; exact map_add (i n) _ _ }
  let t : (ℕ → A) →+ (ℕ → A) :=
    { toFun := fun a n => a (n + 1)
      map_zero' := rfl
      map_add' := by intros; rfl }
  let s : (∀ n, G n) →+ (∀ n, G n) :=
    { toFun := fun b n => f n (b (n + 1))
      map_zero' := by funext n; exact map_zero (f n)
      map_add' := by intros; funext n; exact map_add (f n) _ _ }
  refine surjective_sub_of_eventual_range ip t s ?_ ?_ N ?_
  · intro a
    funext n
    exact hcomm n (a (n + 1))
  · exact surjective_sub_shift_of_surjective (fun _ => A)
      (fun _ => AddMonoidHom.id A) (fun _ => Function.surjective_id)
  · intro b
    refine ⟨fun n => (hN b n).choose, ?_⟩
    funext n
    exact (hN b n).choose_spec

end KIP126.Core.InverseSequence
