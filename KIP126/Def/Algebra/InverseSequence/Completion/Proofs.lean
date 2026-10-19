module

public import KIP126.Def.Algebra.InverseSequence.Finite.Proofs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.Abel

@[expose] public section

namespace KIP126.Core.InverseSequence

universe u v

variable {A : Type u} [AddCommGroup A]
variable {B : ℕ → Type v} [∀ n, AddCommGroup (B n)]

/-- If `1 - shift` is surjective on a residual sequence, every Cauchy
sequence for its image filtration has a limit. The limit is not yet claimed
unique, since separation requires control of the kernels of the projections. -/
theorem exists_limit_of_surjective_sub_shift
    (p : ∀ n, B n →+ A) (f : ∀ n, B (n + 1) →+ B n)
    (hp : ∀ n b, p n (f n b) = p (n + 1) b)
    (hsurj : Function.Surjective (fun x : ∀ n, B n => fun n => x n - f n (x (n + 1))))
    (a : ℕ → A) (ha : ∀ n, ∃ b, p n b = a (n + 1) - a n) :
    ∃ x : A, ∀ n, ∃ b, p n b = x - a n := by
  classical
  choose d hd using ha
  obtain ⟨b, hb⟩ := hsurj d
  have heq (n : ℕ) : a n + p n (b n) = a (n + 1) + p (n + 1) (b (n + 1)) := by
    have h := congrArg (p n) (congrFun hb n)
    simp only [map_sub, hp, hd] at h
    calc
      a n + p n (b n) = a n + (p n (b n) - p (n + 1) (b (n + 1))) +
          p (n + 1) (b (n + 1)) := by abel
      _ = a (n + 1) + p (n + 1) (b (n + 1)) := by rw [h]; abel
  have hconstant (n : ℕ) : a n + p n (b n) = a 0 + p 0 (b 0) := by
    induction n with
    | zero => rfl
    | succ n ih => exact (heq n).symm.trans ih
  refine ⟨a 0 + p 0 (b 0), fun n => ⟨b n, ?_⟩⟩
  rw [← hconstant n]
  abel

/-- Finite projection kernels make the lifting fibers finite. Compatible
lifts then exist, so injectivity of `1 - shift` forces the intersection of
all residual images to be zero. The residual groups themselves may be infinite. -/
theorem eq_zero_of_mem_ranges_of_injective_sub_shift
    (p : ∀ n, B n →+ A) (f : ∀ n, B (n + 1) →+ B n)
    (hp : ∀ n b, p n (f n b) = p (n + 1) b)
    (hinj : Function.Injective (fun x : ∀ n, B n => fun n => x n - f n (x (n + 1))))
    [∀ n, Finite (p n).ker]
    (a : A) (ha : ∀ n, ∃ b, p n b = a) : a = 0 := by
  classical
  choose b hb using ha
  let T (n : ℕ) := {y : B n // p n y = a}
  have hfin (n : ℕ) : Finite (T n) := by
    let g : T n → (p n).ker := fun y => ⟨y.val - b n, by
      change p n (y.val - b n) = 0
      rw [map_sub, y.property, hb n, sub_self]⟩
    exact Finite.of_injective g (fun y z h => Subtype.ext
      (sub_left_injective (congrArg Subtype.val h)))
  obtain ⟨y, hy⟩ := exists_compatible_of_finite 0 (fun n _ => T n)
    (fun n _ z => ⟨f n z.val, (hp n z.val).trans z.property⟩)
    (fun n _ => hfin n) (fun n _ => ⟨⟨b n, hb n⟩⟩)
  have hyzero : (fun n => (y n (Nat.zero_le n)).val) = fun n => (0 : B n) := by
    apply hinj
    funext n
    have h := congrArg Subtype.val (hy n (Nat.zero_le n))
    dsimp only at h
    change (y n _).val - f n (y (n + 1) _).val = 0 - f n 0
    rw [← h, map_zero, sub_self, sub_self]
  have h0 := congrFun hyzero 0
  exact (y 0 (Nat.zero_le 0)).property.symm.trans (h0 ▸ (p 0).map_zero)

end KIP126.Core.InverseSequence
