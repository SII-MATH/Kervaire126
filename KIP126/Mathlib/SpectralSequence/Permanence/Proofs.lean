import KIP126.Mathlib.SpectralSequence.Permanence.Data

namespace KIP126.Core.SpectralSequence

open CategoryTheory
universe w u v

/-- Reindex pagewise permanence without assuming definitional equality of
page-number expressions. Heterogeneous equalities record only the harmless
changes of index, not additional identifications of mathematical objects. -/
theorem isPermanent_iff_indexed {R : Type u} [Ring R]
    {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
    (E : CategoryTheory.SpectralSequence (ModuleCat.{v} R) c r₀)
    (r : ℤ) (hr : r₀ ≤ r) (p : κ) (x : (E.page r hr).X p)
    (f : ℕ → ℤ) (hf : ∀ n, r₀ ≤ f n) (heq : f = iteratedPage r) :
    IsPermanent E r hr p x ↔
      ∃ y : ∀ n : ℕ, (E.page (f n) (hf n)).X p,
        HEq (y 0) x ∧ (∀ n : ℕ, y n ≠ 0) ∧
        (∀ n : ℕ, ∃ hy : ((E.page (f n) (hf n)).d p ((c (f n)).next p)) (y n) = 0,
          HEq (nextPageClass E (f n) (hf n) p (y n) hy) (y (n + 1))) := by
  subst f
  constructor
  · rintro ⟨y, hn⟩
    exact ⟨y.classAt, heq_of_eq y.classAt_zero, hn,
      fun n => ⟨y.isCycle n, heq_of_eq (y.passage n)⟩⟩
  · rintro ⟨y, h0, hn, hs⟩
    exact ⟨{
      classAt := y
      classAt_zero := eq_of_heq h0
      isCycle := fun n => (hs n).choose
      passage := fun n => eq_of_heq (hs n).choose_spec
    }, hn⟩

theorem iteratedPage_two_eq (n : ℕ) : iteratedPage 2 n = Int.ofNat (n + 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedPage_succ, ih]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    omega

end KIP126.Core.SpectralSequence
