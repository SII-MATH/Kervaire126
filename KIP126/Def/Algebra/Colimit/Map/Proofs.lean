module

public import Mathlib.Algebra.Colimit.DirectLimit

@[expose] public section

namespace KIP126.Core.DirectLimit

universe u v

variable {G : ℕ → Type u} {H : ℕ → Type v}
    [∀ i, Monoid (G i)] [∀ i, Monoid (H i)]
    (f : ∀ i j, i ≤ j → G i →* G j) (g : ∀ i j, i ≤ j → H i →* H j)
    [DirectedSystem G (fun i j h => f i j h)] [DirectedSystem H (fun i j h => g i j h)]
    (e : ∀ i, G i → H i)
    (he : ∀ i j h x, g i j h (e i x) = e j (f i j h x))

/-- A compatible family of levelwise bijections induces a bijection on the
actual sequential colimit quotient. -/
theorem map_bijective (hb : ∀ i, Function.Bijective (e i)) :
    Function.Bijective (_root_.DirectLimit.map f g e he) := by
  constructor
  · intro x y
    induction x, y using _root_.DirectLimit.induction₂ with
    | ih i x y =>
      intro h
      obtain ⟨j,hx,hy,hxy⟩ := Quotient.exact h
      apply Quotient.sound
      refine ⟨j,hx,hy,(hb j).injective ?_⟩
      exact (he i j hx x).symm.trans (hxy.trans (he i j hy y))
  · intro y
    induction y using _root_.DirectLimit.induction with
    | ih i y =>
      obtain ⟨x,rfl⟩ := (hb i).surjective y
      exact ⟨⟦⟨i,x⟩⟧,rfl⟩

end KIP126.Core.DirectLimit
