module

public import KIP126.Def.Algebra.Colimit.FiniteProduct.Data
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace KIP126.Core.DirectLimit

universe u v

variable {J : Type v} (G : J → ℕ → Type u) [∀ j i, Monoid (G j i)]
    (f : ∀ j i k, i ≤ k → G j i →* G j k)
    [∀ j, DirectedSystem (G j) (fun i k h => f j i k h)]

theorem piComparison_injective [Fintype J] : Function.Injective (piComparison G f) := by
  classical
  intro x y h
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      have hh (j : J) : ∃ (n : ℕ) (hx : x.1 ≤ n) (hy : y.1 ≤ n),
          f j x.1 n hx (x.2 j) = f j y.1 n hy (y.2 j) :=
        Quotient.exact (congrFun h j)
      choose n hx hy he using hh
      let N := max (max x.1 y.1) (Finset.univ.sup n)
      have hxN : x.1 ≤ N := (le_max_left _ _).trans (le_max_left _ _)
      have hyN : y.1 ≤ N := (le_max_right _ _).trans (le_max_left _ _)
      have hnN (j : J) : n j ≤ N :=
        (Finset.le_sup (f := n) (Finset.mem_univ j)).trans (le_max_right _ _)
      apply Quotient.sound
      refine ⟨N,hxN,hyN,funext fun j => ?_⟩
      change f j x.1 N hxN (x.2 j) = f j y.1 N hyN (y.2 j)
      calc
        _ = f j (n j) N (hnN j) (f j x.1 (n j) (hx j) (x.2 j)) :=
          (DirectedSystem.map_map (f := fun i k h => f j i k h) (hx j) (hnN j) _).symm
        _ = f j (n j) N (hnN j) (f j y.1 (n j) (hy j) (y.2 j)) := congrArg _ (he j)
        _ = _ := DirectedSystem.map_map (f := fun i k h => f j i k h) (hy j) (hnN j) _

theorem piComparison_surjective [Fintype J] : Function.Surjective (piComparison G f) := by
  classical
  intro y
  choose n x hx using fun j => _root_.DirectLimit.exists_eq_mk (f j) (y j)
  let N := Finset.univ.sup n
  have hn (j : J) : n j ≤ N := Finset.le_sup (f := n) (Finset.mem_univ j)
  refine ⟨⟦⟨N,fun j => f j (n j) N (hn j) (x j)⟩⟧, funext fun j => ?_⟩
  change (⟦⟨N, f j (n j) N (hn j) (x j)⟩⟧ : _root_.DirectLimit (G j) (f j)) = y j
  exact (_root_.DirectLimit.mk_apply (n j) N (x j) (hn j)).trans (hx j).symm

/-- A finite family admits one common stage for its representatives and
their equalities; hence the actual sequential colimit commutes with its product. -/
theorem piComparison_bijective [Finite J] : Function.Bijective (piComparison G f) := by
  letI := Fintype.ofFinite J
  exact ⟨piComparison_injective G f, piComparison_surjective G f⟩

end KIP126.Core.DirectLimit
