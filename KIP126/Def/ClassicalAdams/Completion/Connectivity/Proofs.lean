module

public import KIP126.Def.ClassicalAdams.TowerLayer.Mapping.Proofs
public import KIP126.Def.ClassicalAdams.TowerHomology.Connectivity.Proofs

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]

/-- A fixed lower bound on all coefficient layers yields a fixed ordinary
homotopy bound on the residual tower. The one-degree margin accounts for
the preceding term of the actual fiber long exact sequence. -/
theorem adamsTower_homotopy_bounded_uniform_of_layer_bound
    {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (N : ℤ)
    (hX : ∀ n : ℤ, n < N → Subsingleton (HomotopyGroup n X))
    (hlayers : ∀ s : ℕ, ∀ n : ℤ, n < N + 1 →
      Subsingleton (HomotopyGroup n (H ⊗ adamsTower unit X s))) :
    ∀ s : ℕ, ∀ n : ℤ, n < N →
      Subsingleton (HomotopyGroup n (adamsTower unit X s)) := by
  intro s
  induction s with
  | zero => exact hX
  | succ s ih =>
      intro n hn
      letI := ih n hn
      letI := hlayers s (n + 1) (by omega)
      have hsurj : Function.Surjective
          (inducedMap (adamsUnit unit (adamsTower unit X s)) (n + 1)) := by
        intro a
        exact ⟨0, Subsingleton.elim _ _⟩
      have hinj := fiberι_homotopy_injective_of_surjective
        (adamsUnit unit (adamsTower unit X s)) (n + 1) hsurj
      rw [show n + 1 - 1 = n by omega] at hinj
      exact hinj.subsingleton

variable [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

include R K B in
/-- Bounded initial ordinary homotopy and bounded initial HF₂ homology
produce one ordinary homotopy lower bound for every actual Adams stage.
The coefficient recurrence and the fiber exact sequences prove the bound;
no connective tensor closure or t-structure is assumed. -/
theorem adamsTower_exists_uniform_homotopy_bound (X : C)
    (hX : BoundedBelow X) (hHX : BoundedBelow (H.HF2 ⊗ X)) :
    ∃ N : ℤ, ∀ s : ℕ, ∀ n : ℤ, n < N →
      Subsingleton (HomotopyGroup n (adamsTower H.unit X s)) := by
  obtain ⟨NX, hNX⟩ := hX
  obtain ⟨NH, hNH⟩ := adamsTower_homology_exists_uniform_bound H R K B X hHX
  refine ⟨min NX (NH - 1), adamsTower_homotopy_bounded_uniform_of_layer_bound H.unit X _ ?_ ?_⟩
  · intro n hn
    exact hNX n (lt_of_lt_of_le hn (min_le_left _ _))
  · intro s n hn
    apply hNH s n
    have := min_le_right NX (NH - 1)
    omega

end KIP126.Classical.Adams
