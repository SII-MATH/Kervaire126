module

public import KIP126.Def.StableHomotopy.Completion.Moore.Data
public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u v

section Tower

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasFunctorialCofiber (C := C)]

/-- The actual cofiber inclusions are compatible with the reduction maps. -/
theorem moorePowerSequence_inclusion_step (p : ℕ) (X : C) (k : ℕ) :
    HasFunctorialCofiber.cofibι (moorePowerMap p X (k + 1)) ≫
      (moorePowerSequence p X).step k =
        HasFunctorialCofiber.cofibι (moorePowerMap p X k) := by
  simpa only [moorePowerSequence, Category.id_comp] using
    (HasFunctorialCofiber.cofibMap_ι (moorePowerMap p X (k + 1))
      (moorePowerMap p X k) (p • 𝟙 X) (𝟙 X) _).symm

end Tower

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- Taking the cofiber of a scalar self-map retains the original lower
homotopy bound. -/
theorem moorePowerSequence_homotopy_subsingleton (p : ℕ) (X : C) (N : ℤ)
    (hX : ∀ n, n < N → Subsingleton (HomotopyGroup n X))
    (k : ℕ) (n : ℤ) (hn : n < N) :
    Subsingleton (HomotopyGroup n ((moorePowerSequence p X).obj k)) := by
  let T := HoCofiberSequence.ofMorphism (moorePowerMap p X k)
  letI : Subsingleton (HomotopyGroup n T.Y) := hX n hn
  letI : Subsingleton (HomotopyGroup (n - 1) T.X) := hX (n - 1) (by omega)
  have hz (z : HomotopyGroup n T.Z) : z = 0 := by
    obtain ⟨y, hy⟩ := (les_homotopy_exact_g T n z).mp (Subsingleton.elim _ _)
    rw [show y = 0 from Subsingleton.elim _ _] at hy
    simpa using hy.symm
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- In the first possible nonzero degree, the cofiber inclusion surjects
on homotopy groups because the preceding homotopy group vanishes. -/
theorem moorePowerSequence_inclusion_surjective (p : ℕ) (X : C) (N : ℤ)
    (hX : ∀ n, n < N → Subsingleton (HomotopyGroup n X)) (k : ℕ) :
    Function.Surjective (inducedMap (HasFunctorialCofiber.cofibι (moorePowerMap p X k)) N) := by
  let T := HoCofiberSequence.ofMorphism (moorePowerMap p X k)
  letI : Subsingleton (HomotopyGroup (N - 1) T.X) := hX (N - 1) (by omega)
  intro z
  exact (les_homotopy_exact_g T N z).mp (Subsingleton.elim _ _)

/-- Reduction maps are surjective in the boundary degree. Thus the Moore
tower has no derived-limit obstruction there, without a finiteness premise. -/
theorem moorePowerSequence_step_surjective (p : ℕ) (X : C) (N : ℤ)
    (hX : ∀ n, n < N → Subsingleton (HomotopyGroup n X)) (k : ℕ) :
    Function.Surjective (inducedMap ((moorePowerSequence p X).step k) N) := by
  intro z
  obtain ⟨x, hx⟩ := moorePowerSequence_inclusion_surjective p X N hX k z
  refine ⟨inducedMap (HasFunctorialCofiber.cofibι (moorePowerMap p X (k + 1))) N x, ?_⟩
  change (x ≫ _) ≫ _ = z
  rw [Category.assoc, moorePowerSequence_inclusion_step]
  exact hx

variable [HasProductsOfShape ℕ C]

/-- The constructed Moore completion has a unit with its actual compatible
cofiber projections, obtained from exactness of its Milnor triangle. -/
theorem mooreCompletion_exists_unit (p : ℕ) (X : C) :
    ∃ u : X ⟶ mooreCompletion p X, ∀ k,
      u ≫ (moorePowerSequence p X).homotopyLimitWitness.π k =
        HasFunctorialCofiber.cofibι (moorePowerMap p X k) :=
  (moorePowerSequence p X).homotopyLimitWitness.exists_lift
    (fun k => HasFunctorialCofiber.cofibι (moorePowerMap p X k))
    (moorePowerSequence_inclusion_step p X)

/-- The Moore completion preserves the exact lower bound, including the
critical preceding degree where the Milnor derived limit could contribute. -/
theorem mooreCompletion_homotopy_subsingleton (p : ℕ) (X : C) (N : ℤ)
    (hX : ∀ n, n < N → Subsingleton (HomotopyGroup n X))
    (n : ℤ) (hn : n < N) : Subsingleton (HomotopyGroup n (mooreCompletion p X)) := by
  let D := moorePowerSequence p X
  letI : ∀ k, Subsingleton (HomotopyGroup n (D.obj k)) :=
    fun k => moorePowerSequence_homotopy_subsingleton p X N hX k n hn
  apply D.homotopyLimitWitness.homotopy_subsingleton_of_surjective n
  intro k
  by_cases h : n + 1 = N
  · rw [h]
    exact moorePowerSequence_step_surjective p X N hX k
  · letI := moorePowerSequence_homotopy_subsingleton p X N hX k (n + 1) (by omega)
    exact Function.surjective_to_subsingleton _

/-- Boundedness below follows for the explicitly constructed Moore completion. -/
theorem mooreCompletion_boundedBelow (p : ℕ) {X : C} (hX : BoundedBelow X) :
    BoundedBelow (mooreCompletion p X) := by
  obtain ⟨N, hN⟩ := hX
  exact ⟨N, mooreCompletion_homotopy_subsingleton p X N hN⟩

end KIP126.StableHomotopy
