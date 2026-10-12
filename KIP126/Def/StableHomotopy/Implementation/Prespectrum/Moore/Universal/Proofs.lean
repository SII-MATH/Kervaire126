module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Orthogonality.Proofs
public import KIP126.Def.StableHomotopy.Completion.Moore.Universal.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual source Milnor projections determine maps from bounded scalar
torsion objects, because the represented difference map is surjective. -/
theorem sourceMooreCompletion_hom_ext_of_torsion (p : ℕ) (X U : SourceCategory.{u})
    {N : ℕ} (hU : p ^ N • 𝟙 U = 0) {a b : U ⟶ sourceMooreCompletion p X}
    (hab : ∀ k, a ≫ (sourceHomotopyLimitWitness (moorePowerSequence p X)).π k =
      b ≫ (sourceHomotopyLimitWitness (moorePowerSequence p X)).π k) : a = b :=
  (sourceHomotopyLimitWitness (moorePowerSequence p X)).hom_ext_of_surjective
    (moorePowerSequence_postcomp_oneSubShift_surjective_of_torsion p X (U⟦(1 : ℤ)⟧)
      (nsmul_pow_id_shift_eq_zero p hU 1)) hab

/-- The actual source Moore unit is an equivalence on maps from each
bounded scalar torsion object. -/
theorem sourceMooreCompletionUnit_postcomp_bijective_of_torsion
    (p : ℕ) (X U : SourceCategory.{u}) {N : ℕ} (hU : p ^ N • 𝟙 U = 0) :
    Function.Bijective (fun a : U ⟶ X => a ≫ sourceMooreCompletionUnit p X) := by
  constructor
  · intro a b hab
    apply moorePowerSequence_inclusion_injective_of_torsion p X U hU (Nat.le_refl N)
    have h := congrArg
      (fun f => f ≫ (sourceHomotopyLimitWitness (moorePowerSequence p X)).π N) hab
    simpa only [Category.assoc, sourceMooreCompletionUnit_projection] using h
  · intro a
    obtain ⟨b, hb, _⟩ := moorePowerSequence_existsUnique_compatible_of_torsion p X U hU
      (fun k => a ≫ (sourceHomotopyLimitWitness (moorePowerSequence p X)).π k)
      (fun k => by rw [Category.assoc, SequentialHomotopyLimit.π_step])
    refine ⟨b, sourceMooreCompletion_hom_ext_of_torsion p X U hU (fun k => ?_)⟩
    rw [Category.assoc, sourceMooreCompletionUnit_projection]
    exact hb k

/-- The actual chosen source cofiber of the constructed Moore unit has
invertible scalar action. -/
theorem sourceMooreCompletionUnit_cofiber_scalar_isIso (p : ℕ) (X : SourceCategory.{u}) :
    IsIso (p • 𝟙 (HasFunctorialCofiber.cofib (sourceMooreCompletionUnit p X))) := by
  apply isIso_nsmul_id_cofiber_of_torsion_postcomp_bijective p
  intro U hU
  exact sourceMooreCompletionUnit_postcomp_bijective_of_torsion p X U hU

/-- Every source map into an object orthogonal to scalar-invertible
objects extends uniquely across the actual Moore unit. -/
theorem sourceMooreCompletionUnit_precomp_bijective
    (p : ℕ) (X L : SourceCategory.{u})
    (hL : ∀ U : SourceCategory.{u}, IsIso (p • 𝟙 U) → Subsingleton (U ⟶ L)) :
    Function.Bijective (fun a : sourceMooreCompletion p X ⟶ L =>
      sourceMooreCompletionUnit p X ≫ a) := by
  letI := sourceMooreCompletionUnit_cofiber_scalar_isIso p X
  exact precomp_bijective_of_scalar_cofiber_orthogonal p _ L hL

/-- For an already orthogonal source object, the actual Moore unit is
an isomorphism. This uses its proved universal property and locality. -/
theorem sourceMooreCompletionUnit_isIso_of_orthogonal
    (p : ℕ) (X : SourceCategory.{u})
    (hX : ∀ U : SourceCategory.{u}, IsIso (p • 𝟙 U) → Subsingleton (U ⟶ X)) :
    IsIso (sourceMooreCompletionUnit p X) := by
  let η := sourceMooreCompletionUnit p X
  obtain ⟨r, hr⟩ := (sourceMooreCompletionUnit_precomp_bijective p X X hX).surjective (𝟙 X)
  change η ≫ r = 𝟙 X at hr
  have hη : Function.Injective (fun a : sourceMooreCompletion p X ⟶ sourceMooreCompletion p X =>
      η ≫ a) := (sourceMooreCompletionUnit_precomp_bijective p X _ (fun U hU => by
        letI := hU
        exact sourceMooreCompletion_hom_subsingleton p X U)).injective
  have hr' : r ≫ η = 𝟙 _ := by
    apply hη
    change η ≫ (r ≫ η) = η ≫ 𝟙 _
    rw [← Category.assoc, hr, Category.id_comp, Category.comp_id]
  exact ⟨⟨r, hr, hr'⟩⟩

end KIP126.StableHomotopy.Implementation
