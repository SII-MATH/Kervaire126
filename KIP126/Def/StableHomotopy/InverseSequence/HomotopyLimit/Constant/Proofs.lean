module

public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Constant.Data
public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasProductsOfShape ℕ C]

/-- Epimorphic transitions make the actual Milnor difference map
epimorphic. In a pretriangulated category these transitions split. -/
theorem InverseSequence.oneSubShift_epi_of_step_epi (D : InverseSequence C)
    [∀ n, Epi (D.step n)] : Epi D.oneSubShift := by
  have hsurj : Function.Surjective (fun a : ∏ᶜ D.obj ⟶ ∏ᶜ D.obj => a ≫ D.oneSubShift) := by
    apply D.postcomp_oneSubShift_surjective_of_surjective
    intro n a
    letI := isSplitEpi_of_epi (D.step n)
    refine ⟨a ≫ section_ (D.step n), ?_⟩
    simp
  obtain ⟨s, hs⟩ := hsurj (𝟙 _)
  change s ≫ D.oneSubShift = 𝟙 _ at hs
  constructor
  intro Z a b hab
  calc
    a = s ≫ D.oneSubShift ≫ a := by rw [← Category.assoc, hs, Category.id_comp]
    _ = s ≫ D.oneSubShift ≫ b := by rw [hab]
    _ = b := by rw [← Category.assoc, hs, Category.id_comp]

/-- When all transition morphisms are epimorphic, the Milnor projections
are jointly monomorphic, with the derived-limit term proved to vanish. -/
theorem SequentialHomotopyLimit.hom_ext_of_step_epi
    {D : InverseSequence C} {L W : C} (H : SequentialHomotopyLimit D L)
    [∀ n, Epi (D.step n)] {a b : W ⟶ L}
    (hab : ∀ n, a ≫ H.π n = b ≫ H.π n) : a = b := by
  let T := Triangle.mk H.toProduct D.oneSubShift H.boundary
  letI : Epi T.mor₂ := D.oneSubShift_epi_of_step_epi
  have hz : T.mor₃ = 0 := T.mor₃_eq_zero_of_epi₂ H.distinguished inferInstance
  letI : Mono H.toProduct := T.mono₁ H.distinguished hz
  apply (cancel_mono H.toProduct).mp
  apply Pi.hom_ext
  intro n
  exact (Category.assoc _ _ _).trans ((hab n).trans (Category.assoc _ _ _).symm)

/-- All projections in the identity sequence agree. -/
theorem SequentialHomotopyLimit.constant_π_eq {X L : C}
    (H : SequentialHomotopyLimit (InverseSequence.constant X) L) (n : ℕ) :
    H.π n = H.π 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := H.π_step n
    have hn' : H.π (n + 1) = H.π n := by
      simpa only [InverseSequence.constant, Category.comp_id] using hn
    exact hn'.trans ih

/-- A lift of the actual diagonal into the Milnor limit of the constant
identity sequence is an isomorphism, with inverse its zeroth projection. -/
theorem SequentialHomotopyLimit.constant_isIso_of_projections {X L : C}
    (H : SequentialHomotopyLimit (InverseSequence.constant X) L)
    (u : X ⟶ L) (hu : ∀ n, u ≫ H.π n = 𝟙 X) : IsIso u := by
  have hi : H.π 0 ≫ u = 𝟙 L := by
    letI : ∀ n, Epi ((InverseSequence.constant X).step n) := fun _ =>
      inferInstanceAs (Epi (𝟙 X))
    apply H.hom_ext_of_step_epi
    intro n
    change ((H.π 0 : L ⟶ X) ≫ u) ≫ (H.π n : L ⟶ X) = 𝟙 L ≫ (H.π n : L ⟶ X)
    rw [Category.assoc, hu n]
    simpa only [Category.comp_id, Category.id_comp] using (H.constant_π_eq n).symm
  exact ⟨⟨H.π 0, hu 0, hi⟩⟩

/-- The constant tower has its original object as its Milnor homotopy
limit, including all canonical diagonal projection equations. -/
theorem SequentialHomotopyLimit.constant_exists_iso {X L : C}
    (H : SequentialHomotopyLimit (InverseSequence.constant X) L) :
    ∃ e : X ≅ L, ∀ n, e.hom ≫ H.π n = 𝟙 X := by
  obtain ⟨u, hu⟩ := H.exists_lift (fun _ => 𝟙 X) (by
    intro n
    exact Category.id_comp _)
  letI := H.constant_isIso_of_projections u hu
  exact ⟨asIso u, hu⟩

end KIP126.StableHomotopy
