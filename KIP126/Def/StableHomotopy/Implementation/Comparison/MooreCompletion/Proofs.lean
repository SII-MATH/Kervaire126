module

public import KIP126.Def.StableHomotopy.Implementation.Comparison.Conservativity.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Locality.Proofs
public import KIP126.Def.StableHomotopy.Completion.Moore.Universal.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open KIP126.StableHomotopy.Cohomology

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C]
  {H : Mod2EilenbergMacLane (C := C)}
  (S : SourceComparison H) (R : Mod2RingStructure H)
  [(tensorLeft H.HF2).CommShift ℤ]

include S R in
/-- Every two-invertible object in the specified HF₂-local realization
category is zero, by the actual coefficient-smash conservativity theorem. -/
theorem SourceComparison.isZero_of_two_isIso (X : C) [IsIso (2 • 𝟙 X)] :
    IsZero X := by
  letI := S.tensorLeft_hf2_reflectsIsomorphisms R
  exact isZero_of_two_isIso_of_hf2_conservative H R X

variable [HasProductsOfShape ℕ C]

include S R in
/-- In the specified HF₂-local category, any unit with the actual Moore
projections is an isomorphism. This is Moore completeness and does not
assert acyclicity of the HF₂-Adams residual tower. -/
theorem SourceComparison.mooreCompletion_unit_isIso (X : C)
    (u : X ⟶ mooreCompletion 2 X)
    (hu : ∀ k, u ≫ (moorePowerSequence 2 X).homotopyLimitWitness.π k =
      HasFunctorialCofiber.cofibι (moorePowerMap 2 X k)) : IsIso u := by
  letI := mooreCompletion_unit_cofiber_scalar_isIso 2 X u hu
  have hz := S.isZero_of_two_isIso R (HasFunctorialCofiber.cofib u)
  exact (Triangle.isZero₃_iff_isIso₁ _ (HasFunctorialCofiber.cofib_distinguished u)).mp hz

include S R in
/-- Every object in the specified HF₂-local category is isomorphic to its
constructed Moore completion, with all prescribed cofiber projections. -/
theorem SourceComparison.mooreCompletion_exists_iso (X : C) :
    ∃ e : X ≅ mooreCompletion 2 X, ∀ k,
      e.hom ≫ (moorePowerSequence 2 X).homotopyLimitWitness.π k =
        HasFunctorialCofiber.cofibι (moorePowerMap 2 X k) := by
  obtain ⟨u, hu⟩ := mooreCompletion_exists_unit 2 X
  letI := S.mooreCompletion_unit_isIso R X u hu
  exact ⟨asIso u, hu⟩

end KIP126.StableHomotopy.Implementation
