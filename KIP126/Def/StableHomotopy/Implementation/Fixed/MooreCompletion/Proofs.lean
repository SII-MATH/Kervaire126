module

public import KIP126.Def.StableHomotopy.Implementation.Fixed
public import KIP126.Def.StableHomotopy.Implementation.Comparison.MooreCompletion.Proofs

@[expose] public section

namespace KIP126.Def

open CategoryTheory
open KIP126.StableHomotopy

/-- Every actual Moore unit in the selected implementation is an
isomorphism. Its construction depends on the existing source-model
recognition; the assertion is Moore completeness, not Adams nilcompletion. -/
theorem fixed_mooreCompletion_unit_isIso
    (X : fixedImplementation.foundationInput.Spectrum)
    (u : X ⟶ mooreCompletion 2 X)
    (hu : ∀ k, u ≫ (moorePowerSequence 2 X).homotopyLimitWitness.π k =
      HasFunctorialCofiber.cofibι (moorePowerMap 2 X k)) : IsIso u := by
  letI := fixedImplementation.tensorInput
  exact fixedImplementation.sourceComparison.mooreCompletion_unit_isIso
    fixedImplementation.cooperationInput.ring X u hu

/-- Every object of the selected implementation has its specified Moore
completion comparison isomorphism, with the actual stage projections. -/
theorem fixed_mooreCompletion_exists_iso
    (X : fixedImplementation.foundationInput.Spectrum) :
    ∃ e : X ≅ mooreCompletion 2 X, ∀ k,
      e.hom ≫ (moorePowerSequence 2 X).homotopyLimitWitness.π k =
        HasFunctorialCofiber.cofibι (moorePowerMap 2 X k) := by
  obtain ⟨u, hu⟩ := mooreCompletion_exists_unit 2 X
  letI := fixed_mooreCompletion_unit_isIso X u hu
  exact ⟨asIso u, hu⟩

end KIP126.Def
