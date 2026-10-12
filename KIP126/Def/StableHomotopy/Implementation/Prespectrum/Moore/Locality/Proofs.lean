module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.TwoComplete.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- The actual dyadic Moore unit induces bijections on cohomology with
every specified actual HF₂ coefficient shift. -/
theorem sourceMooreCompletionUnit_hf2Equivalence (X : SourceCategory.{0}) :
    HF2Equivalences (sourceMooreCompletionUnit 2 X) := by
  intro d
  apply sourceMooreCompletionUnit_precomp_bijective 2 X (sourceHF2Shift d)
  intro U hU
  letI := hU
  exact KIP126.Foundation.hom_subsingleton_of_nsmul_id_isIso U (sourceHF2Shift d) 2
    (sourceHF2Shift_two_id d)

/-- Maps into any actually HF₂-local target extend uniquely across the
constructed dyadic Moore unit. -/
theorem sourceMooreCompletionUnit_precomp_bijective_of_local
    (X L : SourceCategory.{0}) (hL : SourceIsHF2Local L) :
    Function.Bijective (fun a : sourceMooreCompletion 2 X ⟶ L =>
      sourceMooreCompletionUnit 2 X ≫ a) :=
  hL _ (sourceMooreCompletionUnit_hf2Equivalence X)

/-- An already HF₂-local actual source object is unchanged by its
constructed dyadic Moore completion. -/
theorem sourceMooreCompletionUnit_isIso_of_local
    (X : SourceCategory.{0}) (hX : SourceIsHF2Local X) :
    IsIso (sourceMooreCompletionUnit 2 X) := by
  apply sourceMooreCompletionUnit_isIso_of_orthogonal
  intro U hU
  letI := hU
  exact hX.hom_subsingleton_of_two_id_isIso U

/-- For a local source input, the actual Moore candidate is local via its
proved unit isomorphism. -/
theorem sourceMooreCompletion_isHF2Local_of_local
    (X : SourceCategory.{0}) (hX : SourceIsHF2Local X) :
    SourceIsHF2Local (sourceMooreCompletion 2 X) := by
  letI := sourceMooreCompletionUnit_isIso_of_local X hX
  intro A B f hf
  exact SourceIsHF2Local.of_iso (asIso (sourceMooreCompletionUnit 2 X)).symm hX f hf

end KIP126.StableHomotopy.Implementation
