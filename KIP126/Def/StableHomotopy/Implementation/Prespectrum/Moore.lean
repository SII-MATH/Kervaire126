module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Cofiber.Data
public import KIP126.Def.StableHomotopy.Completion.Moore.Proofs
public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Represented.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The actual Moore completion candidate in the original source category,
formed from the existing scalar-power tower using its constructed cofibers
and constructed Milnor homotopy limit. -/
noncomputable def sourceMooreCompletion (p : ℕ) (X : SourceCategory.{u}) : SourceCategory.{u} :=
  sourceHomotopyLimit (moorePowerSequence p X)

/-- The actual compatible cofiber inclusions lift through the constructed
Milnor triangle to a chosen Moore unit. -/
noncomputable def sourceMooreCompletionUnit (p : ℕ) (X : SourceCategory.{u}) :
    X ⟶ sourceMooreCompletion p X :=
  ((sourceHomotopyLimitWitness (moorePowerSequence p X)).exists_lift
    (fun k => HasFunctorialCofiber.cofibι (moorePowerMap p X k))
    (moorePowerSequence_inclusion_step p X)).choose

end KIP126.StableHomotopy.Implementation

end

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The constructed unit retains the specified inclusions at every
actual scalar-power cofiber stage. -/
theorem sourceMooreCompletionUnit_projection (p : ℕ) (X : SourceCategory.{u}) (k : ℕ) :
    sourceMooreCompletionUnit p X ≫ (sourceHomotopyLimitWitness (moorePowerSequence p X)).π k =
      HasFunctorialCofiber.cofibι (moorePowerMap p X k) :=
  ((sourceHomotopyLimitWitness (moorePowerSequence p X)).exists_lift
    (fun k => HasFunctorialCofiber.cofibι (moorePowerMap p X k))
    (moorePowerSequence_inclusion_step p X)).choose_spec k

/-- The actual tower reductions act on the boundary by the original
scalar, as specified by their completed morphisms of triangles. -/
theorem sourceMoorePowerSequence_boundary_step (p : ℕ) (X : SourceCategory.{u}) (k : ℕ) :
    (moorePowerSequence p X).step k ≫ HasFunctorialCofiber.cofibδ (moorePowerMap p X k) =
      p • HasFunctorialCofiber.cofibδ (moorePowerMap p X (k+1)) := by
  have h := HasFunctorialCofiber.cofibMap_δ (moorePowerMap p X (k+1))
    (moorePowerMap p X k) (p • 𝟙 X) (𝟙 X) (by
      simp only [moorePowerMap, Preadditive.nsmul_comp, Category.id_comp,
        Category.comp_id, smul_smul, pow_succ'])
  simpa only [moorePowerSequence, Functor.map_nsmul, CategoryTheory.Functor.map_id,
    Preadditive.comp_nsmul, Category.comp_id] using h

end KIP126.StableHomotopy.Implementation

end
