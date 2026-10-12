module

public import KIP126.Def.ClassicalAdams.Convergence.Tower.Predicates
public import KIP126.Def.ClassicalAdams.Convergence.Tower.Completion.Proofs
public import KIP126.Def.ClassicalAdams.Detection.Convergence.Data

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory CategoryTheory.Limits MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Completeness already implies separation of the specified Adams
filtration, so only the associated-graded comparison remains to assemble
strong convergence. -/
theorem IsAdamsTowerStronglyConvergent.of_complete
    (hcomplete : ∀ n : ℤ,
      Nonempty (Core.Algebra.Filtration.CompletionWitness (adamsHomotopyFiltration unit X) n))
    (hgraded : ∀ s t : ℤ,
      Nonempty (((adamsTowerInternalSpectralSequence unit X).ssData (s, t)).eInfty ≅
        (adamsHomotopyFiltration unit X).associatedGraded s (t - s))) :
    IsAdamsTowerStronglyConvergent unit X where
  complete := hcomplete
  separated n S hS := (hcomplete n).elim fun W => W.separated S hS
  associatedGraded := hgraded

/-- The existing detection comparison uses the same actual image filtration
and canonical associated-graded quotient, so it supplies the final strong
convergence comparison once completeness is known. -/
theorem IsAdamsTowerStronglyConvergent.of_complete_and_detection
    (hcomplete : ∀ n : ℤ,
      Nonempty (Core.Algebra.Filtration.CompletionWitness (adamsHomotopyFiltration unit X) n))
    (hdetect : TowerDetection.Convergence unit X) : IsAdamsTowerStronglyConvergent unit X := by
  apply IsAdamsTowerStronglyConvergent.of_complete unit X hcomplete
  intro s t
  exact ⟨hdetect.identification (s, t)⟩

variable [HasProductsOfShape ℕ C]

/-- Nilpotent completeness, finite actual Adams layers, and the existing
E∞ detection comparison imply source-faithful strong convergence. -/
theorem IsAdamsTowerStronglyConvergent.of_nilpotent_complete_of_finite_layers
    (hX : IsENilpotentComplete unit X)
    [∀ (n : ℤ) (k : ℕ), Finite (HomotopyGroup (n + 1) (H ⊗ adamsTower unit X k))]
    (hdetect : TowerDetection.Convergence unit X) : IsAdamsTowerStronglyConvergent unit X := by
  exact IsAdamsTowerStronglyConvergent.of_complete_and_detection unit X
    (fun n => ⟨adamsHomotopyFiltration_complete_of_finite_layers unit X hX n⟩) hdetect

end KIP126.Classical.Adams
