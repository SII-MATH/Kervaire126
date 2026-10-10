import KIP126.Def.ClassicalAdams.Completion.Predicates
import KIP126.Def.ClassicalAdams.Convergence.Tower.Predicates

/-! Applicability of the untruncated BHS theorem, on the actual classical
Adams tower. This is a source/application obligation, not part of the
structural definition of a route model and not a consequence of an arbitrary
associated-graded identification.

BHS, SynRevBigraded.tex, Theorem A.1 and definitions preceding it;
SynRevAdams.tex, cor:tau-surj and proof of A.1(2)--(4).
The finite Cτ^q assertions have a more general proof (lemm:comp1), and are
intentionally not made conditional on this record. -/
namespace KIP126.Classical.Adams
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C}

/-- The choice of products is explicit so this proposition cannot silently
use a new model or new inverse-limit construction. -/
structure BHSObjectApplicability (products : HasProductsOfShape ℕ C)
    (unit : 𝟙_ C ⟶ H) (X : C) : Prop where
  nilpotent_complete : letI := products; IsENilpotentComplete unit X
  strongly_convergent : IsAdamsTowerStronglyConvergent unit X

end KIP126.Classical.Adams
