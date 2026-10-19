module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Coproduct.Proofs
public import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits
universe u

/-- Degreewise stable vanishing is preserved by actual small source coproducts. -/
theorem sourceCoproduct_homotopy_subsingleton {J : Type u}
    (X : J → SourceCategory.{u}) (d : ℤ)
    (hX : ∀ j, Subsingleton ((sourceStableHomotopyAddFunctor d).obj (X j))) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj (∐ X)) := by
  let F := sourceStableHomotopyAddFunctor d
  apply AddCommGrpCat.subsingleton_of_isZero
  apply (isColimitOfHasCoproductOfPreservesColimit F X).isZero_pt
  apply (Functor.isZero_iff _).mpr
  intro j
  letI := hX j.as
  exact AddCommGrpCat.isZero_of_subsingleton (F.obj (X j.as))

end KIP126.StableHomotopy.Implementation
