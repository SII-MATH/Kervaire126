module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Instances
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits

/-- Tensoring with an empty parameter with a disjoint basepoint gives
an actual zero spectrum before localization. -/
theorem spaceSmash_adjoinPoint_isZero (S : TopCat.{0}) [IsEmpty S] (X : Prespectrum.{0}) :
    IsZero (spaceSmash (BasedSpace.adjoinPoint S) X) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,x⟩
  cases a with
  | inl s => exact isEmptyElim s
  | inr p =>
    cases p
    change BasedSpace.smashPoint (BasedSpace.adjoinPoint S) (X.level n)
      (BasedSpace.adjoinPoint S).point x = _
    exact BasedSpace.smashPoint_base_left _ _ _

end KIP126.StableHomotopy.Implementation.Prespectrum
