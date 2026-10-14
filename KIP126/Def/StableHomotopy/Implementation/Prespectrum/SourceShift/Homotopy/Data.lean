module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Equivalence
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
universe u

/-- The actual padded desuspension shifts the original stable quotient by one. -/
noncomputable def stableHomotopyDesuspensionEquiv (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy X.desuspension d ≃ StableHomotopy X (d+1) :=
  Classical.choice (stableHomotopy_desuspension_equiv X d)

/-- Removing the first level shifts the original stable quotient down by one. -/
noncomputable def stableHomotopyTailEquiv (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy (levelTail X) d ≃ StableHomotopy X (d-1) :=
  (Equiv.cast (congrArg (StableHomotopy (levelTail X)) (show d = d-1+1 by omega))).trans
    ((stableHomotopyDesuspensionEquiv (levelTail X) (d-1)).symm.trans
      (Equiv.ofBijective (stableHomotopyMap (paddedTailInclusion X) (d-1))
        (paddedTailInclusion_stableEquivalence X (d-1))))

/-- Actual point-set suspension shifts the original stable quotient down by one,
using the proved comparison to the actual level tail. -/
noncomputable def stableHomotopySuspensionEquiv (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy X.suspension d ≃ StableHomotopy X (d-1) :=
  (stableHomotopyEquivOfSourceIso (sourceSuspensionComparisonIso X) d).trans
    (stableHomotopyTailEquiv X d)

/-- Every finite iteration of actual suspension has the corresponding degree shift. -/
noncomputable def stableHomotopyIterateSuspensionEquiv (X : Prespectrum.{u}) (n : ℕ) (d : ℤ) :
    StableHomotopy ((suspension^[n]) X) d ≃ StableHomotopy X (d-n) := by
  induction n generalizing d with
  | zero => simpa using (Equiv.refl (StableHomotopy X d))
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (stableHomotopySuspensionEquiv ((suspension^[n]) X) d).trans
      ((ih (d-1)).trans (Equiv.cast (congrArg (StableHomotopy X) (by push_cast; omega))))

/-- Every finite iteration of actual padded desuspension has the corresponding degree shift. -/
noncomputable def stableHomotopyIterateDesuspensionEquiv (X : Prespectrum.{u}) (n : ℕ) (d : ℤ) :
    StableHomotopy ((desuspension^[n]) X) d ≃ StableHomotopy X (d+n) := by
  induction n generalizing d with
  | zero => simpa using (Equiv.refl (StableHomotopy X d))
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (stableHomotopyDesuspensionEquiv ((desuspension^[n]) X) d).trans
      ((ih (d+1)).trans (Equiv.cast (congrArg (StableHomotopy X) (by push_cast; omega))))

end KIP126.StableHomotopy.Implementation.Prespectrum
