module

public import KIP126.Def.CategoryTheory.Functor.Iterate.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Equivalence

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Foundation

universe u

/-- The exact signed iterate family of the actual source suspension and
desuspension. The integer addition coherence is not part of this definition. -/
noncomputable def sourceIntegerShiftFunctor : ℤ → SourceCategory.{u} ⥤ SourceCategory.{u}
  | Int.ofNat n => functorIterate sourceSuspensionFunctor n
  | Int.negSucc n => functorIterate sourceDesuspensionFunctor (n + 1)

/-- Applying one actual suspension increments the signed iterate family. -/
noncomputable def sourceIntegerSuccessorIso (d : ℤ) :
    sourceIntegerShiftFunctor.{u} (d + 1) ≅ sourceIntegerShiftFunctor d ⋙ sourceSuspensionFunctor := by
  cases d with
  | ofNat n => exact Iso.refl _
  | negSucc n =>
    cases n with
    | zero => exact sourceSuspensionEquivalence.counitIso.symm
    | succ n =>
      have hn : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [hn]
      exact Functor.isoWhiskerLeft (functorIterate sourceDesuspensionFunctor (n + 1))
        sourceSuspensionEquivalence.counitIso.symm

/-- The inverse step uses the actual equivalence unit and the specified
successor comparison, fixing their cancellation compatibility. -/
noncomputable def sourceIntegerUndoSuccessorIso (d : ℤ) :
    sourceIntegerShiftFunctor.{u} d ≅ sourceIntegerShiftFunctor (d + 1) ⋙ sourceDesuspensionFunctor :=
  Functor.isoWhiskerLeft (sourceIntegerShiftFunctor d) sourceSuspensionEquivalence.unitIso ≪≫
    Functor.isoWhiskerRight (sourceIntegerSuccessorIso d).symm sourceDesuspensionFunctor

/-- Applying one actual desuspension decrements the signed iterate family. -/
noncomputable def sourceIntegerPredecessorIso (d : ℤ) :
    sourceIntegerShiftFunctor.{u} (d - 1) ≅ sourceIntegerShiftFunctor d ⋙ sourceDesuspensionFunctor :=
  sourceIntegerUndoSuccessorIso (d - 1) ≪≫
    eqToIso (congrArg (fun k => sourceIntegerShiftFunctor k ⋙ sourceDesuspensionFunctor) (by omega))

end KIP126.StableHomotopy.Implementation.Prespectrum
