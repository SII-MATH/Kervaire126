module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Coherence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- The coherent source shift uses exactly the previously specified integer functor. -/
@[simp] theorem source_shiftFunctor_eq (d : ℤ) :
    shiftFunctor SourceCategory.{u} d = sourceIntegerShiftFunctor d := rfl

@[simp] theorem source_shiftFunctor_one :
    shiftFunctor SourceCategory.{u} (1 : ℤ) = sourceSuspensionFunctor := rfl

@[simp] theorem source_shiftFunctor_neg_one :
    shiftFunctor SourceCategory.{u} (-1 : ℤ) = sourceDesuspensionFunctor := rfl

/-- Every coherent source shift has the exact prescribed point-set object. -/
theorem source_shiftFunctor_obj (d : ℤ) (X : Prespectrum.{u}) :
    (shiftFunctor SourceCategory d).obj (sourceLocalization.obj X) =
      sourceLocalization.obj (if 0 ≤ d then suspension^[d.toNat] X
        else desuspension^[(-d).toNat] X) :=
  sourceIntegerShiftFunctor_obj d X

end KIP126.StableHomotopy.Implementation.Prespectrum
