import KIP126.Def.StableHomotopy.Cohomology.Proofs

/-! Regression checks for the explicit mod-2 cohomology interface. -/
namespace KIP126.Checks.StableHomotopy

open CategoryTheory
open KIP126.StableHomotopy
open KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

example (H : Mod2EilenbergMacLane (C := C)) (n : ℤ) (X : C) :
    Mod2Cohomology H n X = ((shiftFunctor C (-n)).obj X ⟶ H.HF2) := rfl

example (H : Mod2EilenbergMacLane (C := C)) {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    Mod2Cohomology.pullback H f n = Mod2Cohomology.pullback H f n := rfl

example (H : Mod2EilenbergMacLane (C := C)) {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    (Mod2Homology.pushforward H f n) 0 = 0 := by
  simp [Mod2Homology.pushforward]

example (H : Mod2EilenbergMacLane (C := C)) (n : ℤ) (X : C) :
    Nonempty
      (Mod2Cohomology H n X ≃
        (X ⟶ (shiftFunctor C n).obj H.HF2)) :=
  ⟨cohomologyRepresentable H n X⟩

/-- The universal-coefficient index is the ordinary cohomology index, not
the positive shift of its source. -/
example (H : Mod2EilenbergMacLane (C := C)) (U : UniversalCoefficientData H)
    (n : ℤ) (X : C) :
    Mod2Cohomology H n X ≃+ (Mod2Homology H n X →+ ZMod 2) :=
  U.cohomologyHomologyEquiv n X

/-- Positive Steenrod degree raises the target cohomological degree. -/
example (H : Mod2EilenbergMacLane (C := C))
    [ClosedSymmetricTensorTriangulated (C := C)] (A : SteenrodAlgebraData H) :
    Nonempty (A.gradedComponent 1 ≃ (H.HF2 ⟶ (shiftFunctor C (1 : ℤ)).obj H.HF2)) :=
  ⟨A.operationsRepresentable H 1⟩

end KIP126.Checks.StableHomotopy
