module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Step.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual step unit is natural for strict maps. -/
theorem spectrificationStepUnit_natural {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    f ≫ spectrificationStepUnit Y = spectrificationStepUnit X ≫ spectrificationStepMap f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext t
  exact (f.bond n x t).symm

/-- Applying the step to the unit is exactly the unit of the step. -/
theorem spectrificationStepUnit_coherence (X : Prespectrum.{u}) :
    spectrificationStepMap (spectrificationStepUnit X) =
      spectrificationStepUnit (spectrificationStep X) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Path.ext
  funext t
  apply Path.ext
  rfl

theorem Representative.fromSpectrificationStep_next {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative (spectrificationStep X) d) :
    a.next.fromSpectrificationStep = a.fromSpectrificationStep.next := by
  rfl

theorem Representative.fromSpectrificationStep_unit {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) :
    (a.map (spectrificationStepUnit X)).fromSpectrificationStep = a.next := by
  rfl

theorem Representative.unit_fromSpectrificationStep {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative (spectrificationStep X) d) :
    a.fromSpectrificationStep.map (spectrificationStepUnit X) = a.next := by
  rfl

theorem Representative.fromSpectrificationStep_relation {X : Prespectrum.{u}} {d : ℤ}
    {a b : Representative (spectrificationStep X) d}
    (h : StableRelation (spectrificationStep X) d a b) :
    StableRelation X d a.fromSpectrificationStep b.fromSpectrificationStep := by
  cases h with
  | homotopy p h =>
      exact StableRelation.homotopy _ _
        ⟨loopUncurryFirstHomotopy _ _ h.some⟩
  | stabilization =>
      rw [Representative.fromSpectrificationStep_next]
      exact StableRelation.stabilization _

/-- The concrete adjoint-bond unit is a stable equivalence for every actual
prespectrum. Its inverse on stable classes uncurries the first loop coordinate;
both composites are exactly the original stabilization relation. -/
theorem spectrificationStepUnit_stableEquivalence (X : Prespectrum.{u}) :
    stableEquivalences (spectrificationStepUnit X) := by
  intro d
  let g : StableHomotopy (spectrificationStep X) d → StableHomotopy X d :=
    Quot.map Representative.fromSpectrificationStep
      (fun _ _ h => Representative.fromSpectrificationStep_relation h)
  have hleft : Function.LeftInverse g (stableHomotopyMap (spectrificationStepUnit X) d) := by
    intro x
    induction x using Quot.inductionOn with
    | h a =>
        change Quot.mk _ ((a.map (spectrificationStepUnit X)).fromSpectrificationStep) = Quot.mk _ a
        rw [Representative.fromSpectrificationStep_unit]
        exact (Quot.sound (StableRelation.stabilization a)).symm
  have hright : Function.RightInverse g (stableHomotopyMap (spectrificationStepUnit X) d) := by
    intro x
    induction x using Quot.inductionOn with
    | h a =>
        change Quot.mk _ (a.fromSpectrificationStep.map (spectrificationStepUnit X)) = Quot.mk _ a
        rw [Representative.unit_fromSpectrificationStep]
        exact (Quot.sound (StableRelation.stabilization a)).symm
  exact ⟨hleft.injective, hright.surjective⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
