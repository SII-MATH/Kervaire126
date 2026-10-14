module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Step.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Data
public import Mathlib.CategoryTheory.Functor.OfSequence

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- Factor the actual adjoint-bond unit by its actual reduced mapping cylinder. -/
noncomputable def spectrificationCylinderStep (X : Prespectrum.{u}) : Prespectrum.{u} :=
  mappingCylinder (spectrificationStepUnit X)

/-- The actual source inclusion into the cylinder of the adjoint-bond unit. -/
noncomputable def spectrificationCylinderUnit (X : Prespectrum.{u}) :
    X ⟶ spectrificationCylinderStep X := mappingCylinderInclusion (spectrificationStepUnit X)

/-- Repeated actual closed-cylinder steps, starting from the given prespectrum. -/
noncomputable def spectrificationStages (X : Prespectrum.{u}) : ℕ → Prespectrum.{u}
  | 0 => X
  | k+1 => spectrificationCylinderStep (spectrificationStages X k)

/-- The actual sequential diagram with the displayed cylinder inclusions. -/
noncomputable def spectrificationDiagram (X : Prespectrum.{u}) : ℕ ⥤ Prespectrum.{u} :=
  Functor.ofSequence (fun k => spectrificationCylinderUnit (spectrificationStages X k))

/-- The actual levelwise topological colimit of the iterated cylinder steps. -/
noncomputable def spectrificationTelescope (X : Prespectrum.{u}) : Prespectrum.{u} :=
  sequentialColimit (spectrificationDiagram X)

/-- The actual map from the original prespectrum into its constructed telescope. -/
noncomputable def spectrificationTelescopeUnit (X : Prespectrum.{u}) :
    X ⟶ spectrificationTelescope X := sequentialColimitInclusion (spectrificationDiagram X) 0

end KIP126.StableHomotopy.Implementation.Prespectrum
