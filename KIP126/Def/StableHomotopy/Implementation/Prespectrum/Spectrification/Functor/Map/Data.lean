module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Functor.Stages.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The actual levelwise colimit sends a strict map to its induced telescope map. -/
noncomputable def spectrificationTelescopeMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    spectrificationTelescope X ⟶ spectrificationTelescope Y :=
  sequentialColimitDesc
    { pt := spectrificationTelescope Y
      ι := spectrificationDiagramMap f ≫ (sequentialColimitCocone (spectrificationDiagram Y)).ι }

end KIP126.StableHomotopy.Implementation.Prespectrum
