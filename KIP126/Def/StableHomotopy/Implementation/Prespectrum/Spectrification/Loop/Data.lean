module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Functor.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Step.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual closed telescope followed by one strict spectrification
step. Every output level is a literal compact-open based loop space. -/
noncomputable def loopSpectrificationFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} :=
  spectrificationTelescopeFunctor ⋙ spectrificationStepFunctor

/-- The actual composite of the telescope and adjoint-bond units. -/
noncomputable def loopSpectrificationUnit (X : Prespectrum.{u}) :
    X ⟶ loopSpectrificationFunctor.obj X :=
  spectrificationTelescopeUnit X ≫ spectrificationStepUnit (spectrificationTelescope X)

/-- The specified strict units are natural for every prespectrum map. -/
noncomputable def loopSpectrificationUnitNat :
    𝟭 Prespectrum.{u} ⟶ loopSpectrificationFunctor where
  app := loopSpectrificationUnit
  naturality X Y f := by
    change f ≫ (spectrificationTelescopeUnit Y ≫ spectrificationStepUnit (spectrificationTelescope Y)) =
      (spectrificationTelescopeUnit X ≫ spectrificationStepUnit (spectrificationTelescope X)) ≫
        spectrificationStepMap (spectrificationTelescopeMap f)
    rw [← Category.assoc,spectrificationTelescopeUnit_natural,Category.assoc,
      spectrificationStepUnit_natural,Category.assoc]

end KIP126.StableHomotopy.Implementation.Prespectrum
