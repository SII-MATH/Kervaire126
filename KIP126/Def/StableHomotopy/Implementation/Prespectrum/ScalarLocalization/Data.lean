module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Cocone.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory
universe u

/-- The actual constant-object source sequence whose transitions are scalar
multiplication. Its maps are in the original stable localization. -/
noncomputable def sourceScalarSequence (p : ℕ) (X : SourceCategory.{u}) :
    ℕ ⥤ SourceCategory.{u} :=
  Functor.ofSequence (fun _ : ℕ => p • 𝟙 X)

/-- The actual Milnor cofiber of the scalar sequence. -/
noncomputable def sourceScalarTelescope (p : ℕ) (X : SourceCategory.{u}) : SourceCategory.{u} :=
  sourceHomotopyColimit (sourceScalarSequence p X)

/-- The original zeroth-stage map into the actual scalar telescope. -/
noncomputable def sourceScalarTelescopeUnit (p : ℕ) (X : SourceCategory.{u}) :
    X ⟶ sourceScalarTelescope p X :=
  sourceHomotopyColimitInclusion (sourceScalarSequence p X) 0

end KIP126.StableHomotopy.Implementation
