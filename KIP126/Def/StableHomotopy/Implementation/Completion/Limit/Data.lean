module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Limit.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Category.Proofs
public import Mathlib.CategoryTheory.Limits.Creates

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory CategoryTheory.Limits

universe v u

/-- An actual source limit cone on local objects lifts to the same cone
in the category of completed spectra. -/
noncomputable def liftSourceLimit {J : Type u} [Category.{v} J]
    (F : J ⥤ CompletedSpectrum) (c : Cone (F ⋙ toSource)) (hc : IsLimit c) :
    LiftableCone F toSource c := by
  have h : SourceIsHF2Local c.pt :=
    SourceIsHF2Local.of_isLimit c hc (fun j => (F.obj j).isLocal)
  rcases c with ⟨⟨⟨P⟩⟩, π⟩
  exact
    { liftedCone := { pt := ⟨P, h⟩, π := { app := π.app, naturality := π.naturality } }
      validLift := Iso.refl _ }

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
