module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Product.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Finite J]

/-- The actual pointwise product of a finite family of local spectra,
equipped with its proved locality. -/
def pi (X : J → CompletedSpectrum) : CompletedSpectrum where
  spectrum := Prespectrum.piPrespectrum (fun j => (X j).spectrum)
  isLocal := Prespectrum.isHF2Local_pi _ (fun j => (X j).isLocal)

noncomputable def piProjection (X : J → CompletedSpectrum) (j : J) : pi X ⟶ X j :=
  sourceLocalization.map (Prespectrum.piProjection (fun j => (X j).spectrum) j)

/-- The cone of the specified finite product of actual local spectra. -/
noncomputable def piFan (X : J → CompletedSpectrum) : Fan X :=
  Fan.mk (pi X) (piProjection X)

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
