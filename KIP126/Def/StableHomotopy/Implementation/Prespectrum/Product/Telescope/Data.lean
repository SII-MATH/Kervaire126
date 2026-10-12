module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Functor.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Functor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- Form the actual product after applying the actual spectrification telescope
to every factor. -/
noncomputable def piTelescopeFunctor (J : Type) : (J → Prespectrum.{u}) ⥤ Prespectrum.{u} :=
  Functor.pi (fun _ : J => spectrificationTelescopeFunctor) ⋙ piPrespectrumFunctor J

end KIP126.StableHomotopy.Implementation.Prespectrum
