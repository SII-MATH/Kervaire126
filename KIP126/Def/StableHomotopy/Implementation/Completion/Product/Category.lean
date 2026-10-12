module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Product.Proofs

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {J : Type} [Finite J]

/-- The displayed finite product cone is limiting in the category of
actual HF₂-local spectra. -/
noncomputable def piFan_isLimit (X : J → CompletedSpectrum) : IsLimit (piFan X) := by
  let h := (Fan.isLimitMapConeEquiv sourceLocalization (fun j => (X j).spectrum)
    (Prespectrum.piFan (fun j => (X j).spectrum)))
    (Prespectrum.sourcePiFan_isLimit (fun j => (X j).spectrum))
  refine Fan.IsLimit.mk _ (fun s => Fan.IsLimit.lift h (fun j => s.proj j)) ?_ ?_
  · intro s j
    exact Fan.IsLimit.fac h (fun j => s.proj j) j
  · intro s m hm
    apply Fan.IsLimit.hom_ext h m _
    intro j
    exact (hm j).trans (Fan.IsLimit.fac h (fun j => s.proj j) j).symm

instance hasProductsOfShape (J : Type) [Finite J] : HasProductsOfShape J CompletedSpectrum := by
  refine ⟨fun F => ?_⟩
  letI : HasLimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
    ⟨⟨piFan (F.obj ∘ Discrete.mk), piFan_isLimit _⟩⟩
  exact hasLimit_of_iso Discrete.natIsoFunctor.symm

instance hasFiniteProducts : HasFiniteProducts CompletedSpectrum := ⟨fun _ => inferInstance⟩

end KIP126.StableHomotopy.Implementation.CompletedSpectrum

end
