module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Localization.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

/-- The actual finite pointwise product of HF₂-local prespectra is local.
The argument uses the proved product universal property in the ordinary
source localization. -/
theorem Prespectrum.isHF2Local_pi {J : Type} [Finite J]
    (X : J → Prespectrum.{0}) (hX : ∀ j, (X j).IsHF2Local) :
    (Prespectrum.piPrespectrum X).IsHF2Local := by
  let h := (Fan.isLimitMapConeEquiv sourceLocalization X (Prespectrum.piFan X))
    (Prespectrum.sourcePiFan_isLimit X)
  intro A B f hf
  constructor
  · intro a b hab
    apply Fan.IsLimit.hom_ext h a b
    intro j
    apply (hX j f hf).injective
    simpa only [Category.assoc, fan_mk_proj, Prespectrum.piFan] using congrArg
      (fun k => k ≫ sourceLocalization.map (Prespectrum.piProjection X j)) hab
  · intro a
    choose g hg using fun j => (hX j f hf).surjective
      (a ≫ sourceLocalization.map (Prespectrum.piProjection X j))
    refine ⟨Fan.IsLimit.lift h g, Fan.IsLimit.hom_ext h _ _ (fun j => ?_)⟩
    rw [Category.assoc, Fan.IsLimit.fac]
    simpa only [fan_mk_proj, Prespectrum.piFan] using hg j

/-- Finite pointwise products of the specified integer coefficient shifts
are actual local source spectra. -/
theorem sourceHF2Shift_pi_isLocal {J : Type} [Finite J] (d : J → ℤ) :
    (Prespectrum.piPrespectrum (fun j =>
      if 0 ≤ d j then (Prespectrum.suspension^[(d j).toNat]) sourceHF2.spectrum
      else (Prespectrum.desuspension^[(-(d j)).toNat]) sourceHF2.spectrum)).IsHF2Local :=
  Prespectrum.isHF2Local_pi _ (fun j => sourceHF2Shift_isLocal (d j))

end KIP126.StableHomotopy.Implementation
