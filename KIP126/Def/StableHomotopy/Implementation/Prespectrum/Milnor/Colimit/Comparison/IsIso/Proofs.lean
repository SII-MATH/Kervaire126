module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Comparison.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialHomotopyColimit.Source.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Conservativity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The existing stage-preserving comparison identifies the actual Milnor
cofiber with the actual closed-cylinder telescope in the source localization.
Both compute the original stable homotopy colimit, and those groups detect
isomorphisms of arbitrary source morphisms. -/
instance sourceHomotopyColimitToTelescope_isIso (F : ℕ ⥤ Prespectrum.{u}) :
    IsIso (sourceHomotopyColimitToTelescope F) := by
  apply (source_isIso_iff_stableHomotopy_bijective _).mpr
  intro d
  let G := sourceStableHomotopyFunctor d
  let h₁ := sourceHomotopyColimit_homotopy_isColimit (F ⋙ sourceLocalization) d
  let h₂ := Prespectrum.sourceSequentialHomotopyColimitCocone_homotopy_isColimit F d
  let e := h₁.coconePointUniqueUpToIso h₂
  have he : G.map (sourceHomotopyColimitToTelescope F) = e.hom := by
    apply h₁.hom_ext
    intro n
    change G.map (sourceHomotopyColimitInclusion (F ⋙ sourceLocalization) n) ≫
      G.map (sourceHomotopyColimitToTelescope F) = _
    rw [← G.map_comp, sourceHomotopyColimitToTelescope_inclusion]
    exact (h₁.comp_coconePointUniqueUpToIso_hom h₂ n).symm
  change Function.Bijective (G.map (sourceHomotopyColimitToTelescope F))
  rw [he]
  exact (CategoryTheory.isIso_iff_bijective e.hom).mp inferInstance

end KIP126.StableHomotopy.Implementation
