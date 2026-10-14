module

public import KIP126.Def.StableHomotopy.Implementation.Completion

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- A mod-two cohomology equivalence between actual local spectra is an
isomorphism in the ordinary source category. -/
theorem Prespectrum.IsHF2Local.isIso_of_hf2Equivalence
    {X Y : Prespectrum.{0}} (hX : X.IsHF2Local) (hY : Y.IsHF2Local)
    (f : sourceLocalization.obj X ⟶ sourceLocalization.obj Y)
    (hf : HF2Equivalences f) : IsIso f := by
  obtain ⟨r, hr⟩ := (hX f hf).surjective (𝟙 _)
  have hrf : r ≫ f = 𝟙 _ := by
    apply (hY f hf).injective
    simp only [← Category.assoc, hr, Category.id_comp, Category.comp_id]
  exact ⟨⟨r, hr, hrf⟩⟩

/-- The reflection unit is a mod-two cohomology equivalence, as follows
from testing its universal property against every shift of HF₂. -/
theorem CompletionModel.unit_hf2Equivalence (M : CompletionModel)
    (X : Prespectrum.{0}) : HF2Equivalences (sourceLocalization.map (M.unit.app X)) := by
  intro d
  let Y : CompletedSpectrum :=
    { spectrum := if 0 ≤ d then (Prespectrum.suspension^[d.toNat]) sourceHF2.spectrum
        else (Prespectrum.desuspension^[(-d).toNat]) sourceHF2.spectrum
      isLocal := fun f hf => hf d }
  exact M.universal X Y

/-- A local spectrum's actual reflection unit is invertible in the ordinary
stable category. This is HF₂ locality, not Adams nilpotent completeness. -/
theorem CompletionModel.unit_isIso_of_local (M : CompletionModel)
    (X : Prespectrum.{0}) (hX : X.IsHF2Local) :
    IsIso (sourceLocalization.map (M.unit.app X)) := by
  let u := sourceLocalization.map (M.unit.app X)
  obtain ⟨r, hr⟩ := (M.universal X ⟨X, hX⟩).surjective (𝟙 _)
  have hur : u ≫ r = 𝟙 _ := hr
  have hru : r ≫ u = 𝟙 _ := by
    apply (M.universal X ⟨M.replacement.obj X, M.isLocal X⟩).injective
    change u ≫ (r ≫ u) = u ≫ 𝟙 _
    rw [← Category.assoc, hur, Category.id_comp, Category.comp_id]
  exact ⟨⟨r, hur, hru⟩⟩

end KIP126.StableHomotopy.Implementation
