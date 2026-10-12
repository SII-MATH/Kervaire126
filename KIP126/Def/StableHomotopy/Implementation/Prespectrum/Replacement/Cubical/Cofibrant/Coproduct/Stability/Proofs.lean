module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Coproduct

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- Original strict coproducts of maps between actually cofibrant
spectra preserve stable equivalences, by their proved source coproduct
universal property. -/
theorem coproductMap_stableEquivalence_of_isCubicallyCofibrant
    {J : Type u} {X Y : J → Prespectrum.{u}}
    (hX : ∀ j, IsCubicallyCofibrant (X j)) (hY : ∀ j, IsCubicallyCofibrant (Y j))
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, stableEquivalences (f j)) :
    stableEquivalences (CategoryTheory.Limits.Sigma.map f) := by
  classical
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI (j : J) := stableEquivalences.Q_inverts (f j) (hf j)
  let c : Cofan (fun j => sourceLocalization.obj (Y j)) :=
    Cofan.mk (sourceLocalization.obj (∐ X))
      (fun j => inv (sourceLocalization.map (f j)) ≫ sourceLocalization.map (Sigma.ι X j))
  let s := (sourceStrictSigmaCofan_isColimit Y hY).desc c
  have hs (j : J) : sourceLocalization.map (Sigma.ι Y j) ≫ s =
      inv (sourceLocalization.map (f j)) ≫ sourceLocalization.map (Sigma.ι X j) :=
    (sourceStrictSigmaCofan_isColimit Y hY).fac c ⟨j⟩
  refine ⟨s,?_,?_⟩
  · apply (sourceStrictSigmaCofan_isColimit X hX).hom_ext
    rintro ⟨j⟩
    change sourceLocalization.map (Sigma.ι X j) ≫ (sourceLocalization.map (CategoryTheory.Limits.Sigma.map f) ≫ s) =
      sourceLocalization.map (Sigma.ι X j) ≫ 𝟙 _
    rw [← Category.assoc,← Functor.map_comp,Sigma.ι_map,Functor.map_comp,Category.assoc,hs]
    simp only [← Category.assoc,IsIso.hom_inv_id,Category.id_comp,Category.comp_id]
  · apply (sourceStrictSigmaCofan_isColimit Y hY).hom_ext
    rintro ⟨j⟩
    change sourceLocalization.map (Sigma.ι Y j) ≫ (s ≫ sourceLocalization.map (CategoryTheory.Limits.Sigma.map f)) =
      sourceLocalization.map (Sigma.ι Y j) ≫ 𝟙 _
    rw [← Category.assoc,hs,Category.assoc,← Functor.map_comp,Sigma.ι_map,Functor.map_comp]
    simp only [← Category.assoc,IsIso.inv_hom_id,Category.id_comp,Category.comp_id]

end KIP126.StableHomotopy.Implementation.Prespectrum
