module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Derived
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Representation.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Homotopy

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The specified strict coproduct of actual free-cell replacements,
with the original displayed inclusions, satisfies the genuine coproduct
universal property in the original ordinary stable localization. -/
noncomputable def sourceDerivedSigmaCofan_isColimit {J : Type u}
    (X : J → SourceCategory.{u}) : IsColimit (sourceDerivedSigmaCofan X) := by
  classical
  let A (j : J) : Prespectrum.{u} := (X j).as.obj
  let Z (Y : SourceCategory.{u}) := cubicalReplacementFunctor.obj Y.as.obj
  let e (Y : SourceCategory.{u}) :
      sourceLocalization.obj (loopSpectrificationFunctor.obj (Z Y)) ≅ Y := by
    letI := stableEquivalences.Q_inverts (loopSpectrificationUnit (Z Y))
      (loopSpectrificationUnit_stableEquivalence (Z Y))
    letI := stableEquivalences.Q_inverts (cubicalReplacementComparison.app Y.as.obj)
      (cubicalReplacementComparison_stableEquivalence Y.as.obj)
    exact (asIso (sourceLocalization.map (loopSpectrificationUnit (Z Y)))).symm ≪≫
      asIso (sourceLocalization.map (cubicalReplacementComparison.app Y.as.obj))
  let r (c : Cofan X) (j : J) :
      cubicalReplacementFunctor.obj (A j) ⟶ loopSpectrificationFunctor.obj (Z c.pt) :=
    (source_map_surjective_from_cubicalReplacement_to_loopSpectrification (A j) (Z c.pt)
      (sourceLocalization.map (cubicalReplacementComparison.app (A j)) ≫
        c.inj j ≫ (e c.pt).inv)).choose
  have hr (c : Cofan X) (j : J) : sourceLocalization.map (r c j) =
      sourceLocalization.map (cubicalReplacementComparison.app (A j)) ≫
        c.inj j ≫ (e c.pt).inv :=
    (source_map_surjective_from_cubicalReplacement_to_loopSpectrification (A j) (Z c.pt)
      (sourceLocalization.map (cubicalReplacementComparison.app (A j)) ≫
        c.inj j ≫ (e c.pt).inv)).choose_spec
  refine Cofan.IsColimit.mk _
    (fun c => sourceLocalization.map (Sigma.desc (r c)) ≫ (e c.pt).hom) ?_ ?_
  · intro c j
    letI := stableEquivalences.Q_inverts (cubicalReplacementComparison.app (A j))
      (cubicalReplacementComparison_stableEquivalence (A j))
    apply (cancel_epi (sourceLocalization.map (cubicalReplacementComparison.app (A j)))).mp
    change sourceLocalization.map (cubicalReplacementComparison.app (X j).as.obj) ≫
      ((sourceDerivedSigmaCofan X).inj j ≫
        (sourceLocalization.map (Sigma.desc (r c)) ≫ (e c.pt).hom)) = _
    rw [← Category.assoc, sourceDerivedSigmaCofan_inclusion_comparison,
      ← Category.assoc, ← sourceLocalization.map_comp, Sigma.ι_desc, hr]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro c m hm
    obtain ⟨g, hg⟩ :=
      source_map_surjective_from_coproduct_cubicalReplacement_to_loopSpectrification A (Z c.pt)
        (m ≫ (e c.pt).inv)
    change sourceLocalization.map g = m ≫ (e c.pt).inv at hg
    apply (cancel_mono (e c.pt).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, ← hg]
    apply (source_map_eq_iff_pathHomotopic_from_coproduct_cubicalReplacement_to_loopSpectrification
      A (Z c.pt) _ _).mpr
    apply (pathHomotopic_coproduct_iff _ _).mpr
    intro j
    apply (source_map_eq_iff_pathHomotopic_from_cubicalReplacement_to_loopSpectrification
      (A j) (Z c.pt) _ _).mp
    rw [sourceLocalization.map_comp, Sigma.ι_desc, hr, hg]
    dsimp only [A]
    rw [← sourceDerivedSigmaCofan_inclusion_comparison X j]
    simpa only [Category.assoc] using congrArg
      (fun k : X j ⟶ c.pt =>
        sourceLocalization.map (cubicalReplacementComparison.app (X j).as.obj) ≫
          k ≫ (e c.pt).inv) (hm j)

/-- All small coproducts exist in the original stable localization, using
the actual free-cell and loop constructions in the universal-property proof. -/
instance sourceHasCoproducts : HasCoproducts.{u} SourceCategory.{u} :=
  hasCoproducts_of_colimit_cofans sourceDerivedSigmaCofan sourceDerivedSigmaCofan_isColimit

/-- In every spectrum universe this includes all ordinary small indexing
types, in particular the countable coproduct needed for Milnor telescopes. -/
instance sourceHasSmallCoproductsOfShape (J : Type) :
    HasCoproductsOfShape J SourceCategory.{u} := by
  letI : HasCoproducts.{0} SourceCategory.{u} :=
    has_smallest_coproducts_of_hasCoproducts (C := SourceCategory.{u})
  infer_instance

end KIP126.StableHomotopy.Implementation.Prespectrum
