module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Coproduct.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Representation.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual strict coproducts retain the genuine cubical left lifting
property by assembling their component lifts. -/
theorem isCubicallyCofibrant_coproduct {J : Type u} (X : J → Prespectrum.{u})
    (hX : ∀ j, IsCubicallyCofibrant (X j)) : IsCubicallyCofibrant (∐ X) := by
  intro E B p hp
  exact coproduct_initial_hasLiftingProperty X p (fun j => hX j p hp)

/-- The localization of the original strict coproduct is its actual
source coproduct whenever its inputs have the proved cubical lifting
property. The proof uses actual strict representatives and homotopies. -/
noncomputable def sourceStrictSigmaCofan_isColimit {J : Type u}
    (X : J → Prespectrum.{u}) (hX : ∀ j, IsCubicallyCofibrant (X j)) :
    IsColimit (sourceStrictSigmaCofan X) := by
  classical
  have hSigma : IsCubicallyCofibrant (∐ X) := isCubicallyCofibrant_coproduct X hX
  let Z (Y : SourceCategory.{u}) := cubicalReplacementFunctor.obj Y.as.obj
  let e (Y : SourceCategory.{u}) :
      sourceLocalization.obj (loopSpectrificationFunctor.obj (Z Y)) ≅ Y := by
    letI := stableEquivalences.Q_inverts (loopSpectrificationUnit (Z Y))
      (loopSpectrificationUnit_stableEquivalence (Z Y))
    letI := stableEquivalences.Q_inverts (cubicalReplacementComparison.app Y.as.obj)
      (cubicalReplacementComparison_stableEquivalence Y.as.obj)
    exact (asIso (sourceLocalization.map (loopSpectrificationUnit (Z Y)))).symm ≪≫
      asIso (sourceLocalization.map (cubicalReplacementComparison.app Y.as.obj))
  let r (c : Cofan (fun j => sourceLocalization.obj (X j))) (j : J) :
      X j ⟶ loopSpectrificationFunctor.obj (Z c.pt) :=
    (source_map_surjective_of_isCubicallyCofibrant (hX j) (Z c.pt)
      (c.inj j ≫ (e c.pt).inv)).choose
  have hr (c : Cofan (fun j => sourceLocalization.obj (X j))) (j : J) :
      sourceLocalization.map (r c j) = c.inj j ≫ (e c.pt).inv :=
    (source_map_surjective_of_isCubicallyCofibrant (hX j) (Z c.pt)
      (c.inj j ≫ (e c.pt).inv)).choose_spec
  refine Cofan.IsColimit.mk _
    (fun c => sourceLocalization.map (Sigma.desc (r c)) ≫ (e c.pt).hom) ?_ ?_
  · intro c j
    change sourceLocalization.map (Sigma.ι X j) ≫
      (sourceLocalization.map (Sigma.desc (r c)) ≫ (e c.pt).hom) = _
    rw [← Category.assoc,← Functor.map_comp,Sigma.ι_desc,hr]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  · intro c m hm
    obtain ⟨g,hg⟩ := source_map_surjective_of_isCubicallyCofibrant hSigma (Z c.pt)
      (m ≫ (e c.pt).inv)
    change sourceLocalization.map g = m ≫ (e c.pt).inv at hg
    apply (cancel_mono (e c.pt).inv).mp
    rw [Category.assoc,Iso.hom_inv_id,Category.comp_id,← hg]
    apply (source_map_eq_iff_pathHomotopic_of_isCubicallyCofibrant hSigma (Z c.pt) _ _).mpr
    apply (pathHomotopic_coproduct_iff _ _).mpr
    intro j
    apply (source_map_eq_iff_pathHomotopic_of_isCubicallyCofibrant (hX j) (Z c.pt) _ _).mp
    rw [Functor.map_comp,Sigma.ι_desc,hr,hg]
    have hmj : sourceLocalization.map (Sigma.ι X j) ≫ m = c.inj j := hm j
    simpa only [Category.assoc] using congrArg
      (fun k : sourceLocalization.obj (X j) ⟶ c.pt => k ≫ (e c.pt).inv) hmj

end KIP126.StableHomotopy.Implementation.Prespectrum
