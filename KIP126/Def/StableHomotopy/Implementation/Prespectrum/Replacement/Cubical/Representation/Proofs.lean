module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Loop.Mapping.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Localization.Roofs.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Fractions.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

private theorem replacement_comp_stable {A B C : Prespectrum.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (hf : stableEquivalences f) (hg : stableEquivalences g) :
    stableEquivalences (f ≫ g) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts f hf
  letI := stableEquivalences.Q_inverts g hg
  rw [Functor.map_comp]
  infer_instance

/-- Every morphism in the actual ordinary stable localization from the
constructed free-cell replacement to the constructed stabilized loop target
has an actual strict representative. -/
theorem source_map_surjective_from_cubicalReplacement_to_loopSpectrification
    (X Z : Prespectrum.{u}) [∀ n,T1Space (Z.level n)] :
    Function.Surjective (fun f : cubicalReplacementFunctor.obj X ⟶ loopSpectrificationFunctor.obj Z =>
      sourceLocalization.map f) := by
  intro a
  let Y := loopSpectrificationFunctor.obj Z
  let QX := cubicalReplacementFunctor.obj X
  let R := loopSpectrificationFunctor
  let L := sourceLocalization
  obtain ⟨A,w,t,hw,ht⟩ := source_morphism_exists_roof a
  let C := cubicalReplacementFunctor.obj A
  let w' : C ⟶ QX := cubicalReplacementComparison.app A ≫ w
  let t' : C ⟶ Y := cubicalReplacementComparison.app A ≫ t
  have hw' : stableEquivalences w' := replacement_comp_stable _ _
    (cubicalReplacementComparison_stableEquivalence A) hw
  have ht' : L.map w' ≫ a = L.map t' := by
    dsimp only [w',t',L]
    rw [Functor.map_comp,Functor.map_comp,Category.assoc,ht]
  obtain ⟨l,hl⟩ := cubicalReplacement_exists_pathHomotopic_lift X (R.map w')
    (fun n p r => loopSpectrificationFunctor_map_homotopy_bijective w' hw' n r p)
    (loopSpectrificationUnit QX)
  obtain ⟨b,hb⟩ := cubicalReplacement_exists_pathHomotopic_lift X (loopSpectrificationUnit Y)
    (fun n p r => loopSpectrificationUnit_output_homotopy_bijective Z n r p)
    (l ≫ R.map t')
  refine ⟨b,?_⟩
  letI : IsIso (L.map (loopSpectrificationUnit QX)) :=
    stableEquivalences.Q_inverts _ (loopSpectrificationUnit_stableEquivalence QX)
  letI : IsIso (L.map (loopSpectrificationUnit C)) :=
    stableEquivalences.Q_inverts _ (loopSpectrificationUnit_stableEquivalence C)
  letI : IsIso (L.map (loopSpectrificationUnit Y)) :=
    stableEquivalences.Q_inverts _ (loopSpectrificationUnit_stableEquivalence Y)
  have hnw : L.map w' ≫ L.map (loopSpectrificationUnit QX) =
      L.map (loopSpectrificationUnit C) ≫ L.map (R.map w') := by
    rw [← Functor.map_comp,← Functor.map_comp]
    exact congrArg L.map (loopSpectrificationUnitNat.naturality w')
  have hnt : L.map t' ≫ L.map (loopSpectrificationUnit Y) =
      L.map (loopSpectrificationUnit C) ≫ L.map (R.map t') := by
    rw [← Functor.map_comp,← Functor.map_comp]
    exact congrArg L.map (loopSpectrificationUnitNat.naturality t')
  let v := inv (L.map (loopSpectrificationUnit QX)) ≫ a ≫ L.map (loopSpectrificationUnit Y)
  have hrv : L.map (R.map w') ≫ v = L.map (R.map t') := by
    apply (cancel_epi (L.map (loopSpectrificationUnit C))).mp
    rw [← Category.assoc,← hnw]
    dsimp only [v]
    rw [Category.assoc,IsIso.hom_inv_id_assoc,← Category.assoc,ht',hnt]
  have hls : L.map l ≫ L.map (R.map w') = L.map (loopSpectrificationUnit QX) := by
    rw [← Functor.map_comp]
    exact source_map_eq_of_pathHomotopic hl
  have hbs : L.map b ≫ L.map (loopSpectrificationUnit Y) = L.map l ≫ L.map (R.map t') := by
    rw [← Functor.map_comp,← Functor.map_comp]
    exact source_map_eq_of_pathHomotopic hb
  change L.map b = a
  apply (cancel_mono (L.map (loopSpectrificationUnit Y))).mp
  calc
    _ = L.map l ≫ L.map (R.map t') := hbs
    _ = L.map l ≫ L.map (R.map w') ≫ v := congrArg (fun k => L.map l ≫ k) hrv.symm
    _ = L.map (loopSpectrificationUnit QX) ≫ v := by rw [← Category.assoc,hls]
    _ = _ := by dsimp only [v]; rw [IsIso.hom_inv_id_assoc]

/-- Equality of strict representatives from the actual free-cell source
to the actual stabilized loop target is exactly genuine strict homotopy. -/
theorem source_map_eq_iff_pathHomotopic_from_cubicalReplacement_to_loopSpectrification
    (X Z : Prespectrum.{u}) [∀ n,T1Space (Z.level n)]
    (a b : cubicalReplacementFunctor.obj X ⟶ loopSpectrificationFunctor.obj Z) :
    sourceLocalization.map a = sourceLocalization.map b ↔ pathHomotopic a b := by
  constructor
  · intro hab
    let Y := loopSpectrificationFunctor.obj Z
    let QX := cubicalReplacementFunctor.obj X
    let R := loopSpectrificationFunctor
    obtain ⟨A,w,hw,H⟩ := (source_map_eq_iff_exists_homotopy_precomp a b).mp hab
    let C := cubicalReplacementFunctor.obj A
    let w' : C ⟶ QX := cubicalReplacementComparison.app A ≫ w
    have hw' : stableEquivalences w' := replacement_comp_stable _ _
      (cubicalReplacementComparison_stableEquivalence A) hw
    have H' : pathHomotopic (w' ≫ a) (w' ≫ b) := by
      simpa only [w',Category.assoc] using
        pathHomotopic_precomp (cubicalReplacementComparison.app A) H
    obtain ⟨l,hl⟩ := cubicalReplacement_exists_pathHomotopic_lift X (R.map w')
      (fun n p r => loopSpectrificationFunctor_map_homotopy_bijective w' hw' n r p)
      (loopSpectrificationUnit QX)
    have hmid := loopSpectrification_pathHomotopic_precomp X H' l
    have hmid' : pathHomotopic ((l ≫ R.map w') ≫ R.map a) ((l ≫ R.map w') ≫ R.map b) := by
      simpa only [Functor.map_comp,Category.assoc] using hmid
    have ha := pathHomotopic_postcomp hl (R.map a)
    have hb := pathHomotopic_postcomp hl (R.map b)
    have hfinal := pathHomotopic_trans (pathHomotopic_symm ha) (pathHomotopic_trans hmid' hb)
    apply cubicalReplacement_pathHomotopic_of_level_homotopy_bijective X (loopSpectrificationUnit Y)
      (fun n p r => loopSpectrificationUnit_output_homotopy_bijective Z n r p)
    rw [show a ≫ loopSpectrificationUnit Y = loopSpectrificationUnit QX ≫ R.map a from
      loopSpectrificationUnitNat.naturality a,
      show b ≫ loopSpectrificationUnit Y = loopSpectrificationUnit QX ≫ R.map b from
        loopSpectrificationUnitNat.naturality b]
    exact hfinal
  · exact source_map_eq_of_pathHomotopic

end KIP126.StableHomotopy.Implementation.Prespectrum
