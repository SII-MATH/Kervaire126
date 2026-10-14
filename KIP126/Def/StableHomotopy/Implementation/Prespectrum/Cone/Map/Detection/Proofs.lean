module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Equivalence

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The Puppe comparison detects the source comparison as well as
preserving it; suspension is the proved original source equivalence. -/
theorem coneMap_twice_stableEquivalence_iff {X Y X' Y' : Prespectrum.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    stableEquivalences (coneMap b (coneMap a b h) (coneInclusion_map a b h)) ↔
      stableEquivalences a := by
  refine ⟨fun hd => ?_, coneMap_twice_stableEquivalence a b h⟩
  letI := stableEquivalences.Q_inverts _ hd
  letI := stableEquivalences.Q_inverts _ (coneIterationComparison_stableEquivalence f)
  letI := stableEquivalences.Q_inverts _ (coneIterationComparison_stableEquivalence g)
  have hL := congrArg (fun k => sourceLocalization.map k)
    (coneIterationComparison_natural a b h)
  simp only [sourceLocalization.map_comp] at hL
  haveI : IsIso (sourceLocalization.map (suspensionMap a)) :=
    IsIso.of_isIso_fac_left hL.symm
  haveI : IsIso (sourceSuspensionFunctor.map (sourceLocalization.map a)) := by
    rw [sourceSuspensionFunctor_map]
    infer_instance
  letI : sourceSuspensionFunctor.{u}.IsEquivalence :=
    inferInstanceAs sourceSuspensionEquivalence.functor.IsEquivalence
  exact (stableEquivalence_iff_source_isIso a).mpr
    (isIso_of_reflects_iso _ sourceSuspensionFunctor)

/-- Actual cone equivalence and target equivalence imply source
equivalence for maps between cofibrant cone sequences. -/
theorem stableEquivalence_source_of_coneMap
    {X Y X' Y' : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y)
    (hX' : IsCubicallyCofibrant X') (hY' : IsCubicallyCofibrant Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (hb : stableEquivalences b)
    (hc : stableEquivalences (coneMap a b h)) : stableEquivalences a := by
  apply (coneMap_twice_stableEquivalence_iff a b h).mp
  exact coneMap_stableEquivalence_of_isCubicallyCofibrant
    hY (hX.cone hY f) hY' (hX'.cone hY' g)
    b (coneMap a b h) (coneInclusion_map a b h) hb hc

/-- Actual source equivalence and cone equivalence imply target
equivalence, using the next actual Puppe stage. -/
theorem stableEquivalence_target_of_coneMap
    {X Y X' Y' : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y)
    (hX' : IsCubicallyCofibrant X') (hY' : IsCubicallyCofibrant Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (ha : stableEquivalences a)
    (hc : stableEquivalences (coneMap a b h)) : stableEquivalences b := by
  let c := coneMap a b h
  let d := coneMap b c (coneInclusion_map a b h)
  apply (coneMap_twice_stableEquivalence_iff b c (coneInclusion_map a b h)).mp
  exact coneMap_stableEquivalence_of_isCubicallyCofibrant
    (hX.cone hY f) (hY.cone (hX.cone hY f) _)
    (hX'.cone hY' g) (hY'.cone (hX'.cone hY' g) _)
    c d (coneInclusion_map b c (coneInclusion_map a b h)) hc
    (coneMap_twice_stableEquivalence a b h ha)

end KIP126.StableHomotopy.Implementation.Prespectrum
