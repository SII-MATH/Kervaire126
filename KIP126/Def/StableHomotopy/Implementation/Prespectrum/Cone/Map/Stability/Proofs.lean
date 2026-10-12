module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Source.Exact.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Naturality.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Stability.Proofs
public import Mathlib.Algebra.FiveLemma

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The iterated literal cone map is an actual stable equivalence
whenever its original source comparison is, by the actual Puppe comparison. -/
theorem coneMap_twice_stableEquivalence {X Y X' Y' : Prespectrum.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (ha : stableEquivalences a) :
    stableEquivalences (coneMap b (coneMap a b h) (coneInclusion_map a b h)) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ (coneIterationComparison_stableEquivalence f)
  letI := stableEquivalences.Q_inverts _ (coneIterationComparison_stableEquivalence g)
  letI := stableEquivalences.Q_inverts _ (suspensionMap_stableEquivalence a ha)
  have hL := congrArg (fun k => sourceLocalization.map k)
    (coneIterationComparison_natural a b h)
  simp only [sourceLocalization.map_comp] at hL
  haveI : IsIso (sourceLocalization.map (coneMap b (coneMap a b h) (coneInclusion_map a b h)) ≫
      sourceLocalization.map (coneIterationComparison g)) := by
    rw [hL]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (sourceLocalization.map (coneIterationComparison g))

/-- Actual stable equivalences between cubically cofibrant prespectra
induce an actual stable equivalence on their literal mapping cones.
The proof uses the proved contravariant exact sequences and actual
iterated-cone comparison, rather than assuming stable excision. -/
theorem coneMap_stableEquivalence_of_isCubicallyCofibrant
    {X Y X' Y' : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y)
    (hX' : IsCubicallyCofibrant X') (hY' : IsCubicallyCofibrant Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (ha : stableEquivalences a) (hb : stableEquivalences b) :
    stableEquivalences (coneMap a b h) := by
  let c := coneMap a b h
  let d := coneMap b c (coneInclusion_map a b h)
  let e := coneMap c d (coneInclusion_map b c (coneInclusion_map a b h))
  have hc : IsCubicallyCofibrant (cone f) := hX.cone hY f
  have hc' : IsCubicallyCofibrant (cone g) := hX'.cone hY' g
  have hd : IsCubicallyCofibrant (cone (coneInclusion f)) := hY.cone hc _
  have hd' : IsCubicallyCofibrant (cone (coneInclusion g)) := hY'.cone hc' _
  letI := stableEquivalences.Q_inverts a ha
  letI := stableEquivalences.Q_inverts b hb
  letI := stableEquivalences.Q_inverts d (coneMap_twice_stableEquivalence a b h ha)
  letI := stableEquivalences.Q_inverts e
    (coneMap_twice_stableEquivalence b c (coneInclusion_map a b h) hb)
  apply (stableEquivalence_iff_source_isIso _).mpr
  apply isIso_of_coyoneda_map_bijective
  intro A
  have comm {U V U' V' : Prespectrum.{u}} {p : U ⟶ V} {q : U' ⟶ V'}
      (i : U ⟶ U') (j : V ⟶ V') (w : p ≫ j = i ≫ q) :
      (Preadditive.leftComp A (sourceLocalization.map p)).comp
          (Preadditive.leftComp A (sourceLocalization.map j)) =
        (Preadditive.leftComp A (sourceLocalization.map i)).comp
          (Preadditive.leftComp A (sourceLocalization.map q)) := by
    ext z
    change sourceLocalization.map p ≫ (sourceLocalization.map j ≫ z) =
      sourceLocalization.map i ≫ (sourceLocalization.map q ≫ z)
    rw [← Category.assoc, ← sourceLocalization.map_comp, w, sourceLocalization.map_comp,
      Category.assoc]
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (Preadditive.leftComp A (sourceLocalization.map (coneInclusion (coneInclusion (coneInclusion g)))))
    (Preadditive.leftComp A (sourceLocalization.map (coneInclusion (coneInclusion g))))
    (Preadditive.leftComp A (sourceLocalization.map (coneInclusion g)))
    (Preadditive.leftComp A (sourceLocalization.map g))
    (Preadditive.leftComp A (sourceLocalization.map (coneInclusion (coneInclusion (coneInclusion f)))))
    (Preadditive.leftComp A (sourceLocalization.map (coneInclusion (coneInclusion f))))
    (Preadditive.leftComp A (sourceLocalization.map (coneInclusion f)))
    (Preadditive.leftComp A (sourceLocalization.map f))
    (Preadditive.leftComp A (sourceLocalization.map e))
    (Preadditive.leftComp A (sourceLocalization.map d))
    (Preadditive.leftComp A (sourceLocalization.map c))
    (Preadditive.leftComp A (sourceLocalization.map b))
    (Preadditive.leftComp A (sourceLocalization.map a))
    (comm d e (coneInclusion_map c d (coneInclusion_map b c (coneInclusion_map a b h))))
    (comm c d (coneInclusion_map b c (coneInclusion_map a b h)))
    (comm b c (coneInclusion_map a b h)) (comm a b h)
    (source_coneInclusion_hom_exact hc' hd' (coneInclusion (coneInclusion g)) A)
    (source_coneInclusion_hom_exact hY' hc' (coneInclusion g) A)
    (source_coneInclusion_hom_exact hX' hY' g A)
    (source_coneInclusion_hom_exact hc hd (coneInclusion (coneInclusion f)) A)
    (source_coneInclusion_hom_exact hY hc (coneInclusion f) A)
    (source_coneInclusion_hom_exact hX hY f A)
    ((isIso_iff_coyoneda_map_bijective (sourceLocalization.map e)).mp inferInstance A).2
    ((isIso_iff_coyoneda_map_bijective (sourceLocalization.map d)).mp inferInstance A)
    ((isIso_iff_coyoneda_map_bijective (sourceLocalization.map b)).mp inferInstance A)
    ((isIso_iff_coyoneda_map_bijective (sourceLocalization.map a)).mp inferInstance A).1

end KIP126.StableHomotopy.Implementation.Prespectrum
