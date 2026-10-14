module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.FiberComparison.Source.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Detection.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- Covariant exactness on the original source hom groups, for every strict map. -/
theorem source_coneInclusion_postcomp_hom_exact {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (A : SourceCategory.{u}) :
    Function.Exact (Preadditive.rightComp A (sourceLocalization.map f))
      (Preadditive.rightComp A (sourceLocalization.map (coneInclusion f))) :=
  source_coneInclusion_postcomp_exact f A

/-- Stable equivalences on both ends induce a stable equivalence of the actual
literal cones, without cofibrancy or separation assumptions on the four objects. -/
theorem coneMap_stableEquivalence {X Y X' Y' : Prespectrum.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (ha : stableEquivalences a) (hb : stableEquivalences b) :
    stableEquivalences (coneMap a b h) := by
  let c := coneMap a b h
  let d := coneMap b c (coneInclusion_map a b h)
  let e := coneMap c d (coneInclusion_map b c (coneInclusion_map a b h))
  letI := stableEquivalences.Q_inverts a ha
  letI := stableEquivalences.Q_inverts b hb
  letI := stableEquivalences.Q_inverts d (coneMap_twice_stableEquivalence a b h ha)
  letI := stableEquivalences.Q_inverts e
    (coneMap_twice_stableEquivalence b c (coneInclusion_map a b h) hb)
  apply (stableEquivalence_iff_source_isIso _).mpr
  apply isIso_of_yoneda_map_bijective
  intro A
  have comm {U V U' V' : Prespectrum.{u}} {p : U ⟶ V} {q : U' ⟶ V'}
      (i : U ⟶ U') (j : V ⟶ V') (w : p ≫ j = i ≫ q) :
      (Preadditive.rightComp A (sourceLocalization.map q)).comp
          (Preadditive.rightComp A (sourceLocalization.map i)) =
        (Preadditive.rightComp A (sourceLocalization.map j)).comp
          (Preadditive.rightComp A (sourceLocalization.map p)) := by
    ext z
    change (z ≫ sourceLocalization.map i) ≫ sourceLocalization.map q =
      (z ≫ sourceLocalization.map p) ≫ sourceLocalization.map j
    rw [Category.assoc, ← sourceLocalization.map_comp, ← w,
      sourceLocalization.map_comp, Category.assoc]
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (Preadditive.rightComp A (sourceLocalization.map f))
    (Preadditive.rightComp A (sourceLocalization.map (coneInclusion f)))
    (Preadditive.rightComp A (sourceLocalization.map (coneInclusion (coneInclusion f))))
    (Preadditive.rightComp A (sourceLocalization.map (coneInclusion (coneInclusion (coneInclusion f)))))
    (Preadditive.rightComp A (sourceLocalization.map g))
    (Preadditive.rightComp A (sourceLocalization.map (coneInclusion g)))
    (Preadditive.rightComp A (sourceLocalization.map (coneInclusion (coneInclusion g))))
    (Preadditive.rightComp A (sourceLocalization.map (coneInclusion (coneInclusion (coneInclusion g)))))
    (Preadditive.rightComp A (sourceLocalization.map a))
    (Preadditive.rightComp A (sourceLocalization.map b))
    (Preadditive.rightComp A (sourceLocalization.map c))
    (Preadditive.rightComp A (sourceLocalization.map d))
    (Preadditive.rightComp A (sourceLocalization.map e))
    (comm a b h) (comm b c (coneInclusion_map a b h))
    (comm c d (coneInclusion_map b c (coneInclusion_map a b h)))
    (comm d e (coneInclusion_map c d (coneInclusion_map b c (coneInclusion_map a b h))))
    (source_coneInclusion_postcomp_hom_exact f A)
    (source_coneInclusion_postcomp_hom_exact (coneInclusion f) A)
    (source_coneInclusion_postcomp_hom_exact (coneInclusion (coneInclusion f)) A)
    (source_coneInclusion_postcomp_hom_exact g A)
    (source_coneInclusion_postcomp_hom_exact (coneInclusion g) A)
    (source_coneInclusion_postcomp_hom_exact (coneInclusion (coneInclusion g)) A)
    ((isIso_iff_yoneda_map_bijective (sourceLocalization.map a)).mp inferInstance A).2
    ((isIso_iff_yoneda_map_bijective (sourceLocalization.map b)).mp inferInstance A)
    ((isIso_iff_yoneda_map_bijective (sourceLocalization.map d)).mp inferInstance A)
    ((isIso_iff_yoneda_map_bijective (sourceLocalization.map e)).mp inferInstance A).1

/-- Actual cone and target equivalences detect source equivalences without
cofibrancy assumptions. -/
theorem stableEquivalence_source_of_coneMap_general {X Y X' Y' : Prespectrum.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (hb : stableEquivalences b)
    (hc : stableEquivalences (coneMap a b h)) : stableEquivalences a := by
  apply (coneMap_twice_stableEquivalence_iff a b h).mp
  exact coneMap_stableEquivalence b (coneMap a b h) (coneInclusion_map a b h) hb hc

/-- Actual source and cone equivalences detect target equivalences without
cofibrancy assumptions. -/
theorem stableEquivalence_target_of_coneMap_general {X Y X' Y' : Prespectrum.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (ha : stableEquivalences a)
    (hc : stableEquivalences (coneMap a b h)) : stableEquivalences b := by
  let c := coneMap a b h
  let d := coneMap b c (coneInclusion_map a b h)
  apply (coneMap_twice_stableEquivalence_iff b c (coneInclusion_map a b h)).mp
  exact coneMap_stableEquivalence c d
    (coneInclusion_map b c (coneInclusion_map a b h)) hc
    (coneMap_twice_stableEquivalence a b h ha)

end KIP126.StableHomotopy.Implementation.Prespectrum
