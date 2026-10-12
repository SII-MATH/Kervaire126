module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Functor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceShiftUnit : 𝟭 SourceCategory.{u} ⟶ sourceDesuspensionFunctor ⋙ sourceTailFunctor :=
  Localization.Construction.natTransExtension {
    app X := 𝟙 (sourceLocalization.obj X)
    naturality := by
      intro X Y f
      change sourceLocalization.map f ≫ 𝟙 _ = 𝟙 _ ≫ sourceTailFunctor.map
        (sourceDesuspensionFunctor.map (sourceLocalization.map f))
      rw [sourceDesuspensionFunctor_map,sourceTailFunctor_map,levelTailMap_desuspensionMap,
        Category.id_comp,Category.comp_id] }

noncomputable def sourceShiftCounit : sourceTailFunctor ⋙ sourceDesuspensionFunctor ⟶ 𝟭 SourceCategory.{u} :=
  Localization.Construction.natTransExtension {
    app X := sourceLocalization.map (paddedTailInclusion X)
    naturality := by
      intro X Y f
      change sourceDesuspensionFunctor.map (sourceTailFunctor.map (sourceLocalization.map f)) ≫
        sourceLocalization.map (paddedTailInclusion Y) =
          sourceLocalization.map (paddedTailInclusion X) ≫ sourceLocalization.map f
      rw [sourceTailFunctor_map,sourceDesuspensionFunctor_map,← Functor.map_comp,← Functor.map_comp,
        paddedTailInclusion_natural] }

/-- The actual mapping-path comparison descends naturally to all source maps. -/
noncomputable def sourceSuspensionDesuspensionComparison :
    sourceDesuspensionFunctor ⋙ sourceSuspensionFunctor ⟶ 𝟭 SourceCategory.{u} :=
  Localization.Construction.natTransExtension {
    app X := (suspensionDesuspensionComparison X).sourceMap
    naturality := by
      intro X Y f
      change sourceSuspensionFunctor.map (sourceDesuspensionFunctor.map (sourceLocalization.map f)) ≫
        (suspensionDesuspensionComparison Y).sourceMap =
          (suspensionDesuspensionComparison X).sourceMap ≫ sourceLocalization.map f
      rw [sourceDesuspensionFunctor_map,sourceSuspensionFunctor_map]
      exact suspensionDesuspensionComparison_sourceMap_natural f }


end KIP126.StableHomotopy.Implementation.Prespectrum
