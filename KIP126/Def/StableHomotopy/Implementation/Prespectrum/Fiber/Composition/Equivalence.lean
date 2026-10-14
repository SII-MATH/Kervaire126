module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The reverse comparison has an actual strict homotopy to the identity:
pad its paths, reverse the retained-square deformation, and remove padding. -/
noncomputable def fiberCompositeRetractionComparisonHomotopy {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    StrictHomotopy (fiberCompositeRetraction f g ≫ fiberCompositeComparison f g)
      (𝟙 (fiber (fiberCompositeProjection f g))) := by
  let a := fiberCompositeRetraction f g ≫ fiberCompositeComparison f g
  let padding : StrictHomotopy
      (fiberCompositePaddingHomotopy f g ≫ pathEvaluation _ 0)
      (𝟙 (fiber (fiberCompositeProjection f g))) :=
    ⟨fiberCompositePaddingHomotopy f g,rfl,fiberCompositePaddingHomotopy_one f g⟩
  let move : StrictHomotopy
      (fiberCompositePaddingHomotopy f g ≫ pathEvaluation _ 0)
      (a ≫ (fiberCompositePaddingHomotopy f g ≫ pathEvaluation _ 0)) :=
    ⟨fiberCompositeMoveHomotopy f g,fiberCompositeMoveHomotopy_zero f g,
      fiberCompositeMoveHomotopy_one f g⟩
  simpa only [Category.comp_id] using
    ((padding.precomp a).symm.trans move.symm).trans padding

/-- The fiber of the composite-fiber projection is the original first
fiber in the ordinary source, via the actual retained-square comparison. -/
noncomputable def sourceFiberCompositeIso {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    sourceLocalization.obj (fiber f) ≅
      sourceLocalization.obj (fiber (fiberCompositeProjection f g)) where
  hom := sourceLocalization.map (fiberCompositeComparison f g)
  inv := sourceLocalization.map (fiberCompositeRetraction f g)
  hom_inv_id := by
    rw [← Functor.map_comp,fiberCompositeComparison_retraction,sourceLocalization.map_id]
  inv_hom_id := by
    rw [← Functor.map_comp]
    exact (source_map_eq_of_pathHomotopic
      ⟨fiberCompositeRetractionComparisonHomotopy f g⟩).trans (sourceLocalization.map_id _)

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual composite-fiber comparison is a stable equivalence for
every composable pair, with no lifting or convergence premise. -/
theorem fiberCompositeComparison_stableEquivalence {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    stableEquivalences (fiberCompositeComparison f g) :=
  (stableEquivalence_iff_source_isIso _).mpr
    (inferInstance : IsIso (sourceFiberCompositeIso f g).hom)

theorem fiberCompositeRetraction_stableEquivalence {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    stableEquivalences (fiberCompositeRetraction f g) :=
  (stableEquivalence_iff_source_isIso _).mpr
    (inferInstance : IsIso (sourceFiberCompositeIso f g).inv)

@[simp, reassoc] theorem sourceFiberCompositeIso_projection {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (sourceFiberCompositeIso f g).hom ≫
        sourceLocalization.map (fiberProjection (fiberCompositeProjection f g)) =
      sourceLocalization.map (fiberCompositeInclusion f g) := by
  change sourceLocalization.map (fiberCompositeComparison f g) ≫ _ = _
  rw [← Functor.map_comp,fiberCompositeComparison_projection]

end KIP126.StableHomotopy.Implementation.Prespectrum

end
