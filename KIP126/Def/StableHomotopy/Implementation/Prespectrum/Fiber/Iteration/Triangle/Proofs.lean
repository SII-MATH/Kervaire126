module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Triangle.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Naturality of the actual suspension-coordinate boundary for arbitrary
source maps whose loop-coordinate connecting square has been proved. -/
theorem sourceFiberBoundary_natural {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (b : sourceLocalization.obj Y ⟶ sourceLocalization.obj Y')
    (c : sourceLocalization.obj (fiber f) ⟶ sourceLocalization.obj (fiber g))
    (h : sourceLocalization.map (fiberConnecting f) ≫ c =
      sourceLoopFunctor.map b ≫ sourceLocalization.map (fiberConnecting g)) :
    sourceFiberBoundary f ≫ c⟦(1 : ℤ)⟧' = b ≫ sourceFiberBoundary g := by
  change (-((sourceSuspensionLoopCounitIso.app (sourceLocalization.obj Y)).inv ≫
    sourceSuspensionFunctor.map (sourceLocalization.map (fiberConnecting f)))) ≫
      sourceSuspensionFunctor.map c = b ≫
        (-((sourceSuspensionLoopCounitIso.app (sourceLocalization.obj Y')).inv ≫
          sourceSuspensionFunctor.map (sourceLocalization.map (fiberConnecting g))))
  simp only [Preadditive.neg_comp,Preadditive.comp_neg]
  congr 1
  rw [Category.assoc,← Functor.map_comp,h,Functor.map_comp,← Category.assoc]
  have hn := sourceSuspensionLoopCounitIso.inv.naturality b
  change b ≫ (sourceSuspensionLoopCounitIso.app (sourceLocalization.obj Y')).inv =
    (sourceSuspensionLoopCounitIso.app (sourceLocalization.obj Y)).inv ≫
      sourceSuspensionFunctor.map (sourceLoopFunctor.map b) at hn
  rw [← hn,Category.assoc]

theorem sourceFiberIterationIso_inv_connecting {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    (sourceFiberIterationIso f).inv ≫ sourceLocalization.map (fiberConnecting f) =
      sourceLocalization.map (fiberProjection (fiberProjection f)) := by
  rw [← sourceFiberIterationIso_projection,← Category.assoc,Iso.inv_hom_id,Category.id_comp]

/-- The connecting morphism of the projection becomes the original map
under the actual third-object rotation isomorphism. -/
theorem sourceFiberIterationSuspensionIso_boundary {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceFiberBoundary (fiberProjection f) ≫ (sourceFiberIterationSuspensionIso f).hom =
      sourceLocalization.map f := by
  change (-((sourceSuspensionLoopCounitIso.app (sourceLocalization.obj X)).inv ≫
    sourceSuspensionFunctor.map (sourceLocalization.map (fiberConnecting (fiberProjection f))))) ≫
      (sourceSuspensionFunctor.map (sourceFiberIterationIso f).inv ≫
        (sourceSuspensionLoopCounitIso.app (sourceLocalization.obj Y)).hom) = _
  rw [Preadditive.neg_comp,Category.assoc,← sourceSuspensionFunctor.map_comp_assoc,
    sourceFiberIterationIso_connecting,Functor.map_neg]
  simp only [Preadditive.neg_comp,Preadditive.comp_neg,neg_neg]
  rw [← sourceLoopFunctor_map]
  change (sourceSuspensionLoopCounitIso.app (sourceLocalization.obj X)).inv ≫
    (sourceLoopFunctor ⋙ sourceSuspensionFunctor).map (sourceLocalization.map f) ≫
      sourceSuspensionLoopCounitIso.hom.app (sourceLocalization.obj Y) = _
  rw [sourceSuspensionLoopCounitIso.hom.naturality]
  change (sourceSuspensionLoopCounitIso.app (sourceLocalization.obj X)).inv ≫
    (sourceSuspensionLoopCounitIso.app (sourceLocalization.obj X)).hom ≫ sourceLocalization.map f = _
  rw [Iso.inv_hom_id_assoc]

/-- The last square of the rotated actual fiber triangle has precisely
the negative shifted projection required by Mathlib's rotation. -/
theorem sourceFiberIterationSuspensionIso_connecting {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    (sourceFiberIterationSuspensionIso f).hom ≫ sourceFiberBoundary f =
      -((sourceLocalization.map (fiberProjection (fiberProjection f)))⟦(1 : ℤ)⟧') := by
  change (sourceSuspensionFunctor.map (sourceFiberIterationIso f).inv ≫
    (sourceSuspensionLoopCounitIso.app (sourceLocalization.obj Y)).hom) ≫
      (-((sourceSuspensionLoopCounitIso.app (sourceLocalization.obj Y)).inv ≫
        sourceSuspensionFunctor.map (sourceLocalization.map (fiberConnecting f)))) = _
  rw [Preadditive.comp_neg,Category.assoc,Iso.hom_inv_id_assoc,← Functor.map_comp,
    sourceFiberIterationIso_inv_connecting]
  rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
