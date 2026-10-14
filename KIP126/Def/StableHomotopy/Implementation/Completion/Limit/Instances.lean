module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Limit.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory CategoryTheory.Limits

universe v u

/-- The actual inclusion creates every limit that exists in the source. -/
noncomputable instance toSource_createsLimit {J : Type u} [Category.{v} J]
    (F : J ⥤ CompletedSpectrum) : CreatesLimit F toSource where
  lifts := liftSourceLimit F

noncomputable instance toSource_createsLimitsOfShape (J : Type u) [Category.{v} J] :
    CreatesLimitsOfShape J toSource where
  CreatesLimit := toSource_createsLimit _

/-- Whenever the actual source has limits of a shape, the same is true
of its HF₂-local subcategory. -/
theorem hasLimitsOfShape_of_source (J : Type u) [Category.{v} J]
    [HasLimitsOfShape J SourceCategory.{0}] : HasLimitsOfShape J CompletedSpectrum :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape toSource

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
