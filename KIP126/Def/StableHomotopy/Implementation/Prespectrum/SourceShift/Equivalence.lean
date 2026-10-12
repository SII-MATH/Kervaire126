module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Proofs
public import Mathlib.CategoryTheory.Whiskering

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceDesuspensionEquivalence : SourceCategory.{u} ≌ SourceCategory.{u} :=
  CategoryTheory.Equivalence.mk sourceDesuspensionFunctor sourceTailFunctor (asIso sourceShiftUnit) (asIso sourceShiftCounit)


noncomputable def sourceSuspensionTailIso : sourceSuspensionFunctor.{u} ≅ sourceTailFunctor :=
  (Functor.leftUnitor sourceSuspensionFunctor).symm ≪≫
    Functor.isoWhiskerRight (asIso sourceShiftCounit).symm sourceSuspensionFunctor ≪≫
      Functor.associator sourceTailFunctor sourceDesuspensionFunctor sourceSuspensionFunctor ≪≫
        Functor.isoWhiskerLeft sourceTailFunctor (asIso sourceSuspensionDesuspensionComparison) ≪≫
          Functor.rightUnitor sourceTailFunctor

noncomputable def sourceSuspensionEquivalence : SourceCategory.{u} ≌ SourceCategory.{u} :=
  CategoryTheory.Equivalence.mk sourceSuspensionFunctor sourceDesuspensionFunctor
    (Functor.isoWhiskerRight sourceSuspensionTailIso sourceDesuspensionFunctor ≪≫ asIso sourceShiftCounit).symm
    (asIso sourceSuspensionDesuspensionComparison)

/-- The inverse of padded desuspension has the actual levelwise suspension
as its value on every point-set source object, naturally in localized maps. -/
noncomputable def sourceSuspensionComparisonIso (X : Prespectrum.{u}) :
    sourceLocalization.obj X.suspension ≅ sourceTailFunctor.obj (sourceLocalization.obj X) :=
  sourceSuspensionTailIso.app (sourceLocalization.obj X)

end KIP126.StableHomotopy.Implementation.Prespectrum
