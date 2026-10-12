module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u
set_option backward.isDefEq.respectTransparency false

instance sourceShiftUnit_isIso : IsIso sourceShiftUnit.{u} := by
  haveI (Z : SourceCategory.{u}) : IsIso (sourceShiftUnit.app Z) := by
    rcases Z with ⟨⟨X⟩⟩
    change IsIso (Localization.Construction.NatTransExtension.app _ (sourceLocalization.obj X))
    rw [Localization.Construction.NatTransExtension.app_eq]
    change IsIso (𝟙 (sourceLocalization.obj X))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

instance sourceShiftCounit_isIso : IsIso sourceShiftCounit.{u} := by
  haveI (Z : SourceCategory.{u}) : IsIso (sourceShiftCounit.app Z) := by
    rcases Z with ⟨⟨X⟩⟩
    change IsIso (Localization.Construction.NatTransExtension.app _ (sourceLocalization.obj X))
    rw [Localization.Construction.NatTransExtension.app_eq]
    exact paddedTailInclusion_isIso X
  exact NatIso.isIso_of_isIso_app _

instance sourceSuspensionDesuspensionComparison_isIso :
    IsIso sourceSuspensionDesuspensionComparison.{u} := by
  haveI (Z : SourceCategory.{u}) : IsIso (sourceSuspensionDesuspensionComparison.app Z) := by
    rcases Z with ⟨⟨X⟩⟩
    change IsIso (Localization.Construction.NatTransExtension.app _ (sourceLocalization.obj X))
    rw [Localization.Construction.NatTransExtension.app_eq]
    exact suspensionDesuspensionComparison_sourceMap_isIso X
  exact NatIso.isIso_of_isIso_app _


end KIP126.StableHomotopy.Implementation.Prespectrum
