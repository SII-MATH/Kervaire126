module

public import KIP126.LinProgram.Model.ModulePresentation.Data
public import KIP126.LinProgram.Generated.Modules.Ceta
public import KIP126.LinProgram.Generated.Modules.CWNuEta

@[expose] public section


/-! The two complete archived module presentations over the same LinE2.E2.
All native generators and relations are retained. The recorded degree limit
does not impose further zero relations. No actual Ext comparison is supplied. -/
namespace KIP126.LinModule

namespace Ceta
abbrev Generator := Fin RawData.Ceta.generatorCount
abbrev Model := Presentation.Model RawData.Ceta.generatorCount RawData.Ceta.relations
noncomputable def generator (i : Generator) : Model :=
  Presentation.generator _ _ i
noncomputable def monomial (code : String) : Model :=
  Presentation.projection _ _ (Presentation.monomialVector _ code)
end Ceta

namespace CWNuEta
abbrev Generator := Fin RawData.CWNuEta.generatorCount
abbrev Model := Presentation.Model RawData.CWNuEta.generatorCount RawData.CWNuEta.relations
noncomputable def generator (i : Generator) : Model :=
  Presentation.generator _ _ i
noncomputable def monomial (code : String) : Model :=
  Presentation.projection _ _ (Presentation.monomialVector _ code)
end CWNuEta

end KIP126.LinModule
