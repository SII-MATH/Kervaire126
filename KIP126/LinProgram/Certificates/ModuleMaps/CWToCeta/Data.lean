module

public import KIP126.LinProgram.Certificates.ModuleMaps.Support
public import KIP126.LinProgram.Certificates.ModuleMaps.ModuleTerms
public import KIP126.LinProgram.Generated.ModuleMaps.CWToCeta
public import KIP126.LinProgram.Model.Modules

@[expose] public section

open NamedElementCertificates
open KIP126.LinE2 KIP126.LinE2.NativeModuleCertificates
open KIP126.LinE2.NativeModuleCertificates.Support
open KIP126.LinModule.NativeMapCertificates
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local cbv_eval] SquareDetection.splitOn_comma
  SquareDetection.splitOn_semicolon SquareDetection.toNat?_eq_chars

namespace KIP126.LinModule.CWToCeta
noncomputable def generatorImage (i : KIP126.LinModule.CWNuEta.Generator) : KIP126.LinModule.Ceta.Model :=
  nativeModuleImage 887 KIP126.LinModule.RawData.Ceta.relations
    (KIP126.LinModule.RawData.Maps.CWToCeta.imageCode i)
def imageTerms (i : KIP126.LinModule.CWNuEta.Generator) : ModuleTerms 887 :=
  nativeModuleTerms 887 (KIP126.LinModule.RawData.Maps.CWToCeta.imageCode i)
theorem imageTerms_evaluate (i : KIP126.LinModule.CWNuEta.Generator) :
    ModuleExpressions.evaluate nativeScalar KIP126.LinModule.Ceta.generator
      (termsExpression (imageTerms i)) = generatorImage i :=
  evaluate_nativeModuleTerms 887 KIP126.LinModule.RawData.Ceta.relations _
end KIP126.LinModule.CWToCeta
