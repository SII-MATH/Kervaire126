module

public import KIP126.LinProgram.Certificates.Secondary.Contraction
public import KIP126.LinProgram.Certificates.Secondary.Augmentation
public import KIP126.LinProgram.Certificates.Secondary.Milnor.ProductTables
public import KIP126.LinProgram.Certificates.Secondary.IndexedExpansion
public import KIP126.LinProgram.Certificates.ModuleMaps.CWToCeta.Grading
public import KIP126.LinProgram.Certificates.ModuleMaps.CWMaxSupport
public import KIP126.LinProgram.Certificates.ModuleMaps.CetaToSphere.Grading
public import KIP126.Def.StableHomotopy.Implementation.TensorCompatibility.Proofs
public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.BoundaryTower.Connecting.Proofs
public import KIP126.LinProgram.Generated.ModuleMaps.CetaToSphere
public import KIP126.LinProgram.Generated.ModuleMaps.CWToCeta
public import KIP126.LinProgram.Model.ModulePresentation.Maps
public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.BoundaryTower.Proofs
public import KIP126.LinProgram.Certificates.StemFour
public import KIP126.Def.ClassicalAdams.Detection.Vanishing
public import KIP126.LinProgram.Certificates.Products.Naturality462481Modules
public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Stage.Comparison.Proofs
public import KIP126.Interface.Solution.LinProgram.Naturality.CWToCeta
public import KIP126.Interface.Solution.Literature.StandardSphere
public import KIP126.Def.StableHomotopy.Context.CofiberExtension.Proofs
public import KIP126.LinProgram.Certificates.Products.Naturality462481
public import KIP126.LinProgram.Certificates.BranchPageThree
public import KIP126.Interface.Solution.LinProgram.Naturality.Row462481
public import KIP126.Interface.Solution.LinProgram.AdamsOneLine.H6
public import KIP126.LinProgram.Certificates.Secondary.Seed5487.Proofs
public import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.Stage.Proofs
public import KIP126.Interface.Solution.LinProgram.Products.Trial152097
public import KIP126.LinProgram.Certificates.Products.Trial152097
public import KIP126.LinProgram.Interpretation.Branch.Proofs
public import KIP126.Interface.Solution.LinProgram.Naturality.Row245131
public import KIP126.LinProgram.Certificates.Naturality.Row245131Map
public import KIP126.LinProgram.Certificates.Naturality.Batch21
public import KIP126.LinProgram.Certificates.Naturality.CochainBatch21
public import KIP126.LinProgram.Certificates.Naturality.Words200.All
public import KIP126.LinProgram.Certificates.Naturality.Words200.Native
public import KIP126.LinProgram.Model.E2.Native.Basis
public import KIP126.LinProgram.Model.E2.Native.Descent
public import KIP126.LinProgram.Certificates.Naturality.CochainBatch40
public import KIP126.LinProgram.Certificates.BasisCertification.Proofs
public import KIP126.Interface.Challenge.Literature.EtaRows
public import KIP126.LinProgram.SourceMetadata.AppendixTable.Rows.Catalogue.Data
public import KIP126.Main.Solution.Computation.Tower.Survival
public import KIP126.Def.Comparison.PageExtension.Solutions.Finiteness.Proofs
public import KIP126.Def.Comparison.PageExtension.Solutions.Coherence.Proofs
public import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.LongLayer.Lifting.Proofs
public import KIP126.Main.Solution.Computation.Vanishing
public import KIP126.Main.Solution.Computation.Nonvanishing
public import KIP126.Main.Solution.Computation.Dimension
public import KIP126.Main.Solution.Computation.Comparisons.Classes
public import KIP126.Main.Solution.Computation.Differential.Second
public import KIP126.Main.Solution.Computation.Reduction
public import KIP126.LinProgram.Certificates.SquareDetection.Certificate
public import KIP126.Interface.Solution.LinProgram.Basis.Certification
public import KIP126.Def.Comparison.Pages.Proofs
public import KIP126.Def.Comparison.Pages.Naturality.Proofs
public import KIP126.Def.Comparison.ClassicalSynthetic.FirstQuotient.Detection.Proofs
public import KIP126.Def.Comparison.ClassicalSynthetic.EInfty.Proofs
public import KIP126.Def.Synthetic.Bockstein.Layer.Zero.Proofs
public import KIP126.Def.Comparison.Cobar.Proofs
public import KIP126.Interface.Solution.LinProgram.Multiplication
public import KIP126.Def.Comparison.PageExtension.Solutions.Proofs
public import KIP126.Def
public import KIP126.Interface.Challenge.Challenge2
public import KIP126.Def.Solution
public import KIP126.LinProgram.Interpretation.AdamsE2.Classes.Proofs
public import KIP126.Interface
public import KIP126.Main
public import KIP126.Main.Solution
public import KIP126.Checks.Examples.LinProgram.AdamsE2Table
public import KIP126.Checks.Examples.LinProgram.AdamsE2LowDegrees
public import KIP126.Checks.SourceMetadata.AppendixTable.Rows.Catalogue.Proofs

@[expose] public section


/-! Library entry for shared definitions, stage inputs and open statements.
Main's paper deductions are exported from Solution, without intermediate
Challenge mirrors. The stage Solution tracks also have separate entry modules.
Previously exposed helper results remain re-exported here for compatibility. Importing a Challenge
never establishes proof completion. Regression modules live in `KIP126.Checks`. -/
