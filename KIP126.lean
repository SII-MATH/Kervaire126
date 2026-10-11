module

public import KIP126.LinProgram.Certificates.BasisTable.Proofs
public import KIP126.Interface.Challenge.Literature.EtaRows
public import KIP126.LinProgram.SourceMetadata.AppendixTable.Rows.Catalogue.Data
public import KIP126.Main.Solution.Computation.Tower.Survival
public import KIP126.Def.Comparison.PageExtension.Solutions.Finiteness.Proofs
public import KIP126.Def.Comparison.PageExtension.Solutions.Coherence.Proofs
public import KIP126.Mathlib.ClassicalAdams.StandardSphere.Proofs
public import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.LongLayer.Lifting.Proofs
public import KIP126.Main.Solution.Computation.Vanishing
public import KIP126.Main.Solution.Computation.Nonvanishing
public import KIP126.Main.Solution.Computation.Dimension
public import KIP126.Main.Solution.Computation.Comparisons.Classes
public import KIP126.Main.Solution.Computation.Differential.Second
public import KIP126.Main.Solution.Computation.Reduction
public import KIP126.LinProgram.Certificates.SquareDetection.Certificate
public import KIP126.Interface.Solution.LinProgram.BasisTable
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
public import KIP126.Mathlib
public import KIP126.Checks.Examples.LinProgram.AdamsE2Table
public import KIP126.Checks.Examples.LinProgram.AdamsE2LowDegrees
public import KIP126.Checks.SourceMetadata.AppendixTable.Rows.Catalogue.Proofs

@[expose] public section

/-! Library entry for shared definitions, stage inputs and open statements.
Main's paper deductions are exported from Solution, without intermediate
Challenge mirrors. The stage Solution tracks also have separate entry modules.
Previously exposed helper results remain re-exported here for compatibility. Importing a Challenge
never establishes proof completion. Regression modules live in `KIP126.Checks`. -/
