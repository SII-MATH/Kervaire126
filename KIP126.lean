import KIP126.LinProgram.Certificates.BasisTable.Proofs
import KIP126.Interface.Challenge.Literature.EtaRows
import KIP126.LinProgram.SourceMetadata.AppendixTable.Rows.Catalogue.Data
import KIP126.Main.Solution.Computation.Tower.Survival
import KIP126.Def.Comparison.PageExtension.Solutions.Finiteness.Proofs
import KIP126.Def.Comparison.PageExtension.Solutions.Coherence.Proofs
import KIP126.Mathlib.ClassicalAdams.StandardSphere.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.LongLayer.Lifting.Proofs
import KIP126.Main.Solution.Computation.Vanishing
import KIP126.Main.Solution.Computation.Nonvanishing
import KIP126.Main.Solution.Computation.Dimension
import KIP126.Main.Solution.Computation.Comparisons.Classes
import KIP126.Main.Solution.Computation.Differential.Second
import KIP126.Main.Solution.Computation.Reduction
import KIP126.LinProgram.Certificates.SquareDetection.Certificate
import KIP126.Interface.Solution.LinProgram.BasisTable
import KIP126.Def.Comparison.Pages.Proofs
import KIP126.Def.Comparison.Pages.Naturality.Proofs
import KIP126.Def.Comparison.Cobar.Proofs
import KIP126.Interface.Solution.LinProgram.Multiplication
import KIP126.Def.Comparison.PageExtension.Solutions.Proofs
import KIP126.Def
import KIP126.Interface.Challenge.Challenge2
import KIP126.Def.Solution
import KIP126.LinProgram.Interpretation.AdamsE2.Classes.Proofs
import KIP126.Interface
import KIP126.Main
import KIP126.Main.Solution
import KIP126.Mathlib
import KIP126.Checks.Examples.LinProgram.AdamsE2Table
import KIP126.Checks.Examples.LinProgram.AdamsE2LowDegrees
import KIP126.Checks.SourceMetadata.AppendixTable.Rows.Catalogue.Proofs

/-! Library entry for shared definitions, stage inputs and open statements.
Main's paper deductions are exported from Solution, without intermediate
Challenge mirrors. The stage Solution tracks also have separate entry modules.
Previously exposed helper results remain re-exported here for compatibility. Importing a Challenge
never establishes proof completion. Regression modules live in `KIP126.Checks`. -/
