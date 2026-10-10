import KIP126.LinProgram.Certificates.SquareDetection.Archive.Batch0
import KIP126.LinProgram.Certificates.SquareDetection.Archive.Batch1
import KIP126.LinProgram.Certificates.SquareDetection.Archive.Batch2
import KIP126.LinProgram.Certificates.SquareDetection.Archive.Batch3
import KIP126.LinProgram.Certificates.SquareDetection.Archive.Batch4
import KIP126.LinProgram.Certificates.SquareDetection.Archive.Batch5
import KIP126.LinProgram.Certificates.SquareDetection.Archive.Batch6
import KIP126.LinProgram.Certificates.SquareDetection.Archive.Batch7
import KIP126.LinProgram.Certificates.SquareDetection

namespace KIP126.LinE2.SquareDetection

set_option maxRecDepth 100000

/-- All 227 original archived chunks have kernel-checked certificates. -/
theorem archivedChunks_check : chunksCheck RawData.relationChunks.toList = true := by
  -- Construct applications of the composition theorem directly: elaborating
  -- underscores against this closed Boolean goal would try to evaluate the
  -- entire checker. The resulting term is still checked by the kernel.
  run_tac do
    let mut xs := Lean.mkApp (Lean.mkConst ``List.nil [Lean.Level.zero])
      (Lean.mkConst ``String)
    let mut proof := Lean.mkConst ``chunksCheck_nil
    for name in [``archivedChunks_batch7, ``archivedChunks_batch6,
        ``archivedChunks_batch5, ``archivedChunks_batch4, ``archivedChunks_batch3,
        ``archivedChunks_batch2, ``archivedChunks_batch1, ``archivedChunks_batch0] do
      let type := (← Lean.getConstInfo name).type
      let some (_, lhs, _) := type.eq? | throwError "expected a chunk certificate"
      let ys := lhs.appArg!
      proof := Lean.mkAppN (Lean.mkConst ``chunksCheck_append)
        #[ys, xs, Lean.mkConst name, proof]
      xs := Lean.mkApp3 (Lean.mkConst ``List.append [Lean.Level.zero])
        (Lean.mkConst ``String) ys xs
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

/-- The complete finite certificate, checked by Lean's kernel. This is a
theorem about the archived quotient relations, not a higher differential. -/
theorem allRelationsCheck_eq_true : allRelationsCheck = true := by
  exact allRelationsCheck_of_chunks (List.all_eq_true.mp archivedChunks_check)

/-- Nonvanishing in the actual Lin quotient, without a finite-check premise,
basis-table soundness, or a native evaluation axiom. -/
theorem dataH6Sq_ne_zero : dataH6Sq ≠ 0 :=
  dataH6Sq_ne_zero_of_check allRelationsCheck_eq_true

end KIP126.LinE2.SquareDetection
