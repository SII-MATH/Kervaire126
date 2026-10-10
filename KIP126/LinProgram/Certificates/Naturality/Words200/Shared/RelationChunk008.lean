import KIP126.LinProgram.Certificates.Naturality.Words200.Support

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk008
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
set_option Elab.async false
attribute [local cbv_eval] cetaCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.splitOn_newline SquareDetection.toNat?_eq_chars
  BasisCatalogue.splitOn_pipe
open Lean Elab Tactic in
private def block0 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[8]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 8 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[8]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block1_mem : block1 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 1) (by decide)
private theorem block1_in_rows (r : List Char) (hr : r ∈ block1) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block1, block1_mem, hr⟩
private theorem block2_mem : block2 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 2) (by decide)
private theorem block2_in_rows (r : List Char) (hr : r ∈ block2) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block2, block2_mem, hr⟩
private theorem block3_mem : block3 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 3) (by decide)
private theorem block3_in_rows (r : List Char) (hr : r ∈ block3) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block3, block3_mem, hr⟩
private theorem block8_mem : block8 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 8) (by decide)
private theorem block8_in_rows (r : List Char) (hr : r ∈ block8) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block8, block8_mem, hr⟩
private theorem block9_mem : block9 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 9) (by decide)
private theorem block9_in_rows (r : List Char) (hr : r ∈ block9) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block9, block9_mem, hr⟩
private theorem block10_mem : block10 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 10) (by decide)
private theorem block10_in_rows (r : List Char) (hr : r ∈ block10) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block10, block10_mem, hr⟩
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
private theorem block12_mem : block12 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 12) (by decide)
private theorem block12_in_rows (r : List Char) (hr : r ∈ block12) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block12, block12_mem, hr⟩
private theorem block13_mem : block13 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 13) (by decide)
private theorem block13_in_rows (r : List Char) (hr : r ∈ block13) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block13, block13_mem, hr⟩
private theorem block15_mem : block15 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 15) (by decide)
private theorem block15_in_rows (r : List Char) (hr : r ∈ block15) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block15, block15_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
private theorem block17_mem : block17 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 17) (by decide)
private theorem block17_in_rows (r : List Char) (hr : r ∈ block17) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block17, block17_mem, hr⟩
private theorem block21_mem : block21 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 21) (by decide)
private theorem block21_in_rows (r : List Char) (hr : r ∈ block21) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block21, block21_mem, hr⟩
private theorem block22_mem : block22 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 22) (by decide)
private theorem block22_in_rows (r : List Char) (hr : r ∈ block22) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block22, block22_mem, hr⟩
private theorem block23_mem : block23 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 23) (by decide)
private theorem block23_in_rows (r : List Char) (hr : r ∈ block23) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block23, block23_mem, hr⟩
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block26_mem : block26 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 26) (by decide)
private theorem block26_in_rows (r : List Char) (hr : r ∈ block26) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block26, block26_mem, hr⟩
private theorem block27_mem : block27 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 27) (by decide)
private theorem block27_in_rows (r : List Char) (hr : r ∈ block27) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block27, block27_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation442_mem : "2,2,286,1;1,1,328,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block0[1]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation442_zero : nativeImage "2,2,286,1;1,1,328,1" = 0 := by
  change projection (relationPolynomial "2,2,286,1;1,1,328,1") = 0
  exact csv_relation_zero _ relation442_mem
theorem relation443_mem : "0,2,2,1,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block1[9]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation443_zero : nativeImage "0,2,2,1,292,1" = 0 := by
  change projection (relationPolynomial "0,2,2,1,292,1") = 0
  exact csv_relation_zero _ relation443_mem
theorem relation444_mem : "13,1,208,1;9,1,219,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block1[19]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation444_zero : nativeImage "13,1,208,1;9,1,219,1" = 0 := by
  change projection (relationPolynomial "13,1,208,1;9,1,219,1") = 0
  exact csv_relation_zero _ relation444_mem
theorem relation445_mem : "0,3,316,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block1[23]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation445_zero : nativeImage "0,3,316,1" = 0 := by
  change projection (relationPolynomial "0,3,316,1") = 0
  exact csv_relation_zero _ relation445_mem
theorem relation446_mem : "20,1,167,1;8,1,233,1;0,2,64,1,72,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block2[1]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation446_zero : nativeImage "20,1,167,1;8,1,233,1;0,2,64,1,72,1" = 0 := by
  change projection (relationPolynomial "20,1,167,1;8,1,233,1;0,2,64,1,72,1") = 0
  exact csv_relation_zero _ relation446_mem
theorem relation447_mem : "0,2,64,1,72,1;0,5,301,1;0,5,300,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block2[2]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation447_zero : nativeImage "0,2,64,1,72,1;0,5,301,1;0,5,300,1" = 0 := by
  change projection (relationPolynomial "0,2,64,1,72,1;0,5,301,1;0,5,300,1") = 0
  exact csv_relation_zero _ relation447_mem
theorem relation448_mem : "17,1,180,1;8,1,232,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block2[11]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation448_zero : nativeImage "17,1,180,1;8,1,232,1" = 0 := by
  change projection (relationPolynomial "17,1,180,1;8,1,232,1") = 0
  exact csv_relation_zero _ relation448_mem
theorem relation449_mem : "0,2,8,2,16,1,64,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block3[6]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation449_zero : nativeImage "0,2,8,2,16,1,64,1" = 0 := by
  change projection (relationPolynomial "0,2,8,2,16,1,64,1") = 0
  exact csv_relation_zero _ relation449_mem
theorem relation450_mem : "64,1,80,1;17,1,187,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block8[10]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation450_zero : nativeImage "64,1,80,1;17,1,187,1" = 0 := by
  change projection (relationPolynomial "64,1,80,1;17,1,187,1") = 0
  exact csv_relation_zero _ relation450_mem
theorem relation451_mem : "17,1,187,1;16,1,188,1;0,1,347,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block8[17]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation451_zero : nativeImage "17,1,187,1;16,1,188,1;0,1,347,1" = 0 := by
  change projection (relationPolynomial "17,1,187,1;16,1,188,1;0,1,347,1") = 0
  exact csv_relation_zero _ relation451_mem
theorem relation452_mem : "17,1,186,1;8,2,9,1,101,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block9[19]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation452_zero : nativeImage "17,1,186,1;8,2,9,1,101,1" = 0 := by
  change projection (relationPolynomial "17,1,186,1;8,2,9,1,101,1") = 0
  exact csv_relation_zero _ relation452_mem
theorem relation453_mem : "17,1,20,1,80,1;8,1,23,1,113,1;7,1,245,1;0,6,301,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block10[12]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation453_zero : nativeImage "17,1,20,1,80,1;8,1,23,1,113,1;7,1,245,1;0,6,301,1" = 0 := by
  change projection (relationPolynomial "17,1,20,1,80,1;8,1,23,1,113,1;7,1,245,1;0,6,301,1") = 0
  exact csv_relation_zero _ relation453_mem
theorem relation454_mem : "7,1,245,1;0,6,300,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block10[13]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation454_zero : nativeImage "7,1,245,1;0,6,300,1" = 0 := by
  change projection (relationPolynomial "7,1,245,1;0,6,300,1") = 0
  exact csv_relation_zero _ relation454_mem
theorem relation455_mem : "17,1,184,1;8,1,238,1;6,1,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block11[23]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation455_zero : nativeImage "17,1,184,1;8,1,238,1;6,1,244,1" = 0 := by
  change projection (relationPolynomial "17,1,184,1;8,1,238,1;6,1,244,1") = 0
  exact csv_relation_zero _ relation455_mem
theorem relation456_mem : "6,1,244,1;0,1,343,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block11[24]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation456_zero : nativeImage "6,1,244,1;0,1,343,1" = 0 := by
  change projection (relationPolynomial "6,1,244,1;0,1,343,1") = 0
  exact csv_relation_zero _ relation456_mem
theorem relation457_mem : "9,1,224,1;8,1,237,1;1,1,5,1,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block12[5]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation457_zero : nativeImage "9,1,224,1;8,1,237,1;1,1,5,1,244,1" = 0 := by
  change projection (relationPolynomial "9,1,224,1;8,1,237,1;1,1,5,1,244,1") = 0
  exact csv_relation_zero _ relation457_mem
theorem relation458_mem : "17,1,182,1;16,1,183,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block13[11]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation458_zero : nativeImage "17,1,182,1;16,1,183,1" = 0 := by
  change projection (relationPolynomial "17,1,182,1;16,1,183,1") = 0
  exact csv_relation_zero _ relation458_mem
theorem relation459_mem : "23,1,164,1;13,2,134,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block15[23]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation459_zero : nativeImage "23,1,164,1;13,2,134,1" = 0 := by
  change projection (relationPolynomial "23,1,164,1;13,2,134,1") = 0
  exact csv_relation_zero _ relation459_mem
theorem relation460_mem : "8,2,20,1,69,1;7,1,255,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block15[25]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation460_zero : nativeImage "8,2,20,1,69,1;7,1,255,1" = 0 := by
  change projection (relationPolynomial "8,2,20,1,69,1;7,1,255,1") = 0
  exact csv_relation_zero _ relation460_mem
theorem relation461_mem : "7,1,255,1;1,1,349,1;0,6,312,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block16[0]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation461_zero : nativeImage "7,1,255,1;1,1,349,1;0,6,312,1" = 0 := by
  change projection (relationPolynomial "7,1,255,1;1,1,349,1;0,6,312,1") = 0
  exact csv_relation_zero _ relation461_mem
theorem relation462_mem : "1,1,346,1;0,1,356,1;0,1,355,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block17[18]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation462_zero : nativeImage "1,1,346,1;0,1,356,1;0,1,355,1" = 0 := by
  change projection (relationPolynomial "1,1,346,1;0,1,356,1;0,1,355,1") = 0
  exact csv_relation_zero _ relation462_mem
theorem relation463_mem : "2,1,339,1;1,1,368,1;0,1,377,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block21[19]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation463_zero : nativeImage "2,1,339,1;1,1,368,1;0,1,377,1" = 0 := by
  change projection (relationPolynomial "2,1,339,1;1,1,368,1;0,1,377,1") = 0
  exact csv_relation_zero _ relation463_mem
theorem relation464_mem : "69,1,83,1;69,1,82,1;18,1,190,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block21[22]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation464_zero : nativeImage "69,1,83,1;69,1,82,1;18,1,190,1" = 0 := by
  change projection (relationPolynomial "69,1,83,1;69,1,82,1;18,1,190,1") = 0
  exact csv_relation_zero _ relation464_mem
theorem relation465_mem : "75,1,76,1;18,1,189,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block22[5]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation465_zero : nativeImage "75,1,76,1;18,1,189,1" = 0 := by
  change projection (relationPolynomial "75,1,76,1;18,1,189,1") = 0
  exact csv_relation_zero _ relation465_mem
theorem relation466_mem : "75,2;18,1,188,1;0,1,371,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block22[18]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation466_zero : nativeImage "75,2;18,1,188,1;0,1,371,1" = 0 := by
  change projection (relationPolynomial "75,2;18,1,188,1;0,1,371,1") = 0
  exact csv_relation_zero _ relation466_mem
theorem relation467_mem : "7,2,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block22[30]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation467_zero : nativeImage "7,2,188,1" = 0 := by
  change projection (relationPolynomial "7,2,188,1") = 0
  exact csv_relation_zero _ relation467_mem
theorem relation468_mem : "67,1,82,1;3,1,306,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block23[28]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation468_zero : nativeImage "67,1,82,1;3,1,306,1" = 0 := by
  change projection (relationPolynomial "67,1,82,1;3,1,306,1") = 0
  exact csv_relation_zero _ relation468_mem
theorem relation469_mem : "3,1,306,1;0,1,370,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block23[31]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation469_zero : nativeImage "3,1,306,1;0,1,370,1" = 0 := by
  change projection (relationPolynomial "3,1,306,1;0,1,370,1") = 0
  exact csv_relation_zero _ relation469_mem
theorem relation470_mem : "2,2,302,1;1,1,357,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block25[17]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation470_zero : nativeImage "2,2,302,1;1,1,357,1" = 0 := by
  change projection (relationPolynomial "2,2,302,1;1,1,357,1") = 0
  exact csv_relation_zero _ relation470_mem
theorem relation471_mem : "23,1,168,1;13,1,220,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block26[13]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation471_zero : nativeImage "23,1,168,1;13,1,220,1" = 0 := by
  change projection (relationPolynomial "23,1,168,1;13,1,220,1") = 0
  exact csv_relation_zero _ relation471_mem
theorem relation472_mem : "23,1,167,1;13,1,219,1;0,2,16,1,188,1;0,3,347,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block26[29]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation472_zero : nativeImage "23,1,167,1;13,1,219,1;0,2,16,1,188,1;0,3,347,1" = 0 := by
  change projection (relationPolynomial "23,1,167,1;13,1,219,1;0,2,16,1,188,1;0,3,347,1") = 0
  exact csv_relation_zero _ relation472_mem
theorem relation473_mem : "0,3,346,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block26[30]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation473_zero : nativeImage "0,3,346,1" = 0 := by
  change projection (relationPolynomial "0,3,346,1") = 0
  exact csv_relation_zero _ relation473_mem
theorem relation474_mem : "22,1,167,1;13,1,218,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block27[7]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation474_zero : nativeImage "22,1,167,1;13,1,218,1" = 0 := by
  change projection (relationPolynomial "22,1,167,1;13,1,218,1") = 0
  exact csv_relation_zero _ relation474_mem
theorem relation475_mem : "13,1,218,1;9,1,233,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block27[9]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation475_zero : nativeImage "13,1,218,1;9,1,233,1" = 0 := by
  change projection (relationPolynomial "13,1,218,1;9,1,233,1") = 0
  exact csv_relation_zero _ relation475_mem
theorem relation476_mem : "9,1,233,1;8,1,248,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block27[10]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation476_zero : nativeImage "9,1,233,1;8,1,248,1" = 0 := by
  change projection (relationPolynomial "9,1,233,1;8,1,248,1") = 0
  exact csv_relation_zero _ relation476_mem
theorem relation477_mem : "17,1,194,1;9,1,232,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block27[26]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation477_zero : nativeImage "17,1,194,1;9,1,232,1" = 0 := by
  change projection (relationPolynomial "17,1,194,1;9,1,232,1") = 0
  exact csv_relation_zero _ relation477_mem
theorem relation478_mem : "9,1,232,1;8,2,167,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block27[27]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation478_zero : nativeImage "9,1,232,1;8,2,167,1" = 0 := by
  change projection (relationPolynomial "9,1,232,1;8,2,167,1") = 0
  exact csv_relation_zero _ relation478_mem
theorem relation479_mem : "17,1,193,1;16,1,194,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block28[6]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation479_zero : nativeImage "17,1,193,1;16,1,194,1" = 0 := by
  change projection (relationPolynomial "17,1,193,1;16,1,194,1") = 0
  exact csv_relation_zero _ relation479_mem
theorem relation480_mem : "16,1,194,1;8,2,166,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block28[7]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation480_zero : nativeImage "16,1,194,1;8,2,166,1" = 0 := by
  change projection (relationPolynomial "16,1,194,1;8,2,166,1") = 0
  exact csv_relation_zero _ relation480_mem
theorem relation481_mem : "8,1,246,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block28[12]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation481_zero : nativeImage "8,1,246,1" = 0 := by
  change projection (relationPolynomial "8,1,246,1") = 0
  exact csv_relation_zero _ relation481_mem
theorem relation482_mem : "2,1,352,1;1,1,376,1;0,1,394,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block30[27]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation482_zero : nativeImage "2,1,352,1;1,1,376,1;0,1,394,1" = 0 := by
  change projection (relationPolynomial "2,1,352,1;1,1,376,1;0,1,394,1") = 0
  exact csv_relation_zero _ relation482_mem
theorem relation483_mem : "0,1,393,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block30[28]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation483_zero : nativeImage "0,1,393,1" = 0 := by
  change projection (relationPolynomial "0,1,393,1") = 0
  exact csv_relation_zero _ relation483_mem
theorem relation484_mem : "1,1,373,1" ∈ LinE2.RawData.relations := by
  exact relation_member 8 chunkBound rows transcription
    (block31[2]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation484_zero : nativeImage "1,1,373,1" = 0 := by
  change projection (relationPolynomial "1,1,373,1") = 0
  exact csv_relation_zero _ relation484_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk008
