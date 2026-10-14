module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk009
open KIP126.LinE2 NativeMapCertificates BatchMapCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 10000000
set_option Elab.async false
attribute [local cbv_eval] cetaCode_get KIP126.LinE2.generatorDegree_eq_row
  SquareDetection.splitOn_comma SquareDetection.splitOn_semicolon
  SquareDetection.splitOn_newline SquareDetection.toNat?_eq_chars
open Lean Elab Tactic in
private def block0 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[9]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 9 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[9]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block2_mem : block2 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 2) (by decide)
private theorem block2_in_rows (r : List Char) (hr : r ∈ block2) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block2, block2_mem, hr⟩
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
private theorem block6_mem : block6 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 6) (by decide)
private theorem block6_in_rows (r : List Char) (hr : r ∈ block6) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block6, block6_mem, hr⟩
private theorem block7_mem : block7 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 7) (by decide)
private theorem block7_in_rows (r : List Char) (hr : r ∈ block7) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block7, block7_mem, hr⟩
private theorem block8_mem : block8 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 8) (by decide)
private theorem block8_in_rows (r : List Char) (hr : r ∈ block8) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block8, block8_mem, hr⟩
private theorem block9_mem : block9 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 9) (by decide)
private theorem block9_in_rows (r : List Char) (hr : r ∈ block9) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block9, block9_mem, hr⟩
private theorem block13_mem : block13 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 13) (by decide)
private theorem block13_in_rows (r : List Char) (hr : r ∈ block13) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block13, block13_mem, hr⟩
private theorem block19_mem : block19 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 19) (by decide)
private theorem block19_in_rows (r : List Char) (hr : r ∈ block19) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block19, block19_mem, hr⟩
private theorem block20_mem : block20 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 20) (by decide)
private theorem block20_in_rows (r : List Char) (hr : r ∈ block20) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block20, block20_mem, hr⟩
private theorem block24_mem : block24 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 24) (by decide)
private theorem block24_in_rows (r : List Char) (hr : r ∈ block24) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block24, block24_mem, hr⟩
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
theorem relation485_mem : "0,2,371,1;0,2,69,1,79,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block0[7]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation485_zero : nativeImage "0,2,371,1;0,2,69,1,79,1" = 0 := by
  change projection (relationPolynomial "0,2,371,1;0,2,69,1,79,1") = 0
  exact csv_relation_zero _ relation485_mem
theorem relation486_mem : "0,1,383,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block2[6]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation486_zero : nativeImage "0,1,383,1" = 0 := by
  change projection (relationPolynomial "0,1,383,1") = 0
  exact csv_relation_zero _ relation486_mem
theorem relation487_mem : "72,1,80,1;20,1,187,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block2[15]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation487_zero : nativeImage "72,1,80,1;20,1,187,1" = 0 := by
  change projection (relationPolynomial "72,1,80,1;20,1,187,1") = 0
  exact csv_relation_zero _ relation487_mem
theorem relation488_mem : "19,1,188,1;17,1,201,1;15,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block2[17]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation488_zero : nativeImage "19,1,188,1;17,1,201,1;15,1,209,1" = 0 := by
  change projection (relationPolynomial "19,1,188,1;17,1,201,1;15,1,209,1") = 0
  exact csv_relation_zero _ relation488_mem
theorem relation489_mem : "17,1,201,1;15,1,209,1;8,1,255,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block2[18]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation489_zero : nativeImage "17,1,201,1;15,1,209,1;8,1,255,1" = 0 := by
  change projection (relationPolynomial "17,1,201,1;15,1,209,1;8,1,255,1") = 0
  exact csv_relation_zero _ relation489_mem
theorem relation490_mem : "15,1,209,1;2,1,347,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block2[19]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation490_zero : nativeImage "15,1,209,1;2,1,347,1" = 0 := by
  change projection (relationPolynomial "15,1,209,1;2,1,347,1") = 0
  exact csv_relation_zero _ relation490_mem
theorem relation491_mem : "2,1,347,1;0,1,382,1;0,3,359,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block2[22]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation491_zero : nativeImage "2,1,347,1;0,1,382,1;0,3,359,1" = 0 := by
  change projection (relationPolynomial "2,1,347,1;0,1,382,1;0,3,359,1") = 0
  exact csv_relation_zero _ relation491_mem
theorem relation492_mem : "0,1,382,1;0,3,359,1;0,4,349,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block2[23]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation492_zero : nativeImage "0,1,382,1;0,3,359,1;0,4,349,1" = 0 := by
  change projection (relationPolynomial "0,1,382,1;0,3,359,1;0,4,349,1") = 0
  exact csv_relation_zero _ relation492_mem
theorem relation493_mem : "0,1,8,1,245,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block4[29]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation493_zero : nativeImage "0,1,8,1,245,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,245,1") = 0
  exact csv_relation_zero _ relation493_mem
theorem relation494_mem : "13,1,224,1;9,1,237,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block6[8]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation494_zero : nativeImage "13,1,224,1;9,1,237,1" = 0 := by
  change projection (relationPolynomial "13,1,224,1;9,1,237,1") = 0
  exact csv_relation_zero _ relation494_mem
theorem relation495_mem : "9,1,237,1;8,1,16,1,137,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block6[9]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation495_zero : nativeImage "9,1,237,1;8,1,16,1,137,1" = 0 := by
  change projection (relationPolynomial "9,1,237,1;8,1,16,1,137,1") = 0
  exact csv_relation_zero _ relation495_mem
theorem relation496_mem : "17,1,199,1;16,1,200,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block7[11]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation496_zero : nativeImage "17,1,199,1;16,1,200,1" = 0 := by
  change projection (relationPolynomial "17,1,199,1;16,1,200,1") = 0
  exact csv_relation_zero _ relation496_mem
theorem relation497_mem : "16,1,200,1;8,1,253,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block7[12]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation497_zero : nativeImage "16,1,200,1;8,1,253,1" = 0 := by
  change projection (relationPolynomial "16,1,200,1;8,1,253,1") = 0
  exact csv_relation_zero _ relation497_mem
theorem relation498_mem : "9,1,236,1;8,1,252,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block7[20]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation498_zero : nativeImage "9,1,236,1;8,1,252,1" = 0 := by
  change projection (relationPolynomial "9,1,236,1;8,1,252,1") = 0
  exact csv_relation_zero _ relation498_mem
theorem relation499_mem : "2,1,367,1;1,1,394,1;1,1,393,1;0,1,415,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block8[26]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation499_zero : nativeImage "2,1,367,1;1,1,394,1;1,1,393,1;0,1,415,1" = 0 := by
  change projection (relationPolynomial "2,1,367,1;1,1,394,1;1,1,393,1;0,1,415,1") = 0
  exact csv_relation_zero _ relation499_mem
theorem relation500_mem : "1,1,394,1;1,1,392,1;0,2,396,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block8[28]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation500_zero : nativeImage "1,1,394,1;1,1,392,1;0,2,396,1" = 0 := by
  change projection (relationPolynomial "1,1,394,1;1,1,392,1;0,2,396,1") = 0
  exact csv_relation_zero _ relation500_mem
theorem relation501_mem : "3,2,270,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block9[18]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation501_zero : nativeImage "3,2,270,1" = 0 := by
  change projection (relationPolynomial "3,2,270,1") = 0
  exact csv_relation_zero _ relation501_mem
theorem relation502_mem : "68,1,92,1;1,1,389,1;1,1,388,1;0,1,413,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block9[22]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation502_zero : nativeImage "68,1,92,1;1,1,389,1;1,1,388,1;0,1,413,1" = 0 := by
  change projection (relationPolynomial "68,1,92,1;1,1,389,1;1,1,388,1;0,1,413,1") = 0
  exact csv_relation_zero _ relation502_mem
theorem relation503_mem : "0,1,413,1;0,2,391,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block9[24]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation503_zero : nativeImage "0,1,413,1;0,2,391,1" = 0 := by
  change projection (relationPolynomial "0,1,413,1;0,2,391,1") = 0
  exact csv_relation_zero _ relation503_mem
theorem relation504_mem : "2,1,357,1;1,2,359,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block13[31]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation504_zero : nativeImage "2,1,357,1;1,2,359,1" = 0 := by
  change projection (relationPolynomial "2,1,357,1;1,2,359,1") = 0
  exact csv_relation_zero _ relation504_mem
theorem relation505_mem : "3,1,332,1;1,1,413,1;1,1,412,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block19[18]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation505_zero : nativeImage "3,1,332,1;1,1,413,1;1,1,412,1" = 0 := by
  change projection (relationPolynomial "3,1,332,1;1,1,413,1;1,1,412,1") = 0
  exact csv_relation_zero _ relation505_mem
theorem relation506_mem : "24,1,181,1;18,1,201,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block20[12]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation506_zero : nativeImage "24,1,181,1;18,1,201,1" = 0 := by
  change projection (relationPolynomial "24,1,181,1;18,1,201,1") = 0
  exact csv_relation_zero _ relation506_mem
theorem relation507_mem : "18,1,201,1;13,1,235,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block20[13]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation507_zero : nativeImage "18,1,201,1;13,1,235,1" = 0 := by
  change projection (relationPolynomial "18,1,201,1;13,1,235,1") = 0
  exact csv_relation_zero _ relation507_mem
theorem relation508_mem : "13,1,235,1;9,1,251,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block20[15]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation508_zero : nativeImage "13,1,235,1;9,1,251,1" = 0 := by
  change projection (relationPolynomial "13,1,235,1;9,1,251,1") = 0
  exact csv_relation_zero _ relation508_mem
theorem relation509_mem : "29,1,167,1;23,1,180,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block24[11]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation509_zero : nativeImage "29,1,167,1;23,1,180,1" = 0 := by
  change projection (relationPolynomial "29,1,167,1;23,1,180,1") = 0
  exact csv_relation_zero _ relation509_mem
theorem relation510_mem : "23,1,180,1;13,1,233,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block24[13]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation510_zero : nativeImage "23,1,180,1;13,1,233,1" = 0 := by
  change projection (relationPolynomial "23,1,180,1;13,1,233,1") = 0
  exact csv_relation_zero _ relation510_mem
theorem relation511_mem : "13,1,233,1;9,1,248,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block24[14]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation511_zero : nativeImage "13,1,233,1;9,1,248,1" = 0 := by
  change projection (relationPolynomial "13,1,233,1;9,1,248,1") = 0
  exact csv_relation_zero _ relation511_mem
theorem relation512_mem : "20,1,194,1;13,1,232,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block24[23]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation512_zero : nativeImage "20,1,194,1;13,1,232,1" = 0 := by
  change projection (relationPolynomial "20,1,194,1;13,1,232,1") = 0
  exact csv_relation_zero _ relation512_mem
theorem relation513_mem : "13,1,232,1;8,1,9,1,167,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block24[24]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation513_zero : nativeImage "13,1,232,1;8,1,9,1,167,1" = 0 := by
  change projection (relationPolynomial "13,1,232,1;8,1,9,1,167,1") = 0
  exact csv_relation_zero _ relation513_mem
theorem relation514_mem : "17,1,208,1;8,2,180,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block25[1]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation514_zero : nativeImage "17,1,208,1;8,2,180,1" = 0 := by
  change projection (relationPolynomial "17,1,208,1;8,2,180,1") = 0
  exact csv_relation_zero _ relation514_mem
theorem relation515_mem : "17,1,207,1;9,1,247,1;9,1,246,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block25[9]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation515_zero : nativeImage "17,1,207,1;9,1,247,1;9,1,246,1" = 0 := by
  change projection (relationPolynomial "17,1,207,1;9,1,247,1;9,1,246,1") = 0
  exact csv_relation_zero _ relation515_mem
theorem relation516_mem : "9,1,247,1;8,1,259,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block25[10]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation516_zero : nativeImage "9,1,247,1;8,1,259,1" = 0 := by
  change projection (relationPolynomial "9,1,247,1;8,1,259,1") = 0
  exact csv_relation_zero _ relation516_mem
theorem relation517_mem : "9,1,246,1;0,3,380,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block25[11]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation517_zero : nativeImage "9,1,246,1;0,3,380,1" = 0 := by
  change projection (relationPolynomial "9,1,246,1;0,3,380,1") = 0
  exact csv_relation_zero _ relation517_mem
theorem relation518_mem : "39,1,149,1;31,1,160,1;27,1,172,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block25[23]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation518_zero : nativeImage "39,1,149,1;31,1,160,1;27,1,172,1" = 0 := by
  change projection (relationPolynomial "39,1,149,1;31,1,160,1;27,1,172,1") = 0
  exact csv_relation_zero _ relation518_mem
theorem relation519_mem : "31,1,160,1;16,1,206,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block25[24]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation519_zero : nativeImage "31,1,160,1;16,1,206,1" = 0 := by
  change projection (relationPolynomial "31,1,160,1;16,1,206,1") = 0
  exact csv_relation_zero _ relation519_mem
theorem relation520_mem : "16,1,206,1;8,1,257,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block25[26]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation520_zero : nativeImage "16,1,206,1;8,1,257,1" = 0 := by
  change projection (relationPolynomial "16,1,206,1;8,1,257,1") = 0
  exact csv_relation_zero _ relation520_mem
theorem relation521_mem : "24,1,189,1;7,1,279,1" ∈ LinE2.RawData.relations := by
  exact relation_member 9 chunkBound rows transcription
    (block30[30]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation521_zero : nativeImage "24,1,189,1;7,1,279,1" = 0 := by
  change projection (relationPolynomial "24,1,189,1;7,1,279,1") = 0
  exact csv_relation_zero _ relation521_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk009
