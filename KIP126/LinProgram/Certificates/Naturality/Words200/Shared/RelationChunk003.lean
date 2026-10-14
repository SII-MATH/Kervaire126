module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk003
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[3]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 3 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[3]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block1_mem : block1 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 1) (by decide)
private theorem block1_in_rows (r : List Char) (hr : r ∈ block1) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block1, block1_mem, hr⟩
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
private theorem block10_mem : block10 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 10) (by decide)
private theorem block10_in_rows (r : List Char) (hr : r ∈ block10) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block10, block10_mem, hr⟩
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
private theorem block13_mem : block13 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 13) (by decide)
private theorem block13_in_rows (r : List Char) (hr : r ∈ block13) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block13, block13_mem, hr⟩
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
private theorem block24_mem : block24 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 24) (by decide)
private theorem block24_in_rows (r : List Char) (hr : r ∈ block24) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block24, block24_mem, hr⟩
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block26_mem : block26 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 26) (by decide)
private theorem block26_in_rows (r : List Char) (hr : r ∈ block26) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block26, block26_mem, hr⟩
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation252_mem : "17,1,88,1;8,4,16,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block0[11]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation252_zero : nativeImage "17,1,88,1;8,4,16,1" = 0 := by
  change projection (relationPolynomial "17,1,88,1;8,4,16,1") = 0
  exact csv_relation_zero _ relation252_mem
theorem relation253_mem : "42,1,49,1;31,1,60,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block0[12]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation253_zero : nativeImage "42,1,49,1;31,1,60,1" = 0 := by
  change projection (relationPolynomial "42,1,49,1;31,1,60,1") = 0
  exact csv_relation_zero _ relation253_mem
theorem relation254_mem : "31,1,60,1;16,1,88,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block0[15]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation254_zero : nativeImage "31,1,60,1;16,1,88,1" = 0 := by
  change projection (relationPolynomial "31,1,60,1;16,1,88,1") = 0
  exact csv_relation_zero _ relation254_mem
theorem relation255_mem : "16,1,88,1;8,1,125,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block0[16]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation255_zero : nativeImage "16,1,88,1;8,1,125,1" = 0 := by
  change projection (relationPolynomial "16,1,88,1;8,1,125,1") = 0
  exact csv_relation_zero _ relation255_mem
theorem relation256_mem : "2,1,174,1;1,1,181,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block1[12]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation256_zero : nativeImage "2,1,174,1;1,1,181,1" = 0 := by
  change projection (relationPolynomial "2,1,174,1;1,1,181,1") = 0
  exact csv_relation_zero _ relation256_mem
theorem relation257_mem : "24,1,76,1;7,1,139,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block1[17]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation257_zero : nativeImage "24,1,76,1;7,1,139,1" = 0 := by
  change projection (relationPolynomial "24,1,76,1;7,1,139,1") = 0
  exact csv_relation_zero _ relation257_mem
theorem relation258_mem : "7,1,139,1;1,2,174,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block1[18]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation258_zero : nativeImage "7,1,139,1;1,2,174,1" = 0 := by
  change projection (relationPolynomial "7,1,139,1;1,2,174,1") = 0
  exact csv_relation_zero _ relation258_mem
theorem relation259_mem : "0,2,8,2,72,1;0,5,172,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block6[19]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation259_zero : nativeImage "0,2,8,2,72,1;0,5,172,1" = 0 := by
  change projection (relationPolynomial "0,2,8,2,72,1;0,5,172,1") = 0
  exact csv_relation_zero _ relation259_mem
theorem relation260_mem : "1,1,185,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block6[24]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation260_zero : nativeImage "1,1,185,1" = 0 := by
  change projection (relationPolynomial "1,1,185,1") = 0
  exact csv_relation_zero _ relation260_mem
theorem relation261_mem : "1,1,8,1,125,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block7[4]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation261_zero : nativeImage "1,1,8,1,125,1" = 0 := by
  change projection (relationPolynomial "1,1,8,1,125,1") = 0
  exact csv_relation_zero _ relation261_mem
theorem relation262_mem : "3,1,164,1;1,1,192,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block8[19]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation262_zero : nativeImage "3,1,164,1;1,1,192,1" = 0 := by
  change projection (relationPolynomial "3,1,164,1;1,1,192,1") = 0
  exact csv_relation_zero _ relation262_mem
theorem relation263_mem : "0,3,190,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block8[21]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation263_zero : nativeImage "0,3,190,1" = 0 := by
  change projection (relationPolynomial "0,3,190,1") = 0
  exact csv_relation_zero _ relation263_mem
theorem relation264_mem : "0,3,189,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block9[4]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation264_zero : nativeImage "0,3,189,1" = 0 := by
  change projection (relationPolynomial "0,3,189,1") = 0
  exact csv_relation_zero _ relation264_mem
theorem relation265_mem : "22,1,79,1;20,1,90,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block9[26]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation265_zero : nativeImage "22,1,79,1;20,1,90,1" = 0 := by
  change projection (relationPolynomial "22,1,79,1;20,1,90,1") = 0
  exact csv_relation_zero _ relation265_mem
theorem relation266_mem : "20,1,90,1;20,1,89,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block9[27]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation266_zero : nativeImage "20,1,90,1;20,1,89,1" = 0 := by
  change projection (relationPolynomial "20,1,90,1;20,1,89,1") = 0
  exact csv_relation_zero _ relation266_mem
theorem relation267_mem : "20,1,89,1;17,1,101,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block9[28]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation267_zero : nativeImage "20,1,89,1;17,1,101,1" = 0 := by
  change projection (relationPolynomial "20,1,89,1;17,1,101,1") = 0
  exact csv_relation_zero _ relation267_mem
theorem relation268_mem : "17,1,101,1;13,1,118,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block9[30]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation268_zero : nativeImage "17,1,101,1;13,1,118,1" = 0 := by
  change projection (relationPolynomial "17,1,101,1;13,1,118,1") = 0
  exact csv_relation_zero _ relation268_mem
theorem relation269_mem : "13,1,118,1;9,1,127,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block9[31]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation269_zero : nativeImage "13,1,118,1;9,1,127,1" = 0 := by
  change projection (relationPolynomial "13,1,118,1;9,1,127,1") = 0
  exact csv_relation_zero _ relation269_mem
theorem relation270_mem : "9,1,127,1;8,2,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block10[1]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation270_zero : nativeImage "9,1,127,1;8,2,80,1" = 0 := by
  change projection (relationPolynomial "9,1,127,1;8,2,80,1") = 0
  exact csv_relation_zero _ relation270_mem
theorem relation271_mem : "31,1,64,1;8,1,137,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block10[31]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation271_zero : nativeImage "31,1,64,1;8,1,137,1" = 0 := by
  change projection (relationPolynomial "31,1,64,1;8,1,137,1") = 0
  exact csv_relation_zero _ relation271_mem
theorem relation272_mem : "17,1,100,1;8,4,19,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block11[10]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation272_zero : nativeImage "17,1,100,1;8,4,19,1" = 0 := by
  change projection (relationPolynomial "17,1,100,1;8,4,19,1") = 0
  exact csv_relation_zero _ relation272_mem
theorem relation273_mem : "0,3,185,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block11[11]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation273_zero : nativeImage "0,3,185,1" = 0 := by
  change projection (relationPolynomial "0,3,185,1") = 0
  exact csv_relation_zero _ relation273_mem
theorem relation274_mem : "17,2,40,1;9,1,125,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block11[21]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation274_zero : nativeImage "17,2,40,1;9,1,125,1" = 0 := by
  change projection (relationPolynomial "17,2,40,1;9,1,125,1") = 0
  exact csv_relation_zero _ relation274_mem
theorem relation275_mem : "9,1,125,1;8,1,136,1;0,3,184,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block11[23]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation275_zero : nativeImage "9,1,125,1;8,1,136,1;0,3,184,1" = 0 := by
  change projection (relationPolynomial "9,1,125,1;8,1,136,1;0,3,184,1") = 0
  exact csv_relation_zero _ relation275_mem
theorem relation276_mem : "23,1,85,1;9,1,133,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block13[23]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation276_zero : nativeImage "23,1,85,1;9,1,133,1" = 0 := by
  change projection (relationPolynomial "23,1,85,1;9,1,133,1") = 0
  exact csv_relation_zero _ relation276_mem
theorem relation277_mem : "36,1,68,1;3,1,178,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block21[23]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation277_zero : nativeImage "36,1,68,1;3,1,178,1" = 0 := by
  change projection (relationPolynomial "36,1,68,1;3,1,178,1") = 0
  exact csv_relation_zero _ relation277_mem
theorem relation278_mem : "29,1,80,1;23,1,90,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block22[26]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation278_zero : nativeImage "29,1,80,1;23,1,90,1" = 0 := by
  change projection (relationPolynomial "29,1,80,1;23,1,90,1") = 0
  exact csv_relation_zero _ relation278_mem
theorem relation279_mem : "20,1,101,1;13,1,127,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block23[4]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation279_zero : nativeImage "20,1,101,1;13,1,127,1" = 0 := by
  change projection (relationPolynomial "20,1,101,1;13,1,127,1") = 0
  exact csv_relation_zero _ relation279_mem
theorem relation280_mem : "13,1,127,1;8,1,9,1,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block23[7]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation280_zero : nativeImage "13,1,127,1;8,1,9,1,80,1" = 0 := by
  change projection (relationPolynomial "13,1,127,1;8,1,9,1,80,1") = 0
  exact csv_relation_zero _ relation280_mem
theorem relation281_mem : "17,1,112,1;8,1,147,1;6,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block23[31]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation281_zero : nativeImage "17,1,112,1;8,1,147,1;6,1,149,1" = 0 := by
  change projection (relationPolynomial "17,1,112,1;8,1,147,1;6,1,149,1") = 0
  exact csv_relation_zero _ relation281_mem
theorem relation282_mem : "6,1,149,1;0,1,206,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block24[0]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation282_zero : nativeImage "6,1,149,1;0,1,206,1" = 0 := by
  change projection (relationPolynomial "6,1,149,1;0,1,206,1") = 0
  exact csv_relation_zero _ relation282_mem
theorem relation283_mem : "9,1,137,1;8,1,146,1;1,1,5,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block24[9]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation283_zero : nativeImage "9,1,137,1;8,1,146,1;1,1,5,1,149,1" = 0 := by
  change projection (relationPolynomial "9,1,137,1;8,1,146,1;1,1,5,1,149,1") = 0
  exact csv_relation_zero _ relation283_mem
theorem relation284_mem : "17,1,110,1;16,1,111,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block25[8]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation284_zero : nativeImage "17,1,110,1;16,1,111,1" = 0 := by
  change projection (relationPolynomial "17,1,110,1;16,1,111,1") = 0
  exact csv_relation_zero _ relation284_mem
theorem relation285_mem : "0,1,213,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block26[7]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation285_zero : nativeImage "0,1,213,1" = 0 := by
  change projection (relationPolynomial "0,1,213,1") = 0
  exact csv_relation_zero _ relation285_mem
theorem relation286_mem : "24,1,95,1;13,1,134,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block26[19]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation286_zero : nativeImage "24,1,95,1;13,1,134,1" = 0 := by
  change projection (relationPolynomial "24,1,95,1;13,1,134,1") = 0
  exact csv_relation_zero _ relation286_mem
theorem relation287_mem : "23,1,95,1;13,1,133,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block26[27]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation287_zero : nativeImage "23,1,95,1;13,1,133,1" = 0 := by
  change projection (relationPolynomial "23,1,95,1;13,1,133,1") = 0
  exact csv_relation_zero _ relation287_mem
theorem relation288_mem : "2,1,203,1;1,1,214,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block30[9]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation288_zero : nativeImage "2,1,203,1;1,1,214,1" = 0 := by
  change projection (relationPolynomial "2,1,203,1;1,1,214,1") = 0
  exact csv_relation_zero _ relation288_mem
theorem relation289_mem : "2,2,191,1;1,2,203,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block30[13]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation289_zero : nativeImage "2,2,191,1;1,2,203,1" = 0 := by
  change projection (relationPolynomial "2,2,191,1;1,2,203,1") = 0
  exact csv_relation_zero _ relation289_mem
theorem relation290_mem : "2,2,188,1;1,1,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 3 chunkBound rows transcription
    (block31[0]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation290_zero : nativeImage "2,2,188,1;1,1,212,1" = 0 := by
  change projection (relationPolynomial "2,2,188,1;1,1,212,1") = 0
  exact csv_relation_zero _ relation290_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk003
