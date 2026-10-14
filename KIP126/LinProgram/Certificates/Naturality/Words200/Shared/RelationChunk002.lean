module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk002
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[2]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 2 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[2]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
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
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
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
private theorem block14_mem : block14 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 14) (by decide)
private theorem block14_in_rows (r : List Char) (hr : r ∈ block14) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block14, block14_mem, hr⟩
private theorem block20_mem : block20 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 20) (by decide)
private theorem block20_in_rows (r : List Char) (hr : r ∈ block20) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block20, block20_mem, hr⟩
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
private theorem block26_mem : block26 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 26) (by decide)
private theorem block26_in_rows (r : List Char) (hr : r ∈ block26) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block26, block26_mem, hr⟩
private theorem block29_mem : block29 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 29) (by decide)
private theorem block29_in_rows (r : List Char) (hr : r ∈ block29) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block29, block29_mem, hr⟩
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation211_mem : "1,1,8,1,88,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block1[8]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation211_zero : nativeImage "1,1,8,1,88,1" = 0 := by
  change projection (relationPolynomial "1,1,8,1,88,1") = 0
  exact csv_relation_zero _ relation211_mem
theorem relation212_mem : "7,1,109,1;1,1,148,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block2[4]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation212_zero : nativeImage "7,1,109,1;1,1,148,1" = 0 := by
  change projection (relationPolynomial "7,1,109,1;1,1,148,1") = 0
  exact csv_relation_zero _ relation212_mem
theorem relation213_mem : "2,2,134,1;1,1,13,1,76,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block2[18]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation213_zero : nativeImage "2,2,134,1;1,1,13,1,76,1" = 0 := by
  change projection (relationPolynomial "2,2,134,1;1,1,13,1,76,1") = 0
  exact csv_relation_zero _ relation213_mem
theorem relation214_mem : "13,1,79,1;9,1,90,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block3[5]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation214_zero : nativeImage "13,1,79,1;9,1,90,1" = 0 := by
  change projection (relationPolynomial "13,1,79,1;9,1,90,1") = 0
  exact csv_relation_zero _ relation214_mem
theorem relation215_mem : "9,1,90,1;9,1,89,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block3[6]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation215_zero : nativeImage "9,1,90,1;9,1,89,1" = 0 := by
  change projection (relationPolynomial "9,1,90,1;9,1,89,1") = 0
  exact csv_relation_zero _ relation215_mem
theorem relation216_mem : "9,1,89,1;8,1,101,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block3[7]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation216_zero : nativeImage "9,1,89,1;8,1,101,1" = 0 := by
  change projection (relationPolynomial "9,1,89,1;8,1,101,1") = 0
  exact csv_relation_zero _ relation216_mem
theorem relation217_mem : "0,1,150,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block3[9]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation217_zero : nativeImage "0,1,150,1" = 0 := by
  change projection (relationPolynomial "0,1,150,1") = 0
  exact csv_relation_zero _ relation217_mem
theorem relation218_mem : "17,1,63,1;8,4,9,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block4[4]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation218_zero : nativeImage "17,1,63,1;8,4,9,1" = 0 := by
  change projection (relationPolynomial "17,1,63,1;8,4,9,1") = 0
  exact csv_relation_zero _ relation218_mem
theorem relation219_mem : "0,3,147,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block4[5]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation219_zero : nativeImage "0,3,147,1" = 0 := by
  change projection (relationPolynomial "0,3,147,1") = 0
  exact csv_relation_zero _ relation219_mem
theorem relation220_mem : "17,2,20,1;9,1,88,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block4[12]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation220_zero : nativeImage "17,2,20,1;9,1,88,1" = 0 := by
  change projection (relationPolynomial "17,2,20,1;9,1,88,1") = 0
  exact csv_relation_zero _ relation220_mem
theorem relation221_mem : "9,1,88,1;8,1,100,1;0,3,146,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block4[14]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation221_zero : nativeImage "9,1,88,1;8,1,100,1;0,3,146,1" = 0 := by
  change projection (relationPolynomial "9,1,88,1;8,1,100,1;0,3,146,1") = 0
  exact csv_relation_zero _ relation221_mem
theorem relation222_mem : "1,1,16,1,64,1;0,2,17,1,64,1;0,3,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block9[16]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation222_zero : nativeImage "1,1,16,1,64,1;0,2,17,1,64,1;0,3,149,1" = 0 := by
  change projection (relationPolynomial "1,1,16,1,64,1;0,2,17,1,64,1;0,3,149,1") = 0
  exact csv_relation_zero _ relation222_mem
theorem relation223_mem : "18,1,69,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block10[12]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation223_zero : nativeImage "18,1,69,1" = 0 := by
  change projection (relationPolynomial "18,1,69,1") = 0
  exact csv_relation_zero _ relation223_mem
theorem relation224_mem : "18,1,66,1;5,1,122,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block10[28]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation224_zero : nativeImage "18,1,66,1;5,1,122,1" = 0 := by
  change projection (relationPolynomial "18,1,66,1;5,1,122,1") = 0
  exact csv_relation_zero _ relation224_mem
theorem relation225_mem : "5,1,122,1;1,1,157,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block10[31]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation225_zero : nativeImage "5,1,122,1;1,1,157,1" = 0 := by
  change projection (relationPolynomial "5,1,122,1;1,1,157,1") = 0
  exact csv_relation_zero _ relation225_mem
theorem relation226_mem : "13,1,89,1;9,1,101,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block11[16]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation226_zero : nativeImage "13,1,89,1;9,1,101,1" = 0 := by
  change projection (relationPolynomial "13,1,89,1;9,1,101,1") = 0
  exact csv_relation_zero _ relation226_mem
theorem relation227_mem : "17,1,72,1;8,1,113,1;2,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block11[29]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation227_zero : nativeImage "17,1,72,1;8,1,113,1;2,1,149,1" = 0 := by
  change projection (relationPolynomial "17,1,72,1;8,1,113,1;2,1,149,1") = 0
  exact csv_relation_zero _ relation227_mem
theorem relation228_mem : "2,1,149,1;0,1,160,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block11[30]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation228_zero : nativeImage "2,1,149,1;0,1,160,1" = 0 := by
  change projection (relationPolynomial "2,1,149,1;0,1,160,1") = 0
  exact csv_relation_zero _ relation228_mem
theorem relation229_mem : "19,1,64,1;16,1,72,1;14,1,81,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block12[1]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation229_zero : nativeImage "19,1,64,1;16,1,72,1;14,1,81,1" = 0 := by
  change projection (relationPolynomial "19,1,64,1;16,1,72,1;14,1,81,1") = 0
  exact csv_relation_zero _ relation229_mem
theorem relation230_mem : "16,1,72,1;8,1,112,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block12[2]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation230_zero : nativeImage "16,1,72,1;8,1,112,1" = 0 := by
  change projection (relationPolynomial "16,1,72,1;8,1,112,1") = 0
  exact csv_relation_zero _ relation230_mem
theorem relation231_mem : "0,3,17,1,64,1;0,4,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block12[18]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation231_zero : nativeImage "0,3,17,1,64,1;0,4,149,1" = 0 := by
  change projection (relationPolynomial "0,3,17,1,64,1;0,4,149,1") = 0
  exact csv_relation_zero _ relation231_mem
theorem relation232_mem : "17,1,71,1;8,1,111,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block13[7]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation232_zero : nativeImage "17,1,71,1;8,1,111,1" = 0 := by
  change projection (relationPolynomial "17,1,71,1;8,1,111,1") = 0
  exact csv_relation_zero _ relation232_mem
theorem relation233_mem : "1,1,160,1;0,1,162,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block14[29]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation233_zero : nativeImage "1,1,160,1;0,1,162,1" = 0 := by
  change projection (relationPolynomial "1,1,160,1;0,1,162,1") = 0
  exact csv_relation_zero _ relation233_mem
theorem relation234_mem : "17,1,79,1;16,1,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block20[27]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation234_zero : nativeImage "17,1,79,1;16,1,80,1" = 0 := by
  change projection (relationPolynomial "17,1,79,1;16,1,80,1") = 0
  exact csv_relation_zero _ relation234_mem
theorem relation235_mem : "16,1,80,1;8,1,118,1;2,1,160,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block21[0]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation235_zero : nativeImage "16,1,80,1;8,1,118,1;2,1,160,1" = 0 := by
  change projection (relationPolynomial "16,1,80,1;8,1,118,1;2,1,160,1") = 0
  exact csv_relation_zero _ relation235_mem
theorem relation236_mem : "2,1,160,1;0,1,166,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block21[1]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation236_zero : nativeImage "2,1,160,1;0,1,166,1" = 0 := by
  change projection (relationPolynomial "2,1,160,1;0,1,166,1") = 0
  exact csv_relation_zero _ relation236_mem
theorem relation237_mem : "0,6,154,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block21[27]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation237_zero : nativeImage "0,6,154,1" = 0 := by
  change projection (relationPolynomial "0,6,154,1") = 0
  exact csv_relation_zero _ relation237_mem
theorem relation238_mem : "0,7,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block21[29]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation238_zero : nativeImage "0,7,149,1" = 0 := by
  change projection (relationPolynomial "0,7,149,1") = 0
  exact csv_relation_zero _ relation238_mem
theorem relation239_mem : "17,1,77,1;16,1,78,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block22[4]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation239_zero : nativeImage "17,1,77,1;16,1,78,1" = 0 := by
  change projection (relationPolynomial "17,1,77,1;16,1,78,1") = 0
  exact csv_relation_zero _ relation239_mem
theorem relation240_mem : "16,1,78,1;9,1,111,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block22[5]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation240_zero : nativeImage "16,1,78,1;9,1,111,1" = 0 := by
  change projection (relationPolynomial "16,1,78,1;9,1,111,1") = 0
  exact csv_relation_zero _ relation240_mem
theorem relation241_mem : "9,1,111,1;8,1,117,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block22[6]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation241_zero : nativeImage "9,1,111,1;8,1,117,1" = 0 := by
  change projection (relationPolynomial "9,1,111,1;8,1,117,1") = 0
  exact csv_relation_zero _ relation241_mem
theorem relation242_mem : "9,1,110,1;8,1,116,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block22[11]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation242_zero : nativeImage "9,1,110,1;8,1,116,1" = 0 := by
  change projection (relationPolynomial "9,1,110,1;8,1,116,1") = 0
  exact csv_relation_zero _ relation242_mem
theorem relation243_mem : "23,1,68,1;13,1,107,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block23[10]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation243_zero : nativeImage "23,1,68,1;13,1,107,1" = 0 := by
  change projection (relationPolynomial "23,1,68,1;13,1,107,1") = 0
  exact csv_relation_zero _ relation243_mem
theorem relation244_mem : "23,1,67,1;13,1,105,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block23[22]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation244_zero : nativeImage "23,1,67,1;13,1,105,1" = 0 := by
  change projection (relationPolynomial "23,1,67,1;13,1,105,1") = 0
  exact csv_relation_zero _ relation244_mem
theorem relation245_mem : "2,2,151,1;1,1,169,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block24[12]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation245_zero : nativeImage "2,2,151,1;1,1,169,1" = 0 := by
  change projection (relationPolynomial "2,2,151,1;1,1,169,1") = 0
  exact csv_relation_zero _ relation245_mem
theorem relation246_mem : "2,2,150,1;1,1,168,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block24[24]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation246_zero : nativeImage "2,2,150,1;1,1,168,1" = 0 := by
  change projection (relationPolynomial "2,2,150,1;1,1,168,1") = 0
  exact csv_relation_zero _ relation246_mem
theorem relation247_mem : "24,1,70,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block26[15]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation247_zero : nativeImage "24,1,70,1" = 0 := by
  change projection (relationPolynomial "24,1,70,1") = 0
  exact csv_relation_zero _ relation247_mem
theorem relation248_mem : "0,1,181,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block29[12]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation248_zero : nativeImage "0,1,181,1" = 0 := by
  change projection (relationPolynomial "0,1,181,1") = 0
  exact csv_relation_zero _ relation248_mem
theorem relation249_mem : "2,1,168,1;1,1,176,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block30[18]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation249_zero : nativeImage "2,1,168,1;1,1,176,1" = 0 := by
  change projection (relationPolynomial "2,1,168,1;1,1,176,1") = 0
  exact csv_relation_zero _ relation249_mem
theorem relation250_mem : "17,1,89,1;8,1,127,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block31[8]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation250_zero : nativeImage "17,1,89,1;8,1,127,1" = 0 := by
  change projection (relationPolynomial "17,1,89,1;8,1,127,1") = 0
  exact csv_relation_zero _ relation250_mem
theorem relation251_mem : "13,1,112,1;8,2,72,1" ∈ LinE2.RawData.relations := by
  exact relation_member 2 chunkBound rows transcription
    (block31[23]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation251_zero : nativeImage "13,1,112,1;8,2,72,1" = 0 := by
  change projection (relationPolynomial "13,1,112,1;8,2,72,1") = 0
  exact csv_relation_zero _ relation251_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk002
