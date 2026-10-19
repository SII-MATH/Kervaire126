module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk007
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[7]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 7 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[7]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block1_mem : block1 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 1) (by decide)
private theorem block1_in_rows (r : List Char) (hr : r ∈ block1) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block1, block1_mem, hr⟩
private theorem block2_mem : block2 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 2) (by decide)
private theorem block2_in_rows (r : List Char) (hr : r ∈ block2) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block2, block2_mem, hr⟩
private theorem block8_mem : block8 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 8) (by decide)
private theorem block8_in_rows (r : List Char) (hr : r ∈ block8) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block8, block8_mem, hr⟩
private theorem block10_mem : block10 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 10) (by decide)
private theorem block10_in_rows (r : List Char) (hr : r ∈ block10) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block10, block10_mem, hr⟩
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
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
private theorem block18_mem : block18 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 18) (by decide)
private theorem block18_in_rows (r : List Char) (hr : r ∈ block18) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block18, block18_mem, hr⟩
private theorem block19_mem : block19 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 19) (by decide)
private theorem block19_in_rows (r : List Char) (hr : r ∈ block19) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block19, block19_mem, hr⟩
private theorem block20_mem : block20 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 20) (by decide)
private theorem block20_in_rows (r : List Char) (hr : r ∈ block20) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block20, block20_mem, hr⟩
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
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation407_mem : "17,1,20,1,69,1;4,1,250,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block1[28]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation407_zero : nativeImage "17,1,20,1,69,1;4,1,250,1" = 0 := by
  change projection (relationPolynomial "17,1,20,1,69,1;4,1,250,1") = 0
  exact csv_relation_zero _ relation407_mem
theorem relation408_mem : "4,1,250,1;1,1,8,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block1[29]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation408_zero : nativeImage "4,1,250,1;1,1,8,1,209,1" = 0 := by
  change projection (relationPolynomial "4,1,250,1;1,1,8,1,209,1") = 0
  exact csv_relation_zero _ relation408_mem
theorem relation409_mem : "0,2,8,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block2[10]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation409_zero : nativeImage "0,2,8,1,209,1" = 0 := by
  change projection (relationPolynomial "0,2,8,1,209,1") = 0
  exact csv_relation_zero _ relation409_mem
theorem relation410_mem : "64,1,67,1;53,1,90,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block2[11]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation410_zero : nativeImage "64,1,67,1;53,1,90,1" = 0 := by
  change projection (relationPolynomial "64,1,67,1;53,1,90,1") = 0
  exact csv_relation_zero _ relation410_mem
theorem relation411_mem : "0,1,303,1;0,1,302,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block2[25]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation411_zero : nativeImage "0,1,303,1;0,1,302,1" = 0 := by
  change projection (relationPolynomial "0,1,303,1;0,1,302,1") = 0
  exact csv_relation_zero _ relation411_mem
theorem relation412_mem : "0,1,302,1;0,3,59,1,69,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block2[27]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation412_zero : nativeImage "0,1,302,1;0,3,59,1,69,1" = 0 := by
  change projection (relationPolynomial "0,1,302,1;0,3,59,1,69,1") = 0
  exact csv_relation_zero _ relation412_mem
theorem relation413_mem : "8,1,221,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block8[10]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation413_zero : nativeImage "8,1,221,1" = 0 := by
  change projection (relationPolynomial "8,1,221,1") = 0
  exact csv_relation_zero _ relation413_mem
theorem relation414_mem : "2,2,268,1;1,1,13,1,189,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block8[18]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation414_zero : nativeImage "2,2,268,1;1,1,13,1,189,1" = 0 := by
  change projection (relationPolynomial "2,2,268,1;1,1,13,1,189,1") = 0
  exact csv_relation_zero _ relation414_mem
theorem relation415_mem : "9,1,208,1;8,1,219,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block10[17]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation415_zero : nativeImage "9,1,208,1;8,1,219,1" = 0 := by
  change projection (relationPolynomial "9,1,208,1;8,1,219,1") = 0
  exact csv_relation_zero _ relation415_mem
theorem relation416_mem : "17,1,167,1;8,1,218,1;0,2,64,2" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block10[24]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation416_zero : nativeImage "17,1,167,1;8,1,218,1;0,2,64,2" = 0 := by
  change projection (relationPolynomial "17,1,167,1;8,1,218,1;0,2,64,2") = 0
  exact csv_relation_zero _ relation416_mem
theorem relation417_mem : "17,1,166,1;16,1,167,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block11[0]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation417_zero : nativeImage "17,1,166,1;16,1,167,1" = 0 := by
  change projection (relationPolynomial "17,1,166,1;16,1,167,1") = 0
  exact csv_relation_zero _ relation417_mem
theorem relation418_mem : "0,2,8,2,146,1;0,5,17,1,154,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block11[29]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation418_zero : nativeImage "0,2,8,2,146,1;0,5,17,1,154,1" = 0 := by
  change projection (relationPolynomial "0,2,8,2,146,1;0,5,17,1,154,1") = 0
  exact csv_relation_zero _ relation418_mem
theorem relation419_mem : "13,1,201,1;9,1,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block15[23]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation419_zero : nativeImage "13,1,201,1;9,1,212,1" = 0 := by
  change projection (relationPolynomial "13,1,201,1;9,1,212,1") = 0
  exact csv_relation_zero _ relation419_mem
theorem relation420_mem : "51,1,101,1;13,1,23,1,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block16[20]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation420_zero : nativeImage "51,1,101,1;13,1,23,1,80,1" = 0 := by
  change projection (relationPolynomial "51,1,101,1;13,1,23,1,80,1") = 0
  exact csv_relation_zero _ relation420_mem
theorem relation421_mem : "8,1,226,1;2,1,291,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block16[22]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation421_zero : nativeImage "8,1,226,1;2,1,291,1" = 0 := by
  change projection (relationPolynomial "8,1,226,1;2,1,291,1") = 0
  exact csv_relation_zero _ relation421_mem
theorem relation422_mem : "0,5,59,1,69,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block16[24]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation422_zero : nativeImage "0,5,59,1,69,1" = 0 := by
  change projection (relationPolynomial "0,5,59,1,69,1") = 0
  exact csv_relation_zero _ relation422_mem
theorem relation423_mem : "17,1,173,1;17,1,172,1;8,3,101,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block17[25]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation423_zero : nativeImage "17,1,173,1;17,1,172,1;8,3,101,1" = 0 := by
  change projection (relationPolynomial "17,1,173,1;17,1,172,1;8,3,101,1") = 0
  exact csv_relation_zero _ relation423_mem
theorem relation424_mem : "17,1,172,1;0,3,299,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block17[26]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation424_zero : nativeImage "17,1,172,1;0,3,299,1" = 0 := by
  change projection (relationPolynomial "17,1,172,1;0,3,299,1") = 0
  exact csv_relation_zero _ relation424_mem
theorem relation425_mem : "17,2,80,1;8,1,42,1,64,1;0,3,64,2" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block18[10]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation425_zero : nativeImage "17,2,80,1;8,1,42,1,64,1;0,3,64,2" = 0 := by
  change projection (relationPolynomial "17,2,80,1;8,1,42,1,64,1;0,3,64,2") = 0
  exact csv_relation_zero _ relation425_mem
theorem relation426_mem : "0,1,8,2,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block19[5]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation426_zero : nativeImage "0,1,8,2,149,1" = 0 := by
  change projection (relationPolynomial "0,1,8,2,149,1") = 0
  exact csv_relation_zero _ relation426_mem
theorem relation427_mem : "31,1,138,1;8,1,225,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block19[28]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation427_zero : nativeImage "31,1,138,1;8,1,225,1" = 0 := by
  change projection (relationPolynomial "31,1,138,1;8,1,225,1") = 0
  exact csv_relation_zero _ relation427_mem
theorem relation428_mem : "17,1,171,1;8,4,55,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block20[12]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation428_zero : nativeImage "17,1,171,1;8,4,55,1" = 0 := by
  change projection (relationPolynomial "17,1,171,1;8,4,55,1") = 0
  exact csv_relation_zero _ relation428_mem
theorem relation429_mem : "17,2,78,1;9,1,211,1;9,1,210,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block20[28]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation429_zero : nativeImage "17,2,78,1;9,1,211,1;9,1,210,1" = 0 := by
  change projection (relationPolynomial "17,2,78,1;9,1,211,1;9,1,210,1") = 0
  exact csv_relation_zero _ relation429_mem
theorem relation430_mem : "9,1,211,1;8,1,223,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block20[29]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation430_zero : nativeImage "9,1,211,1;8,1,223,1" = 0 := by
  change projection (relationPolynomial "9,1,211,1;8,1,223,1") = 0
  exact csv_relation_zero _ relation430_mem
theorem relation431_mem : "9,1,210,1;0,3,297,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block20[30]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation431_zero : nativeImage "9,1,210,1;0,3,297,1" = 0 := by
  change projection (relationPolynomial "9,1,210,1;0,3,297,1") = 0
  exact csv_relation_zero _ relation431_mem
theorem relation432_mem : "16,1,23,1,69,1;8,1,229,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block23[23]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation432_zero : nativeImage "16,1,23,1,69,1;8,1,229,1" = 0 := by
  change projection (relationPolynomial "16,1,23,1,69,1;8,1,229,1") = 0
  exact csv_relation_zero _ relation432_mem
theorem relation433_mem : "8,1,229,1;4,1,261,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block23[24]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation433_zero : nativeImage "8,1,229,1;4,1,261,1" = 0 := by
  change projection (relationPolynomial "8,1,229,1;4,1,261,1") = 0
  exact csv_relation_zero _ relation433_mem
theorem relation434_mem : "4,1,261,1;3,1,279,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block23[25]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation434_zero : nativeImage "4,1,261,1;3,1,279,1" = 0 := by
  change projection (relationPolynomial "4,1,261,1;3,1,279,1") = 0
  exact csv_relation_zero _ relation434_mem
theorem relation435_mem : "3,1,279,1;1,2,308,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block23[27]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation435_zero : nativeImage "3,1,279,1;1,2,308,1" = 0 := by
  change projection (relationPolynomial "3,1,279,1;1,2,308,1") = 0
  exact csv_relation_zero _ relation435_mem
theorem relation436_mem : "67,1,72,1;5,1,250,1;2,1,303,1;2,1,302,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block24[31]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation436_zero : nativeImage "67,1,72,1;5,1,250,1;2,1,303,1;2,1,302,1" = 0 := by
  change projection (relationPolynomial "67,1,72,1;5,1,250,1;2,1,303,1;2,1,302,1") = 0
  exact csv_relation_zero _ relation436_mem
theorem relation437_mem : "2,1,303,1;2,1,302,1;0,2,3,1,267,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block25[2]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation437_zero : nativeImage "2,1,303,1;2,1,302,1;0,2,3,1,267,1" = 0 := by
  change projection (relationPolynomial "2,1,303,1;2,1,302,1;0,2,3,1,267,1") = 0
  exact csv_relation_zero _ relation437_mem
theorem relation438_mem : "69,1,73,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block30[5]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation438_zero : nativeImage "69,1,73,1" = 0 := by
  change projection (relationPolynomial "69,1,73,1") = 0
  exact csv_relation_zero _ relation438_mem
theorem relation439_mem : "68,1,75,1;68,1,74,1;67,1,76,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block30[22]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation439_zero : nativeImage "68,1,75,1;68,1,74,1;67,1,76,1" = 0 := by
  change projection (relationPolynomial "68,1,75,1;68,1,74,1;67,1,76,1") = 0
  exact csv_relation_zero _ relation439_mem
theorem relation440_mem : "68,1,74,1;0,1,336,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block30[28]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation440_zero : nativeImage "68,1,74,1;0,1,336,1" = 0 := by
  change projection (relationPolynomial "68,1,74,1;0,1,336,1") = 0
  exact csv_relation_zero _ relation440_mem
theorem relation441_mem : "8,1,235,1;4,1,269,1" ∈ LinE2.RawData.relations := by
  exact relation_member 7 chunkBound rows transcription
    (block31[0]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation441_zero : nativeImage "8,1,235,1;4,1,269,1" = 0 := by
  change projection (relationPolynomial "8,1,235,1;4,1,269,1") = 0
  exact csv_relation_zero _ relation441_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk007
