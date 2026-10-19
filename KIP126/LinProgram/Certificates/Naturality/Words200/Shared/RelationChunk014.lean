module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk014
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[14]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 14 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[14]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
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
private theorem block14_mem : block14 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 14) (by decide)
private theorem block14_in_rows (r : List Char) (hr : r ∈ block14) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block14, block14_mem, hr⟩
private theorem block15_mem : block15 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 15) (by decide)
private theorem block15_in_rows (r : List Char) (hr : r ∈ block15) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block15, block15_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
private theorem block18_mem : block18 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 18) (by decide)
private theorem block18_in_rows (r : List Char) (hr : r ∈ block18) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block18, block18_mem, hr⟩
private theorem block20_mem : block20 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 20) (by decide)
private theorem block20_in_rows (r : List Char) (hr : r ∈ block20) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block20, block20_mem, hr⟩
private theorem block21_mem : block21 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 21) (by decide)
private theorem block21_in_rows (r : List Char) (hr : r ∈ block21) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block21, block21_mem, hr⟩
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
theorem relation701_mem : "3,2,376,1;1,1,535,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block2[0]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation701_zero : nativeImage "3,2,376,1;1,1,535,1" = 0 := by
  change projection (relationPolynomial "3,2,376,1;1,1,535,1") = 0
  exact csv_relation_zero _ relation701_mem
theorem relation702_mem : "74,1,122,1;8,1,352,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block2[26]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation702_zero : nativeImage "74,1,122,1;8,1,352,1" = 0 := by
  change projection (relationPolynomial "74,1,122,1;8,1,352,1") = 0
  exact csv_relation_zero _ relation702_mem
theorem relation703_mem : "8,1,352,1;7,1,371,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block2[27]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation703_zero : nativeImage "8,1,352,1;7,1,371,1" = 0 := by
  change projection (relationPolynomial "8,1,352,1;7,1,371,1") = 0
  exact csv_relation_zero _ relation703_mem
theorem relation704_mem : "43,1,181,1;3,1,477,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block2[30]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation704_zero : nativeImage "43,1,181,1;3,1,477,1" = 0 := by
  change projection (relationPolynomial "43,1,181,1;3,1,477,1") = 0
  exact csv_relation_zero _ relation704_mem
theorem relation705_mem : "7,1,370,1;5,1,413,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block4[26]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation705_zero : nativeImage "7,1,370,1;5,1,413,1" = 0 := by
  change projection (relationPolynomial "7,1,370,1;5,1,413,1") = 0
  exact csv_relation_zero _ relation705_mem
theorem relation706_mem : "5,1,413,1;5,1,412,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block4[27]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation706_zero : nativeImage "5,1,413,1;5,1,412,1" = 0 := by
  change projection (relationPolynomial "5,1,413,1;5,1,412,1") = 0
  exact csv_relation_zero _ relation706_mem
theorem relation707_mem : "5,1,412,1;1,1,531,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block4[28]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation707_zero : nativeImage "5,1,412,1;1,1,531,1" = 0 := by
  change projection (relationPolynomial "5,1,412,1;1,1,531,1") = 0
  exact csv_relation_zero _ relation707_mem
theorem relation708_mem : "23,1,235,1;8,1,351,1;0,2,533,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block4[31]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation708_zero : nativeImage "23,1,235,1;8,1,351,1;0,2,533,1" = 0 := by
  change projection (relationPolynomial "23,1,235,1;8,1,351,1;0,2,533,1") = 0
  exact csv_relation_zero _ relation708_mem
theorem relation709_mem : "32,1,209,1;13,1,294,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block6[0]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation709_zero : nativeImage "32,1,209,1;13,1,294,1" = 0 := by
  change projection (relationPolynomial "32,1,209,1;13,1,294,1") = 0
  exact csv_relation_zero _ relation709_mem
theorem relation710_mem : "2,2,473,1;1,1,13,1,287,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block6[29]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation710_zero : nativeImage "2,2,473,1;1,1,13,1,287,1" = 0 := by
  change projection (relationPolynomial "2,2,473,1;1,1,13,1,287,1") = 0
  exact csv_relation_zero _ relation710_mem
theorem relation711_mem : "17,1,261,1;13,1,293,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block7[8]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation711_zero : nativeImage "17,1,261,1;13,1,293,1" = 0 := by
  change projection (relationPolynomial "17,1,261,1;13,1,293,1") = 0
  exact csv_relation_zero _ relation711_mem
theorem relation712_mem : "13,1,293,1;8,1,350,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block7[10]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation712_zero : nativeImage "13,1,293,1;8,1,350,1" = 0 := by
  change projection (relationPolynomial "13,1,293,1;8,1,350,1") = 0
  exact csv_relation_zero _ relation712_mem
theorem relation713_mem : "0,7,482,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block8[9]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation713_zero : nativeImage "0,7,482,1" = 0 := by
  change projection (relationPolynomial "0,7,482,1") = 0
  exact csv_relation_zero _ relation713_mem
theorem relation714_mem : "13,1,291,1;9,1,317,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block8[23]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation714_zero : nativeImage "13,1,291,1;9,1,317,1" = 0 := by
  change projection (relationPolynomial "13,1,291,1;9,1,317,1") = 0
  exact csv_relation_zero _ relation714_mem
theorem relation715_mem : "9,1,317,1;9,1,316,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block8[24]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation715_zero : nativeImage "9,1,317,1;9,1,316,1" = 0 := by
  change projection (relationPolynomial "9,1,317,1;9,1,316,1") = 0
  exact csv_relation_zero _ relation715_mem
theorem relation716_mem : "9,1,316,1;8,1,346,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block8[26]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation716_zero : nativeImage "9,1,316,1;8,1,346,1" = 0 := by
  change projection (relationPolynomial "9,1,316,1;8,1,346,1") = 0
  exact csv_relation_zero _ relation716_mem
theorem relation717_mem : "23,1,233,1;9,1,13,1,194,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block9[29]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation717_zero : nativeImage "23,1,233,1;9,1,13,1,194,1" = 0 := by
  change projection (relationPolynomial "23,1,233,1;9,1,13,1,194,1") = 0
  exact csv_relation_zero _ relation717_mem
theorem relation718_mem : "20,1,248,1;8,1,9,1,219,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block10[15]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation718_zero : nativeImage "20,1,248,1;8,1,9,1,219,1" = 0 := by
  change projection (relationPolynomial "20,1,248,1;8,1,9,1,219,1") = 0
  exact csv_relation_zero _ relation718_mem
theorem relation719_mem : "17,1,259,1;8,3,160,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block11[9]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation719_zero : nativeImage "17,1,259,1;8,3,160,1" = 0 := by
  change projection (relationPolynomial "17,1,259,1;8,3,160,1") = 0
  exact csv_relation_zero _ relation719_mem
theorem relation720_mem : "17,1,258,1;9,1,315,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block11[20]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation720_zero : nativeImage "17,1,258,1;9,1,315,1" = 0 := by
  change projection (relationPolynomial "17,1,258,1;9,1,315,1") = 0
  exact csv_relation_zero _ relation720_mem
theorem relation721_mem : "9,1,315,1;8,1,345,1;0,3,516,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block11[22]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation721_zero : nativeImage "9,1,315,1;8,1,345,1;0,3,516,1" = 0 := by
  change projection (relationPolynomial "9,1,315,1;8,1,345,1;0,3,516,1") = 0
  exact csv_relation_zero _ relation721_mem
theorem relation722_mem : "16,1,258,1;8,1,344,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block11[28]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation722_zero : nativeImage "16,1,258,1;8,1,344,1" = 0 := by
  change projection (relationPolynomial "16,1,258,1;8,1,344,1") = 0
  exact csv_relation_zero _ relation722_mem
theorem relation723_mem : "49,1,160,1;31,1,206,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block12[6]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation723_zero : nativeImage "49,1,160,1;31,1,206,1" = 0 := by
  change projection (relationPolynomial "49,1,160,1;31,1,206,1") = 0
  exact csv_relation_zero _ relation723_mem
theorem relation724_mem : "31,1,206,1;28,1,224,1;19,1,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block12[8]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation724_zero : nativeImage "31,1,206,1;28,1,224,1;19,1,244,1" = 0 := by
  change projection (relationPolynomial "31,1,206,1;28,1,224,1;19,1,244,1") = 0
  exact csv_relation_zero _ relation724_mem
theorem relation725_mem : "19,1,244,1;8,1,343,1;1,1,59,1,137,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block12[11]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation725_zero : nativeImage "19,1,244,1;8,1,343,1;1,1,59,1,137,1" = 0 := by
  change projection (relationPolynomial "19,1,244,1;8,1,343,1;1,1,59,1,137,1") = 0
  exact csv_relation_zero _ relation725_mem
theorem relation726_mem : "7,1,392,1;3,2,396,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block14[28]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation726_zero : nativeImage "7,1,392,1;3,2,396,1" = 0 := by
  change projection (relationPolynomial "7,1,392,1;3,2,396,1") = 0
  exact csv_relation_zero _ relation726_mem
theorem relation727_mem : "7,1,395,1;1,1,547,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block14[30]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation727_zero : nativeImage "7,1,395,1;1,1,547,1" = 0 := by
  change projection (relationPolynomial "7,1,395,1;1,1,547,1") = 0
  exact csv_relation_zero _ relation727_mem
theorem relation728_mem : "7,1,393,1;1,1,546,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block14[31]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation728_zero : nativeImage "7,1,393,1;1,1,546,1" = 0 := by
  change projection (relationPolynomial "7,1,393,1;1,1,546,1") = 0
  exact csv_relation_zero _ relation728_mem
theorem relation729_mem : "7,1,391,1;1,1,545,1;0,2,546,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block15[13]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation729_zero : nativeImage "7,1,391,1;1,1,545,1;0,2,546,1" = 0 := by
  change projection (relationPolynomial "7,1,391,1;1,1,545,1;0,2,546,1") = 0
  exact csv_relation_zero _ relation729_mem
theorem relation730_mem : "7,1,389,1;6,1,398,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block15[21]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation730_zero : nativeImage "7,1,389,1;6,1,398,1" = 0 := by
  change projection (relationPolynomial "7,1,389,1;6,1,398,1") = 0
  exact csv_relation_zero _ relation730_mem
theorem relation731_mem : "7,1,388,1;1,1,544,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block15[27]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation731_zero : nativeImage "7,1,388,1;1,1,544,1" = 0 := by
  change projection (relationPolynomial "7,1,388,1;1,1,544,1") = 0
  exact csv_relation_zero _ relation731_mem
theorem relation732_mem : "3,1,486,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block16[13]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation732_zero : nativeImage "3,1,486,1" = 0 := by
  change projection (relationPolynomial "3,1,486,1") = 0
  exact csv_relation_zero _ relation732_mem
theorem relation733_mem : "13,1,310,1;9,1,331,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block18[7]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation733_zero : nativeImage "13,1,310,1;9,1,331,1" = 0 := by
  change projection (relationPolynomial "13,1,310,1;9,1,331,1") = 0
  exact csv_relation_zero _ relation733_mem
theorem relation734_mem : "32,1,213,1;13,2,190,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block18[25]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation734_zero : nativeImage "32,1,213,1;13,2,190,1" = 0 := by
  change projection (relationPolynomial "32,1,213,1;13,2,190,1") = 0
  exact csv_relation_zero _ relation734_mem
theorem relation735_mem : "32,1,212,1;13,2,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block20[31]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation735_zero : nativeImage "32,1,212,1;13,2,188,1" = 0 := by
  change projection (relationPolynomial "32,1,212,1;13,2,188,1") = 0
  exact csv_relation_zero _ relation735_mem
theorem relation736_mem : "8,1,359,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block21[19]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation736_zero : nativeImage "8,1,359,1" = 0 := by
  change projection (relationPolynomial "8,1,359,1") = 0
  exact csv_relation_zero _ relation736_mem
theorem relation737_mem : "42,1,188,1;8,1,13,1,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block21[20]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation737_zero : nativeImage "42,1,188,1;8,1,13,1,212,1" = 0 := by
  change projection (relationPolynomial "42,1,188,1;8,1,13,1,212,1") = 0
  exact csv_relation_zero _ relation737_mem
theorem relation738_mem : "0,1,8,1,347,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block23[10]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation738_zero : nativeImage "0,1,8,1,347,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,347,1") = 0
  exact csv_relation_zero _ relation738_mem
theorem relation739_mem : "88,1,113,1;63,1,138,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block25[2]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation739_zero : nativeImage "88,1,113,1;63,1,138,1" = 0 := by
  change projection (relationPolynomial "88,1,113,1;63,1,138,1") = 0
  exact csv_relation_zero _ relation739_mem
theorem relation740_mem : "63,1,138,1;60,1,147,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block25[3]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation740_zero : nativeImage "63,1,138,1;60,1,147,1" = 0 := by
  change projection (relationPolynomial "63,1,138,1;60,1,147,1") = 0
  exact csv_relation_zero _ relation740_mem
theorem relation741_mem : "60,1,147,1;42,1,185,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block25[6]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation741_zero : nativeImage "60,1,147,1;42,1,185,1" = 0 := by
  change projection (relationPolynomial "60,1,147,1;42,1,185,1") = 0
  exact csv_relation_zero _ relation741_mem
theorem relation742_mem : "42,1,185,1;8,4,112,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block25[10]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation742_zero : nativeImage "42,1,185,1;8,4,112,1" = 0 := by
  change projection (relationPolynomial "42,1,185,1;8,4,112,1") = 0
  exact csv_relation_zero _ relation742_mem
theorem relation743_mem : "0,1,8,1,343,1;0,7,491,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block26[27]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation743_zero : nativeImage "0,1,8,1,343,1;0,7,491,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,343,1;0,7,491,1") = 0
  exact csv_relation_zero _ relation743_mem
theorem relation744_mem : "13,1,297,1;8,2,237,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block27[7]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation744_zero : nativeImage "13,1,297,1;8,2,237,1" = 0 := by
  change projection (relationPolynomial "13,1,297,1;8,2,237,1") = 0
  exact csv_relation_zero _ relation744_mem
theorem relation745_mem : "17,1,265,1;8,4,110,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block27[29]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation745_zero : nativeImage "17,1,265,1;8,4,110,1" = 0 := by
  change projection (relationPolynomial "17,1,265,1;8,4,110,1") = 0
  exact csv_relation_zero _ relation745_mem
theorem relation746_mem : "60,1,145,1;49,1,161,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block28[1]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation746_zero : nativeImage "60,1,145,1;49,1,161,1" = 0 := by
  change projection (relationPolynomial "60,1,145,1;49,1,161,1") = 0
  exact csv_relation_zero _ relation746_mem
theorem relation747_mem : "49,1,161,1;42,1,182,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block28[2]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation747_zero : nativeImage "49,1,161,1;42,1,182,1" = 0 := by
  change projection (relationPolynomial "49,1,161,1;42,1,182,1") = 0
  exact csv_relation_zero _ relation747_mem
theorem relation748_mem : "42,1,182,1;31,1,211,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block28[3]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation748_zero : nativeImage "42,1,182,1;31,1,211,1" = 0 := by
  change projection (relationPolynomial "42,1,182,1;31,1,211,1") = 0
  exact csv_relation_zero _ relation748_mem
theorem relation749_mem : "31,1,211,1;16,1,265,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block28[6]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation749_zero : nativeImage "31,1,211,1;16,1,265,1" = 0 := by
  change projection (relationPolynomial "31,1,211,1;16,1,265,1") = 0
  exact csv_relation_zero _ relation749_mem
theorem relation750_mem : "16,1,265,1;8,1,354,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block28[7]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation750_zero : nativeImage "16,1,265,1;8,1,354,1" = 0 := by
  change projection (relationPolynomial "16,1,265,1;8,1,354,1") = 0
  exact csv_relation_zero _ relation750_mem
theorem relation751_mem : "7,1,413,1;7,1,412,1;0,3,546,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block30[18]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation751_zero : nativeImage "7,1,413,1;7,1,412,1;0,3,546,1" = 0 := by
  change projection (relationPolynomial "7,1,413,1;7,1,412,1;0,3,546,1") = 0
  exact csv_relation_zero _ relation751_mem
theorem relation752_mem : "13,1,314,1;9,1,338,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block31[18]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation752_zero : nativeImage "13,1,314,1;9,1,338,1" = 0 := by
  change projection (relationPolynomial "13,1,314,1;9,1,338,1") = 0
  exact csv_relation_zero _ relation752_mem
theorem relation753_mem : "9,1,338,1;8,1,373,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block31[20]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation753_zero : nativeImage "9,1,338,1;8,1,373,1" = 0 := by
  change projection (relationPolynomial "9,1,338,1;8,1,373,1") = 0
  exact csv_relation_zero _ relation753_mem
theorem relation754_mem : "8,1,374,1;6,1,415,1" ∈ LinE2.RawData.relations := by
  exact relation_member 14 chunkBound rows transcription
    (block31[22]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation754_zero : nativeImage "8,1,374,1;6,1,415,1" = 0 := by
  change projection (relationPolynomial "8,1,374,1;6,1,415,1") = 0
  exact csv_relation_zero _ relation754_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk014
