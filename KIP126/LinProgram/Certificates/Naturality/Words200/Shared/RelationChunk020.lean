module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk020
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[20]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 20 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[20]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block1_mem : block1 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 1) (by decide)
private theorem block1_in_rows (r : List Char) (hr : r ∈ block1) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block1, block1_mem, hr⟩
private theorem block7_mem : block7 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 7) (by decide)
private theorem block7_in_rows (r : List Char) (hr : r ∈ block7) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block7, block7_mem, hr⟩
private theorem block8_mem : block8 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 8) (by decide)
private theorem block8_in_rows (r : List Char) (hr : r ∈ block8) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block8, block8_mem, hr⟩
private theorem block10_mem : block10 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 10) (by decide)
private theorem block10_in_rows (r : List Char) (hr : r ∈ block10) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block10, block10_mem, hr⟩
private theorem block12_mem : block12 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 12) (by decide)
private theorem block12_in_rows (r : List Char) (hr : r ∈ block12) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block12, block12_mem, hr⟩
private theorem block15_mem : block15 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 15) (by decide)
private theorem block15_in_rows (r : List Char) (hr : r ∈ block15) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block15, block15_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
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
private theorem block29_mem : block29 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 29) (by decide)
private theorem block29_in_rows (r : List Char) (hr : r ∈ block29) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block29, block29_mem, hr⟩
theorem relation916_mem : "69,1,164,1;18,1,332,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block1[23]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation916_zero : nativeImage "69,1,164,1;18,1,332,1" = 0 := by
  change projection (relationPolynomial "69,1,164,1;18,1,332,1") = 0
  exact csv_relation_zero _ relation916_mem
theorem relation917_mem : "32,1,261,1;23,1,294,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block7[16]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation917_zero : nativeImage "32,1,261,1;23,1,294,1" = 0 := by
  change projection (relationPolynomial "32,1,261,1;23,1,294,1") = 0
  exact csv_relation_zero _ relation917_mem
theorem relation918_mem : "23,1,294,1;13,1,423,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block7[22]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation918_zero : nativeImage "23,1,294,1;13,1,423,1" = 0 := by
  change projection (relationPolynomial "23,1,294,1;13,1,423,1") = 0
  exact csv_relation_zero _ relation918_mem
theorem relation919_mem : "3,1,581,1;1,1,639,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block7[29]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation919_zero : nativeImage "3,1,581,1;1,1,639,1" = 0 := by
  change projection (relationPolynomial "3,1,581,1;1,1,639,1") = 0
  exact csv_relation_zero _ relation919_mem
theorem relation920_mem : "22,1,294,1;8,1,13,1,261,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block8[20]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation920_zero : nativeImage "22,1,294,1;8,1,13,1,261,1" = 0 := by
  change projection (relationPolynomial "22,1,294,1;8,1,13,1,261,1") = 0
  exact csv_relation_zero _ relation920_mem
theorem relation921_mem : "17,1,350,1;8,3,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block10[6]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation921_zero : nativeImage "17,1,350,1;8,3,209,1" = 0 := by
  change projection (relationPolynomial "17,1,350,1;8,3,209,1") = 0
  exact csv_relation_zero _ relation921_mem
theorem relation922_mem : "17,1,348,1;16,1,350,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block10[21]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation922_zero : nativeImage "17,1,348,1;16,1,350,1" = 0 := by
  change projection (relationPolynomial "17,1,348,1;16,1,350,1") = 0
  exact csv_relation_zero _ relation922_mem
theorem relation923_mem : "16,1,350,1;13,1,420,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block10[25]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation923_zero : nativeImage "16,1,350,1;13,1,420,1" = 0 := by
  change projection (relationPolynomial "16,1,350,1;13,1,420,1") = 0
  exact csv_relation_zero _ relation923_mem
theorem relation924_mem : "13,1,420,1;8,2,293,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block10[28]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation924_zero : nativeImage "13,1,420,1;8,2,293,1" = 0 := by
  change projection (relationPolynomial "13,1,420,1;8,2,293,1") = 0
  exact csv_relation_zero _ relation924_mem
theorem relation925_mem : "17,1,346,1;9,1,454,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block12[0]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation925_zero : nativeImage "17,1,346,1;9,1,454,1" = 0 := by
  change projection (relationPolynomial "17,1,346,1;9,1,454,1") = 0
  exact csv_relation_zero _ relation925_mem
theorem relation926_mem : "9,1,454,1;8,2,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block12[1]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation926_zero : nativeImage "9,1,454,1;8,2,292,1" = 0 := by
  change projection (relationPolynomial "9,1,454,1;8,2,292,1") = 0
  exact csv_relation_zero _ relation926_mem
theorem relation927_mem : "17,1,345,1;8,3,206,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block15[2]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation927_zero : nativeImage "17,1,345,1;8,3,206,1" = 0 := by
  change projection (relationPolynomial "17,1,345,1;8,3,206,1") = 0
  exact csv_relation_zero _ relation927_mem
theorem relation928_mem : "17,1,344,1;9,1,453,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block15[17]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation928_zero : nativeImage "17,1,344,1;9,1,453,1" = 0 := by
  change projection (relationPolynomial "17,1,344,1;9,1,453,1") = 0
  exact csv_relation_zero _ relation928_mem
theorem relation929_mem : "9,1,453,1;8,1,490,1;0,3,623,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block15[19]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation929_zero : nativeImage "9,1,453,1;8,1,490,1;0,3,623,1" = 0 := by
  change projection (relationPolynomial "9,1,453,1;8,1,490,1;0,3,623,1") = 0
  exact csv_relation_zero _ relation929_mem
theorem relation930_mem : "31,1,258,1;16,1,344,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block15[25]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation930_zero : nativeImage "31,1,258,1;16,1,344,1" = 0 := by
  change projection (relationPolynomial "31,1,258,1;16,1,344,1") = 0
  exact csv_relation_zero _ relation930_mem
theorem relation931_mem : "16,1,344,1;8,1,489,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block15[26]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation931_zero : nativeImage "16,1,344,1;8,1,489,1" = 0 := by
  change projection (relationPolynomial "16,1,344,1;8,1,489,1") = 0
  exact csv_relation_zero _ relation931_mem
theorem relation932_mem : "71,1,160,1;49,1,206,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block16[3]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation932_zero : nativeImage "71,1,160,1;49,1,206,1" = 0 := by
  change projection (relationPolynomial "71,1,160,1;49,1,206,1") = 0
  exact csv_relation_zero _ relation932_mem
theorem relation933_mem : "49,1,206,1;48,1,210,1;39,1,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block16[6]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation933_zero : nativeImage "49,1,206,1;48,1,210,1;39,1,244,1" = 0 := by
  change projection (relationPolynomial "49,1,206,1;48,1,210,1;39,1,244,1") = 0
  exact csv_relation_zero _ relation933_mem
theorem relation934_mem : "39,1,244,1;9,1,452,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block16[9]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation934_zero : nativeImage "39,1,244,1;9,1,452,1" = 0 := by
  change projection (relationPolynomial "39,1,244,1;9,1,452,1") = 0
  exact csv_relation_zero _ relation934_mem
theorem relation935_mem : "9,1,452,1;8,1,488,1;1,1,42,1,224,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block16[11]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation935_zero : nativeImage "9,1,452,1;8,1,488,1;1,1,42,1,224,1" = 0 := by
  change projection (relationPolynomial "9,1,452,1;8,1,488,1;1,1,42,1,224,1") = 0
  exact csv_relation_zero _ relation935_mem
theorem relation936_mem : "13,1,443,1;9,1,479,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block20[30]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation936_zero : nativeImage "13,1,443,1;9,1,479,1" = 0 := by
  change projection (relationPolynomial "13,1,443,1;9,1,479,1") = 0
  exact csv_relation_zero _ relation936_mem
theorem relation937_mem : "17,1,366,1;16,1,367,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block23[15]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation937_zero : nativeImage "17,1,366,1;16,1,367,1" = 0 := by
  change projection (relationPolynomial "17,1,366,1;16,1,367,1") = 0
  exact csv_relation_zero _ relation937_mem
theorem relation938_mem : "69,1,166,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block23[30]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation938_zero : nativeImage "69,1,166,1" = 0 := by
  change projection (relationPolynomial "69,1,166,1") = 0
  exact csv_relation_zero _ relation938_mem
theorem relation939_mem : "23,1,310,1;13,1,24,1,190,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block24[16]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation939_zero : nativeImage "23,1,310,1;13,1,24,1,190,1" = 0 := by
  change projection (relationPolynomial "23,1,310,1;13,1,24,1,190,1") = 0
  exact csv_relation_zero _ relation939_mem
theorem relation940_mem : "13,1,24,1,190,1;9,1,474,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block24[21]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation940_zero : nativeImage "13,1,24,1,190,1;9,1,474,1" = 0 := by
  change projection (relationPolynomial "13,1,24,1,190,1;9,1,474,1") = 0
  exact csv_relation_zero _ relation940_mem
theorem relation941_mem : "32,1,267,1;23,1,305,1;13,1,23,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block29[1]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation941_zero : nativeImage "32,1,267,1;23,1,305,1;13,1,23,1,188,1" = 0 := by
  change projection (relationPolynomial "32,1,267,1;23,1,305,1;13,1,23,1,188,1") = 0
  exact csv_relation_zero _ relation941_mem
theorem relation942_mem : "23,1,305,1;9,1,472,1" ∈ LinE2.RawData.relations := by
  exact relation_member 20 chunkBound rows transcription
    (block29[3]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation942_zero : nativeImage "23,1,305,1;9,1,472,1" = 0 := by
  change projection (relationPolynomial "23,1,305,1;9,1,472,1") = 0
  exact csv_relation_zero _ relation942_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk020
