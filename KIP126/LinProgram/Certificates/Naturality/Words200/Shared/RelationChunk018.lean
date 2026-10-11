module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk018
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[18]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 18 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[18]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block1_mem : block1 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 1) (by decide)
private theorem block1_in_rows (r : List Char) (hr : r ∈ block1) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block1, block1_mem, hr⟩
private theorem block2_mem : block2 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 2) (by decide)
private theorem block2_in_rows (r : List Char) (hr : r ∈ block2) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block2, block2_mem, hr⟩
private theorem block14_mem : block14 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 14) (by decide)
private theorem block14_in_rows (r : List Char) (hr : r ∈ block14) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block14, block14_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
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
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block27_mem : block27 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 27) (by decide)
private theorem block27_in_rows (r : List Char) (hr : r ∈ block27) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block27, block27_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation857_mem : "17,1,312,1;16,1,314,1;0,1,613,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block1[23]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation857_zero : nativeImage "17,1,312,1;16,1,314,1;0,1,613,1" = 0 := by
  change projection (relationPolynomial "17,1,312,1;16,1,314,1;0,1,613,1") = 0
  exact csv_relation_zero _ relation857_mem
theorem relation858_mem : "17,1,64,1,69,1;15,1,333,1;8,1,449,1;7,1,472,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block2[13]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation858_zero : nativeImage "17,1,64,1,69,1;15,1,333,1;8,1,449,1;7,1,472,1" = 0 := by
  change projection (relationPolynomial "17,1,64,1,69,1;15,1,333,1;8,1,449,1;7,1,472,1") = 0
  exact csv_relation_zero _ relation858_mem
theorem relation859_mem : "15,1,333,1;6,1,475,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block2[14]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation859_zero : nativeImage "15,1,333,1;6,1,475,1" = 0 := by
  change projection (relationPolynomial "15,1,333,1;6,1,475,1") = 0
  exact csv_relation_zero _ relation859_mem
theorem relation860_mem : "6,1,475,1;2,1,582,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block2[17]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation860_zero : nativeImage "6,1,475,1;2,1,582,1" = 0 := by
  change projection (relationPolynomial "6,1,475,1;2,1,582,1") = 0
  exact csv_relation_zero _ relation860_mem
theorem relation861_mem : "7,1,472,1;2,1,582,1;0,1,612,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block2[18]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation861_zero : nativeImage "7,1,472,1;2,1,582,1;0,1,612,1" = 0 := by
  change projection (relationPolynomial "7,1,472,1;2,1,582,1;0,1,612,1") = 0
  exact csv_relation_zero _ relation861_mem
theorem relation862_mem : "9,1,69,1,95,1;7,1,485,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block14[9]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation862_zero : nativeImage "9,1,69,1,95,1;7,1,485,1" = 0 := by
  change projection (relationPolynomial "9,1,69,1,95,1;7,1,485,1") = 0
  exact csv_relation_zero _ relation862_mem
theorem relation863_mem : "23,1,282,1;3,1,43,1,189,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block16[23]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation863_zero : nativeImage "23,1,282,1;3,1,43,1,189,1" = 0 := by
  change projection (relationPolynomial "23,1,282,1;3,1,43,1,189,1") = 0
  exact csv_relation_zero _ relation863_mem
theorem relation864_mem : "3,1,43,1,189,1;1,1,3,1,540,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block16[24]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation864_zero : nativeImage "3,1,43,1,189,1;1,1,3,1,540,1" = 0 := by
  change projection (relationPolynomial "3,1,43,1,189,1;1,1,3,1,540,1") = 0
  exact csv_relation_zero _ relation864_mem
theorem relation865_mem : "29,1,261,1;23,1,280,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block20[15]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation865_zero : nativeImage "29,1,261,1;23,1,280,1" = 0 := by
  change projection (relationPolynomial "29,1,261,1;23,1,280,1") = 0
  exact csv_relation_zero _ relation865_mem
theorem relation866_mem : "23,1,280,1;13,1,384,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block20[17]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation866_zero : nativeImage "23,1,280,1;13,1,384,1" = 0 := by
  change projection (relationPolynomial "23,1,280,1;13,1,384,1") = 0
  exact csv_relation_zero _ relation866_mem
theorem relation867_mem : "13,1,384,1;9,1,423,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block20[19]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation867_zero : nativeImage "13,1,384,1;9,1,423,1" = 0 := by
  change projection (relationPolynomial "13,1,384,1;9,1,423,1") = 0
  exact csv_relation_zero _ relation867_mem
theorem relation868_mem : "20,1,294,1;8,1,9,1,261,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block21[16]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation868_zero : nativeImage "20,1,294,1;8,1,9,1,261,1" = 0 := by
  change projection (relationPolynomial "20,1,294,1;8,1,9,1,261,1") = 0
  exact csv_relation_zero _ relation868_mem
theorem relation869_mem : "20,1,293,1;13,1,382,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block22[28]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation869_zero : nativeImage "20,1,293,1;13,1,382,1" = 0 := by
  change projection (relationPolynomial "20,1,293,1;13,1,382,1") = 0
  exact csv_relation_zero _ relation869_mem
theorem relation870_mem : "13,1,382,1;8,2,279,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block22[29]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation870_zero : nativeImage "13,1,382,1;8,2,279,1" = 0 := by
  change projection (relationPolynomial "13,1,382,1;8,2,279,1") = 0
  exact csv_relation_zero _ relation870_mem
theorem relation871_mem : "17,1,318,1;9,1,420,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block23[16]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation871_zero : nativeImage "17,1,318,1;9,1,420,1" = 0 := by
  change projection (relationPolynomial "17,1,318,1;9,1,420,1") = 0
  exact csv_relation_zero _ relation871_mem
theorem relation872_mem : "17,1,316,1;8,1,454,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block24[25]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation872_zero : nativeImage "17,1,316,1;8,1,454,1" = 0 := by
  change projection (relationPolynomial "17,1,316,1;8,1,454,1") = 0
  exact csv_relation_zero _ relation872_mem
theorem relation873_mem : "0,2,8,3,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block24[26]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation873_zero : nativeImage "0,2,8,3,188,1" = 0 := by
  change projection (relationPolynomial "0,2,8,3,188,1") = 0
  exact csv_relation_zero _ relation873_mem
theorem relation874_mem : "72,1,149,1;64,1,160,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block24[28]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation874_zero : nativeImage "72,1,149,1;64,1,160,1" = 0 := by
  change projection (relationPolynomial "72,1,149,1;64,1,160,1") = 0
  exact csv_relation_zero _ relation874_mem
theorem relation875_mem : "13,1,380,1;8,2,278,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block25[14]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation875_zero : nativeImage "13,1,380,1;8,2,278,1" = 0 := by
  change projection (relationPolynomial "13,1,380,1;8,2,278,1") = 0
  exact csv_relation_zero _ relation875_mem
theorem relation876_mem : "0,2,16,1,64,2" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block27[15]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation876_zero : nativeImage "0,2,16,1,64,2" = 0 := by
  change projection (relationPolynomial "0,2,16,1,64,2") = 0
  exact csv_relation_zero _ relation876_mem
theorem relation877_mem : "17,1,315,1;8,2,16,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block28[10]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation877_zero : nativeImage "17,1,315,1;8,2,16,1,149,1" = 0 := by
  change projection (relationPolynomial "17,1,315,1;8,2,16,1,149,1") = 0
  exact csv_relation_zero _ relation877_mem
theorem relation878_mem : "31,1,247,1;16,1,315,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block28[16]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation878_zero : nativeImage "31,1,247,1;16,1,315,1" = 0 := by
  change projection (relationPolynomial "31,1,247,1;16,1,315,1") = 0
  exact csv_relation_zero _ relation878_mem
theorem relation879_mem : "16,1,315,1;8,1,453,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block28[17]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation879_zero : nativeImage "16,1,315,1;8,1,453,1" = 0 := by
  change projection (relationPolynomial "16,1,315,1;8,1,453,1") = 0
  exact csv_relation_zero _ relation879_mem
theorem relation880_mem : "2,1,7,1,450,1;1,1,7,1,478,1" ∈ LinE2.RawData.relations := by
  exact relation_member 18 chunkBound rows transcription
    (block31[23]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation880_zero : nativeImage "2,1,7,1,450,1;1,1,7,1,478,1" = 0 := by
  change projection (relationPolynomial "2,1,7,1,450,1;1,1,7,1,478,1") = 0
  exact csv_relation_zero _ relation880_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk018
