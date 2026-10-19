module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk012
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[12]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 12 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[12]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block2_mem : block2 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 2) (by decide)
private theorem block2_in_rows (r : List Char) (hr : r ∈ block2) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block2, block2_mem, hr⟩
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
private theorem block5_mem : block5 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 5) (by decide)
private theorem block5_in_rows (r : List Char) (hr : r ∈ block5) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block5, block5_mem, hr⟩
private theorem block6_mem : block6 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 6) (by decide)
private theorem block6_in_rows (r : List Char) (hr : r ∈ block6) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block6, block6_mem, hr⟩
private theorem block7_mem : block7 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 7) (by decide)
private theorem block7_in_rows (r : List Char) (hr : r ∈ block7) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block7, block7_mem, hr⟩
private theorem block10_mem : block10 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 10) (by decide)
private theorem block10_in_rows (r : List Char) (hr : r ∈ block10) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block10, block10_mem, hr⟩
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
private theorem block17_mem : block17 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 17) (by decide)
private theorem block17_in_rows (r : List Char) (hr : r ∈ block17) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block17, block17_mem, hr⟩
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
theorem relation618_mem : "24,1,213,1;13,1,269,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block2[20]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation618_zero : nativeImage "24,1,213,1;13,1,269,1" = 0 := by
  change projection (relationPolynomial "24,1,213,1;13,1,269,1") = 0
  exact csv_relation_zero _ relation618_mem
theorem relation619_mem : "13,1,269,1;9,1,288,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block2[22]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation619_zero : nativeImage "13,1,269,1;9,1,288,1" = 0 := by
  change projection (relationPolynomial "13,1,269,1;9,1,288,1") = 0
  exact csv_relation_zero _ relation619_mem
theorem relation620_mem : "34,1,188,1;1,2,457,1;0,1,495,1;0,2,482,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block4[7]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation620_zero : nativeImage "34,1,188,1;1,2,457,1;0,1,495,1;0,2,482,1" = 0 := by
  change projection (relationPolynomial "34,1,188,1;1,2,457,1;0,1,495,1;0,2,482,1") = 0
  exact csv_relation_zero _ relation620_mem
theorem relation621_mem : "24,1,212,1;13,1,268,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block4[18]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation621_zero : nativeImage "24,1,212,1;13,1,268,1" = 0 := by
  change projection (relationPolynomial "24,1,212,1;13,1,268,1") = 0
  exact csv_relation_zero _ relation621_mem
theorem relation622_mem : "8,1,308,1;0,2,69,1,112,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block4[29]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation622_zero : nativeImage "8,1,308,1;0,2,69,1,112,1" = 0 := by
  change projection (relationPolynomial "8,1,308,1;0,2,69,1,112,1") = 0
  exact csv_relation_zero _ relation622_mem
theorem relation623_mem : "32,1,188,1;23,1,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block5[6]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation623_zero : nativeImage "32,1,188,1;23,1,212,1" = 0 := by
  change projection (relationPolynomial "32,1,188,1;23,1,212,1") = 0
  exact csv_relation_zero _ relation623_mem
theorem relation624_mem : "23,1,212,1;13,1,267,1;9,1,286,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block5[9]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation624_zero : nativeImage "23,1,212,1;13,1,267,1;9,1,286,1" = 0 := by
  change projection (relationPolynomial "23,1,212,1;13,1,267,1;9,1,286,1") = 0
  exact csv_relation_zero _ relation624_mem
theorem relation625_mem : "8,1,305,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block5[30]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation625_zero : nativeImage "8,1,305,1" = 0 := by
  change projection (relationPolynomial "8,1,305,1") = 0
  exact csv_relation_zero _ relation625_mem
theorem relation626_mem : "22,1,212,1;8,1,13,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block6[0]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation626_zero : nativeImage "22,1,212,1;8,1,13,1,188,1" = 0 := by
  change projection (relationPolynomial "22,1,212,1;8,1,13,1,188,1") = 0
  exact csv_relation_zero _ relation626_mem
theorem relation627_mem : "8,1,300,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block7[0]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation627_zero : nativeImage "8,1,300,1" = 0 := by
  change projection (relationPolynomial "8,1,300,1") = 0
  exact csv_relation_zero _ relation627_mem
theorem relation628_mem : "72,1,113,1;64,1,118,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block7[15]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation628_zero : nativeImage "72,1,113,1;64,1,118,1" = 0 := by
  change projection (relationPolynomial "72,1,113,1;64,1,118,1") = 0
  exact csv_relation_zero _ relation628_mem
theorem relation629_mem : "64,1,118,1;31,1,188,1;19,1,226,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block7[18]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation629_zero : nativeImage "64,1,118,1;31,1,188,1;19,1,226,1" = 0 := by
  change projection (relationPolynomial "64,1,118,1;31,1,188,1;19,1,226,1") = 0
  exact csv_relation_zero _ relation629_mem
theorem relation630_mem : "31,1,188,1;8,1,299,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block7[20]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation630_zero : nativeImage "31,1,188,1;8,1,299,1" = 0 := by
  change projection (relationPolynomial "31,1,188,1;8,1,299,1") = 0
  exact csv_relation_zero _ relation630_mem
theorem relation631_mem : "19,1,226,1;6,1,317,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block7[21]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation631_zero : nativeImage "19,1,226,1;6,1,317,1" = 0 := by
  change projection (relationPolynomial "19,1,226,1;6,1,317,1") = 0
  exact csv_relation_zero _ relation631_mem
theorem relation632_mem : "6,1,317,1;6,1,316,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block7[22]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation632_zero : nativeImage "6,1,317,1;6,1,316,1" = 0 := by
  change projection (relationPolynomial "6,1,317,1;6,1,316,1") = 0
  exact csv_relation_zero _ relation632_mem
theorem relation633_mem : "6,1,316,1;0,1,8,1,291,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block7[24]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation633_zero : nativeImage "6,1,316,1;0,1,8,1,291,1" = 0 := by
  change projection (relationPolynomial "6,1,316,1;0,1,8,1,291,1") = 0
  exact csv_relation_zero _ relation633_mem
theorem relation634_mem : "17,1,237,1;16,1,238,1;15,1,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block10[20]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation634_zero : nativeImage "17,1,237,1;16,1,238,1;15,1,244,1" = 0 := by
  change projection (relationPolynomial "17,1,237,1;16,1,238,1;15,1,244,1") = 0
  exact csv_relation_zero _ relation634_mem
theorem relation635_mem : "16,1,238,1;8,1,298,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block10[21]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation635_zero : nativeImage "16,1,238,1;8,1,298,1" = 0 := by
  change projection (relationPolynomial "16,1,238,1;8,1,298,1") = 0
  exact csv_relation_zero _ relation635_mem
theorem relation636_mem : "15,1,244,1;2,1,452,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block10[22]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation636_zero : nativeImage "15,1,244,1;2,1,452,1" = 0 := by
  change projection (relationPolynomial "15,1,244,1;2,1,452,1") = 0
  exact csv_relation_zero _ relation636_mem
theorem relation637_mem : "2,1,452,1;0,1,488,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block10[23]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation637_zero : nativeImage "2,1,452,1;0,1,488,1" = 0 := by
  change projection (relationPolynomial "2,1,452,1;0,1,488,1") = 0
  exact csv_relation_zero _ relation637_mem
theorem relation638_mem : "17,1,236,1;8,1,296,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block12[18]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation638_zero : nativeImage "17,1,236,1;8,1,296,1" = 0 := by
  change projection (relationPolynomial "17,1,236,1;8,1,296,1") = 0
  exact csv_relation_zero _ relation638_mem
theorem relation639_mem : "2,1,477,1;1,1,3,1,412,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block14[2]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation639_zero : nativeImage "2,1,477,1;1,1,3,1,412,1" = 0 := by
  change projection (relationPolynomial "2,1,477,1;1,1,3,1,412,1") = 0
  exact csv_relation_zero _ relation639_mem
theorem relation640_mem : "7,1,330,1;4,1,388,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block14[14]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation640_zero : nativeImage "7,1,330,1;4,1,388,1" = 0 := by
  change projection (relationPolynomial "7,1,330,1;4,1,388,1") = 0
  exact csv_relation_zero _ relation640_mem
theorem relation641_mem : "4,1,388,1;3,1,426,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block14[15]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation641_zero : nativeImage "4,1,388,1;3,1,426,1" = 0 := by
  change projection (relationPolynomial "4,1,388,1;3,1,426,1") = 0
  exact csv_relation_zero _ relation641_mem
theorem relation642_mem : "3,1,426,1;1,1,497,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block14[17]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation642_zero : nativeImage "3,1,426,1;1,1,497,1" = 0 := by
  change projection (relationPolynomial "3,1,426,1;1,1,497,1") = 0
  exact csv_relation_zero _ relation642_mem
theorem relation643_mem : "69,1,118,1;8,1,312,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block15[2]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation643_zero : nativeImage "69,1,118,1;8,1,312,1" = 0 := by
  change projection (relationPolynomial "69,1,118,1;8,1,312,1") = 0
  exact csv_relation_zero _ relation643_mem
theorem relation644_mem : "11,1,287,1;7,1,328,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block15[30]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation644_zero : nativeImage "11,1,287,1;7,1,328,1" = 0 := by
  change projection (relationPolynomial "11,1,287,1;7,1,328,1") = 0
  exact csv_relation_zero _ relation644_mem
theorem relation645_mem : "0,2,495,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block16[22]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation645_zero : nativeImage "0,2,495,1" = 0 := by
  change projection (relationPolynomial "0,2,495,1") = 0
  exact csv_relation_zero _ relation645_mem
theorem relation646_mem : "2,1,472,1;1,1,493,1;0,3,69,1,112,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block17[11]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation646_zero : nativeImage "2,1,472,1;1,1,493,1;0,3,69,1,112,1" = 0 := by
  change projection (relationPolynomial "2,1,472,1;1,1,493,1;0,3,69,1,112,1") = 0
  exact csv_relation_zero _ relation646_mem
theorem relation647_mem : "7,1,341,1;1,1,508,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block24[8]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation647_zero : nativeImage "7,1,341,1;1,1,508,1" = 0 := by
  change projection (relationPolynomial "7,1,341,1;1,1,508,1") = 0
  exact csv_relation_zero _ relation647_mem
theorem relation648_mem : "3,2,341,1;1,1,507,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block24[10]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation648_zero : nativeImage "3,2,341,1;1,1,507,1" = 0 := by
  change projection (relationPolynomial "3,2,341,1;1,1,507,1") = 0
  exact csv_relation_zero _ relation648_mem
theorem relation649_mem : "69,1,122,1;18,1,241,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block24[12]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation649_zero : nativeImage "69,1,122,1;18,1,241,1" = 0 := by
  change projection (relationPolynomial "69,1,122,1;18,1,241,1") = 0
  exact csv_relation_zero _ relation649_mem
theorem relation650_mem : "18,1,241,1;3,2,340,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block24[13]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation650_zero : nativeImage "18,1,241,1;3,2,340,1" = 0 := by
  change projection (relationPolynomial "18,1,241,1;3,2,340,1") = 0
  exact csv_relation_zero _ relation650_mem
theorem relation651_mem : "3,2,340,1;1,1,505,1;0,2,507,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block24[15]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation651_zero : nativeImage "3,2,340,1;1,1,505,1;0,2,507,1" = 0 := by
  change projection (relationPolynomial "3,2,340,1;1,1,505,1;0,2,507,1") = 0
  exact csv_relation_zero _ relation651_mem
theorem relation652_mem : "3,1,446,1;0,2,506,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block24[16]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation652_zero : nativeImage "3,1,446,1;0,2,506,1" = 0 := by
  change projection (relationPolynomial "3,1,446,1;0,2,506,1") = 0
  exact csv_relation_zero _ relation652_mem
theorem relation653_mem : "38,1,191,1;18,1,239,1;6,1,340,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block24[29]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation653_zero : nativeImage "38,1,191,1;18,1,239,1;6,1,340,1" = 0 := by
  change projection (relationPolynomial "38,1,191,1;18,1,239,1;6,1,340,1") = 0
  exact csv_relation_zero _ relation653_mem
theorem relation654_mem : "18,1,239,1;6,1,340,1;3,1,444,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block24[30]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation654_zero : nativeImage "18,1,239,1;6,1,340,1;3,1,444,1" = 0 := by
  change projection (relationPolynomial "18,1,239,1;6,1,340,1;3,1,444,1") = 0
  exact csv_relation_zero _ relation654_mem
theorem relation655_mem : "3,1,444,1;2,2,445,1;1,1,504,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block25[1]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation655_zero : nativeImage "3,1,444,1;2,2,445,1;1,1,504,1" = 0 := by
  change projection (relationPolynomial "3,1,444,1;2,2,445,1;1,1,504,1") = 0
  exact csv_relation_zero _ relation655_mem
theorem relation656_mem : "2,2,445,1;0,1,514,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block25[2]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation656_zero : nativeImage "2,2,445,1;0,1,514,1" = 0 := by
  change projection (relationPolynomial "2,2,445,1;0,1,514,1") = 0
  exact csv_relation_zero _ relation656_mem
theorem relation657_mem : "7,1,337,1;4,1,415,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block25[11]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation657_zero : nativeImage "7,1,337,1;4,1,415,1" = 0 := by
  change projection (relationPolynomial "7,1,337,1;4,1,415,1") = 0
  exact csv_relation_zero _ relation657_mem
theorem relation658_mem : "4,1,415,1;1,1,7,1,322,1;0,1,2,1,479,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block25[15]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation658_zero : nativeImage "4,1,415,1;1,1,7,1,322,1;0,1,2,1,479,1" = 0 := by
  change projection (relationPolynomial "4,1,415,1;1,1,7,1,322,1;0,1,2,1,479,1") = 0
  exact csv_relation_zero _ relation658_mem
theorem relation659_mem : "3,2,336,1;2,1,484,1;1,2,485,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block26[9]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation659_zero : nativeImage "3,2,336,1;2,1,484,1;1,2,485,1" = 0 := by
  change projection (relationPolynomial "3,2,336,1;2,1,484,1;1,2,485,1") = 0
  exact csv_relation_zero _ relation659_mem
theorem relation660_mem : "29,1,209,1;13,1,280,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block29[9]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation660_zero : nativeImage "29,1,209,1;13,1,280,1" = 0 := by
  change projection (relationPolynomial "29,1,209,1;13,1,280,1") = 0
  exact csv_relation_zero _ relation660_mem
theorem relation661_mem : "13,1,280,1;9,1,294,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block29[11]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation661_zero : nativeImage "13,1,280,1;9,1,294,1" = 0 := by
  change projection (relationPolynomial "13,1,280,1;9,1,294,1") = 0
  exact csv_relation_zero _ relation661_mem
theorem relation662_mem : "17,1,250,1;9,1,293,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block30[13]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation662_zero : nativeImage "17,1,250,1;9,1,293,1" = 0 := by
  change projection (relationPolynomial "17,1,250,1;9,1,293,1") = 0
  exact csv_relation_zero _ relation662_mem
theorem relation663_mem : "0,2,8,1,13,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 12 chunkBound rows transcription
    (block31[20]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation663_zero : nativeImage "0,2,8,1,13,1,188,1" = 0 := by
  change projection (relationPolynomial "0,2,8,1,13,1,188,1") = 0
  exact csv_relation_zero _ relation663_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk012
