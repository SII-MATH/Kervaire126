module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk001
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[1]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 1 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[1]'(chunkBound) =
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
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
private theorem block5_mem : block5 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 5) (by decide)
private theorem block5_in_rows (r : List Char) (hr : r ∈ block5) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block5, block5_mem, hr⟩
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
private theorem block24_mem : block24 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 24) (by decide)
private theorem block24_in_rows (r : List Char) (hr : r ∈ block24) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block24, block24_mem, hr⟩
private theorem block27_mem : block27 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 27) (by decide)
private theorem block27_in_rows (r : List Char) (hr : r ∈ block27) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block27, block27_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
private theorem block29_mem : block29 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 29) (by decide)
private theorem block29_in_rows (r : List Char) (hr : r ∈ block29) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block29, block29_mem, hr⟩
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
theorem relation140_mem : "4,1,72,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block0[22]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation140_zero : nativeImage "4,1,72,1" = 0 := by
  change projection (relationPolynomial "4,1,72,1") = 0
  exact csv_relation_zero _ relation140_mem
theorem relation141_mem : "3,1,82,1;1,1,107,1;0,1,2,1,95,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block1[30]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation141_zero : nativeImage "3,1,82,1;1,1,107,1;0,1,2,1,95,1" = 0 := by
  change projection (relationPolynomial "3,1,82,1;1,1,107,1;0,1,2,1,95,1") = 0
  exact csv_relation_zero _ relation141_mem
theorem relation142_mem : "2,2,82,1;1,1,105,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block2[6]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation142_zero : nativeImage "2,2,82,1;1,1,105,1" = 0 := by
  change projection (relationPolynomial "2,2,82,1;1,1,105,1") = 0
  exact csv_relation_zero _ relation142_mem
theorem relation143_mem : "23,1,33,1;13,1,52,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block2[20]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation143_zero : nativeImage "23,1,33,1;13,1,52,1" = 0 := by
  change projection (relationPolynomial "23,1,33,1;13,1,52,1") = 0
  exact csv_relation_zero _ relation143_mem
theorem relation144_mem : "23,1,32,1;13,1,51,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block2[25]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation144_zero : nativeImage "23,1,32,1;13,1,51,1" = 0 := by
  change projection (relationPolynomial "23,1,32,1;13,1,51,1") = 0
  exact csv_relation_zero _ relation144_mem
theorem relation145_mem : "0,3,101,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block2[27]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation145_zero : nativeImage "0,3,101,1" = 0 := by
  change projection (relationPolynomial "0,3,101,1") = 0
  exact csv_relation_zero _ relation145_mem
theorem relation146_mem : "22,1,32,1;8,1,13,1,23,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block2[30]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation146_zero : nativeImage "22,1,32,1;8,1,13,1,23,1" = 0 := by
  change projection (relationPolynomial "22,1,32,1;8,1,13,1,23,1") = 0
  exact csv_relation_zero _ relation146_mem
theorem relation147_mem : "17,1,42,1;8,3,13,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block3[1]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation147_zero : nativeImage "17,1,42,1;8,3,13,1" = 0 := by
  change projection (relationPolynomial "17,1,42,1;8,3,13,1") = 0
  exact csv_relation_zero _ relation147_mem
theorem relation148_mem : "16,1,42,1;8,1,60,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block3[3]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation148_zero : nativeImage "16,1,42,1;8,1,60,1" = 0 := by
  change projection (relationPolynomial "16,1,42,1;8,1,60,1") = 0
  exact csv_relation_zero _ relation148_mem
theorem relation149_mem : "8,1,59,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block3[4]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation149_zero : nativeImage "8,1,59,1" = 0 := by
  change projection (relationPolynomial "8,1,59,1") = 0
  exact csv_relation_zero _ relation149_mem
theorem relation150_mem : "6,1,64,1;0,1,112,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block4[11]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation150_zero : nativeImage "6,1,64,1;0,1,112,1" = 0 := by
  change projection (relationPolynomial "6,1,64,1;0,1,112,1") = 0
  exact csv_relation_zero _ relation150_mem
theorem relation151_mem : "18,1,43,1;3,1,94,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block4[28]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation151_zero : nativeImage "18,1,43,1;3,1,94,1" = 0 := by
  change projection (relationPolynomial "18,1,43,1;3,1,94,1") = 0
  exact csv_relation_zero _ relation151_mem
theorem relation152_mem : "2,1,105,1;1,2,107,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block5[13]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation152_zero : nativeImage "2,1,105,1;1,2,107,1" = 0 := by
  change projection (relationPolynomial "2,1,105,1;1,2,107,1") = 0
  exact csv_relation_zero _ relation152_mem
theorem relation153_mem : "3,1,90,1;2,1,103,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block5[20]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation153_zero : nativeImage "3,1,90,1;2,1,103,1" = 0 := by
  change projection (relationPolynomial "3,1,90,1;2,1,103,1") = 0
  exact csv_relation_zero _ relation153_mem
theorem relation154_mem : "29,1,32,1;9,1,13,1,23,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block8[6]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation154_zero : nativeImage "29,1,32,1;9,1,13,1,23,1" = 0 := by
  change projection (relationPolynomial "29,1,32,1;9,1,13,1,23,1") = 0
  exact csv_relation_zero _ relation154_mem
theorem relation155_mem : "17,1,46,1;8,2,9,1,13,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block8[13]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation155_zero : nativeImage "17,1,46,1;8,2,9,1,13,1" = 0 := by
  change projection (relationPolynomial "17,1,46,1;8,2,9,1,13,1") = 0
  exact csv_relation_zero _ relation155_mem
theorem relation156_mem : "0,3,113,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block8[14]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation156_zero : nativeImage "0,3,113,1" = 0 := by
  change projection (relationPolynomial "0,3,113,1") = 0
  exact csv_relation_zero _ relation156_mem
theorem relation157_mem : "17,1,45,1;9,1,60,1;9,1,59,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block8[19]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation157_zero : nativeImage "17,1,45,1;9,1,60,1;9,1,59,1" = 0 := by
  change projection (relationPolynomial "17,1,45,1;9,1,60,1;9,1,59,1") = 0
  exact csv_relation_zero _ relation157_mem
theorem relation158_mem : "9,1,60,1;8,1,63,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block8[20]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation158_zero : nativeImage "9,1,60,1;8,1,63,1" = 0 := by
  change projection (relationPolynomial "9,1,60,1;8,1,63,1") = 0
  exact csv_relation_zero _ relation158_mem
theorem relation159_mem : "9,1,59,1;0,3,112,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block8[21]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation159_zero : nativeImage "9,1,59,1;0,3,112,1" = 0 := by
  change projection (relationPolynomial "9,1,59,1;0,3,112,1") = 0
  exact csv_relation_zero _ relation159_mem
theorem relation160_mem : "8,1,67,1;7,1,72,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block9[6]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation160_zero : nativeImage "8,1,67,1;7,1,72,1" = 0 := by
  change projection (relationPolynomial "8,1,67,1;7,1,72,1") = 0
  exact csv_relation_zero _ relation160_mem
theorem relation161_mem : "0,1,8,2,39,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block10[4]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation161_zero : nativeImage "0,1,8,2,39,1" = 0 := by
  change projection (relationPolynomial "0,1,8,2,39,1") = 0
  exact csv_relation_zero _ relation161_mem
theorem relation162_mem : "7,1,75,1;7,1,74,1;3,2,76,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block10[20]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation162_zero : nativeImage "7,1,75,1;7,1,74,1;3,2,76,1" = 0 := by
  change projection (relationPolynomial "7,1,75,1;7,1,74,1;3,2,76,1") = 0
  exact csv_relation_zero _ relation162_mem
theorem relation163_mem : "7,1,74,1;0,1,122,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block10[21]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation163_zero : nativeImage "7,1,74,1;0,1,122,1" = 0 := by
  change projection (relationPolynomial "7,1,74,1;0,1,122,1") = 0
  exact csv_relation_zero _ relation163_mem
theorem relation164_mem : "7,1,73,1;4,1,92,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block10[24]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation164_zero : nativeImage "7,1,73,1;4,1,92,1" = 0 := by
  change projection (relationPolynomial "7,1,73,1;4,1,92,1") = 0
  exact csv_relation_zero _ relation164_mem
theorem relation165_mem : "1,1,8,1,64,1;0,2,118,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block11[20]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation165_zero : nativeImage "1,1,8,1,64,1;0,2,118,1" = 0 := by
  change projection (relationPolynomial "1,1,8,1,64,1;0,2,118,1") = 0
  exact csv_relation_zero _ relation165_mem
theorem relation166_mem : "0,2,7,1,72,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block13[13]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation166_zero : nativeImage "0,2,7,1,72,1" = 0 := by
  change projection (relationPolynomial "0,2,7,1,72,1") = 0
  exact csv_relation_zero _ relation166_mem
theorem relation167_mem : "32,2;13,2,23,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block13[15]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation167_zero : nativeImage "32,2;13,2,23,1" = 0 := by
  change projection (relationPolynomial "32,2;13,2,23,1") = 0
  exact csv_relation_zero _ relation167_mem
theorem relation168_mem : "9,1,64,1;8,1,72,1;5,1,81,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block13[16]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation168_zero : nativeImage "9,1,64,1;8,1,72,1;5,1,81,1" = 0 := by
  change projection (relationPolynomial "9,1,64,1;8,1,72,1;5,1,81,1") = 0
  exact csv_relation_zero _ relation168_mem
theorem relation169_mem : "5,1,81,1;1,1,119,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block13[17]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation169_zero : nativeImage "5,1,81,1;1,1,119,1" = 0 := by
  change projection (relationPolynomial "5,1,81,1;1,1,119,1") = 0
  exact csv_relation_zero _ relation169_mem
theorem relation170_mem : "17,1,51,1;8,2,13,2" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block13[26]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation170_zero : nativeImage "17,1,51,1;8,2,13,2" = 0 := by
  change projection (relationPolynomial "17,1,51,1;8,2,13,2") = 0
  exact csv_relation_zero _ relation170_mem
theorem relation171_mem : "17,1,49,1;16,1,50,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block14[13]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation171_zero : nativeImage "17,1,49,1;16,1,50,1" = 0 := by
  change projection (relationPolynomial "17,1,49,1;16,1,50,1") = 0
  exact csv_relation_zero _ relation171_mem
theorem relation172_mem : "9,1,67,1;8,1,73,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block15[4]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation172_zero : nativeImage "9,1,67,1;8,1,73,1" = 0 := by
  change projection (relationPolynomial "9,1,67,1;8,1,73,1") = 0
  exact csv_relation_zero _ relation172_mem
theorem relation173_mem : "8,1,73,1;7,1,79,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block15[5]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation173_zero : nativeImage "8,1,73,1;7,1,79,1" = 0 := by
  change projection (relationPolynomial "8,1,73,1;7,1,79,1") = 0
  exact csv_relation_zero _ relation173_mem
theorem relation174_mem : "7,1,79,1;0,3,120,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block15[6]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation174_zero : nativeImage "7,1,79,1;0,3,120,1" = 0 := by
  change projection (relationPolynomial "7,1,79,1;0,3,120,1") = 0
  exact csv_relation_zero _ relation174_mem
theorem relation175_mem : "0,1,8,3,17,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block15[21]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation175_zero : nativeImage "0,1,8,3,17,1" = 0 := by
  change projection (relationPolynomial "0,1,8,3,17,1") = 0
  exact csv_relation_zero _ relation175_mem
theorem relation176_mem : "7,1,85,1;7,1,84,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block16[22]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation176_zero : nativeImage "7,1,85,1;7,1,84,1" = 0 := by
  change projection (relationPolynomial "7,1,85,1;7,1,84,1") = 0
  exact csv_relation_zero _ relation176_mem
theorem relation177_mem : "7,1,84,1;1,1,129,1;1,1,128,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block16[25]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation177_zero : nativeImage "7,1,84,1;1,1,129,1;1,1,128,1" = 0 := by
  change projection (relationPolynomial "7,1,84,1;1,1,129,1;1,1,128,1") = 0
  exact csv_relation_zero _ relation177_mem
theorem relation178_mem : "1,1,128,1;1,2,122,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block16[26]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation178_zero : nativeImage "1,1,128,1;1,2,122,1" = 0 := by
  change projection (relationPolynomial "1,1,128,1;1,2,122,1") = 0
  exact csv_relation_zero _ relation178_mem
theorem relation179_mem : "1,1,129,1;0,2,130,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block16[27]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation179_zero : nativeImage "1,1,129,1;0,2,130,1" = 0 := by
  change projection (relationPolynomial "1,1,129,1;0,2,130,1") = 0
  exact csv_relation_zero _ relation179_mem
theorem relation180_mem : "0,5,120,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block20[6]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation180_zero : nativeImage "0,5,120,1" = 0 := by
  change projection (relationPolynomial "0,5,120,1") = 0
  exact csv_relation_zero _ relation180_mem
theorem relation181_mem : "13,1,64,1;9,1,72,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block20[10]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation181_zero : nativeImage "13,1,64,1;9,1,72,1" = 0 := by
  change projection (relationPolynomial "13,1,64,1;9,1,72,1") = 0
  exact csv_relation_zero _ relation181_mem
theorem relation182_mem : "9,1,72,1;8,1,79,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block20[11]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation182_zero : nativeImage "9,1,72,1;8,1,79,1" = 0 := by
  change projection (relationPolynomial "9,1,72,1;8,1,79,1") = 0
  exact csv_relation_zero _ relation182_mem
theorem relation183_mem : "23,1,46,1;9,1,13,1,32,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block20[16]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation183_zero : nativeImage "23,1,46,1;9,1,13,1,32,1" = 0 := by
  change projection (relationPolynomial "23,1,46,1;9,1,13,1,32,1") = 0
  exact csv_relation_zero _ relation183_mem
theorem relation184_mem : "20,1,51,1;8,1,9,1,13,2" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block20[23]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation184_zero : nativeImage "20,1,51,1;8,1,9,1,13,2" = 0 := by
  change projection (relationPolynomial "20,1,51,1;8,1,9,1,13,2") = 0
  exact csv_relation_zero _ relation184_mem
theorem relation185_mem : "17,1,55,1;16,1,56,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block21[8]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation185_zero : nativeImage "17,1,55,1;16,1,56,1" = 0 := by
  change projection (relationPolynomial "17,1,55,1;16,1,56,1") = 0
  exact csv_relation_zero _ relation185_mem
theorem relation186_mem : "16,1,56,1;8,1,78,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block21[9]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation186_zero : nativeImage "16,1,56,1;8,1,78,1" = 0 := by
  change projection (relationPolynomial "16,1,56,1;8,1,78,1") = 0
  exact csv_relation_zero _ relation186_mem
theorem relation187_mem : "9,1,71,1;8,1,77,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block21[13]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation187_zero : nativeImage "9,1,71,1;8,1,77,1" = 0 := by
  change projection (relationPolynomial "9,1,71,1;8,1,77,1") = 0
  exact csv_relation_zero _ relation187_mem
theorem relation188_mem : "13,1,68,1;9,1,75,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block22[9]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation188_zero : nativeImage "13,1,68,1;9,1,75,1" = 0 := by
  change projection (relationPolynomial "13,1,68,1;9,1,75,1") = 0
  exact csv_relation_zero _ relation188_mem
theorem relation189_mem : "9,1,73,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block22[16]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation189_zero : nativeImage "9,1,73,1" = 0 := by
  change projection (relationPolynomial "9,1,73,1") = 0
  exact csv_relation_zero _ relation189_mem
theorem relation190_mem : "8,1,81,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block22[28]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation190_zero : nativeImage "8,1,81,1" = 0 := by
  change projection (relationPolynomial "8,1,81,1") = 0
  exact csv_relation_zero _ relation190_mem
theorem relation191_mem : "11,1,76,1;7,1,95,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block24[0]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation191_zero : nativeImage "11,1,76,1;7,1,95,1" = 0 := by
  change projection (relationPolynomial "11,1,76,1;7,1,95,1") = 0
  exact csv_relation_zero _ relation191_mem
theorem relation192_mem : "2,1,133,1;1,1,139,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block24[9]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation192_zero : nativeImage "2,1,133,1;1,1,139,1" = 0 := by
  change projection (relationPolynomial "2,1,133,1;1,1,139,1") = 0
  exact csv_relation_zero _ relation192_mem
theorem relation193_mem : "23,1,52,1;13,2,33,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block27[0]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation193_zero : nativeImage "23,1,52,1;13,2,33,1" = 0 := by
  change projection (relationPolynomial "23,1,52,1;13,2,33,1") = 0
  exact csv_relation_zero _ relation193_mem
theorem relation194_mem : "13,1,72,1;9,1,79,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block27[2]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation194_zero : nativeImage "13,1,72,1;9,1,79,1" = 0 := by
  change projection (relationPolynomial "13,1,72,1;9,1,79,1") = 0
  exact csv_relation_zero _ relation194_mem
theorem relation195_mem : "9,1,79,1;8,1,90,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block27[3]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation195_zero : nativeImage "9,1,79,1;8,1,90,1" = 0 := by
  change projection (relationPolynomial "9,1,79,1;8,1,90,1") = 0
  exact csv_relation_zero _ relation195_mem
theorem relation196_mem : "8,1,90,1;8,1,89,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block27[4]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation196_zero : nativeImage "8,1,90,1;8,1,89,1" = 0 := by
  change projection (relationPolynomial "8,1,90,1;8,1,89,1") = 0
  exact csv_relation_zero _ relation196_mem
theorem relation197_mem : "23,1,51,1;13,2,32,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block27[11]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation197_zero : nativeImage "23,1,51,1;13,2,32,1" = 0 := by
  change projection (relationPolynomial "23,1,51,1;13,2,32,1") = 0
  exact csv_relation_zero _ relation197_mem
theorem relation198_mem : "22,1,51,1;8,1,13,3" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block27[19]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation198_zero : nativeImage "22,1,51,1;8,1,13,3" = 0 := by
  change projection (relationPolynomial "22,1,51,1;8,1,13,3") = 0
  exact csv_relation_zero _ relation198_mem
theorem relation199_mem : "17,1,60,1;17,1,59,1;8,5" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block27[26]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation199_zero : nativeImage "17,1,60,1;17,1,59,1;8,5" = 0 := by
  change projection (relationPolynomial "17,1,60,1;17,1,59,1;8,5") = 0
  exact csv_relation_zero _ relation199_mem
theorem relation200_mem : "17,1,59,1;0,3,138,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block27[27]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation200_zero : nativeImage "17,1,59,1;0,3,138,1" = 0 := by
  change projection (relationPolynomial "17,1,59,1;0,3,138,1") = 0
  exact csv_relation_zero _ relation200_mem
theorem relation201_mem : "31,1,42,1;16,1,60,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block27[30]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation201_zero : nativeImage "31,1,42,1;16,1,60,1" = 0 := by
  change projection (relationPolynomial "31,1,42,1;16,1,60,1") = 0
  exact csv_relation_zero _ relation201_mem
theorem relation202_mem : "17,3;8,1,88,1;0,3,137,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block28[1]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation202_zero : nativeImage "17,3;8,1,88,1;0,3,137,1" = 0 := by
  change projection (relationPolynomial "17,3;8,1,88,1;0,3,137,1") = 0
  exact csv_relation_zero _ relation202_mem
theorem relation203_mem : "13,1,73,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block29[1]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation203_zero : nativeImage "13,1,73,1" = 0 := by
  change projection (relationPolynomial "13,1,73,1") = 0
  exact csv_relation_zero _ relation203_mem
theorem relation204_mem : "10,1,80,1;9,1,81,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block29[18]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation204_zero : nativeImage "10,1,80,1;9,1,81,1" = 0 := by
  change projection (relationPolynomial "10,1,80,1;9,1,81,1") = 0
  exact csv_relation_zero _ relation204_mem
theorem relation205_mem : "9,1,81,1;5,1,108,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block29[19]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation205_zero : nativeImage "9,1,81,1;5,1,108,1" = 0 := by
  change projection (relationPolynomial "9,1,81,1;5,1,108,1") = 0
  exact csv_relation_zero _ relation205_mem
theorem relation206_mem : "5,1,108,1;1,1,144,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block29[21]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation206_zero : nativeImage "5,1,108,1;1,1,144,1" = 0 := by
  change projection (relationPolynomial "5,1,108,1;1,1,144,1") = 0
  exact csv_relation_zero _ relation206_mem
theorem relation207_mem : "15,1,64,1;2,1,137,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block29[31]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation207_zero : nativeImage "15,1,64,1;2,1,137,1" = 0 := by
  change projection (relationPolynomial "15,1,64,1;2,1,137,1") = 0
  exact csv_relation_zero _ relation207_mem
theorem relation208_mem : "2,1,137,1;0,1,146,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block30[0]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation208_zero : nativeImage "2,1,137,1;0,1,146,1" = 0 := by
  change projection (relationPolynomial "2,1,137,1;0,1,146,1") = 0
  exact csv_relation_zero _ relation208_mem
theorem relation209_mem : "2,1,142,1;1,2,143,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block30[20]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation209_zero : nativeImage "2,1,142,1;1,2,143,1" = 0 := by
  change projection (relationPolynomial "2,1,142,1;1,2,143,1") = 0
  exact csv_relation_zero _ relation209_mem
theorem relation210_mem : "2,2,132,1;1,2,142,1" ∈ LinE2.RawData.relations := by
  exact relation_member 1 chunkBound rows transcription
    (block30[22]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation210_zero : nativeImage "2,2,132,1;1,2,142,1" = 0 := by
  change projection (relationPolynomial "2,2,132,1;1,2,142,1") = 0
  exact csv_relation_zero _ relation210_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk001
