module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk011
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[11]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 11 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[11]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block1_mem : block1 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 1) (by decide)
private theorem block1_in_rows (r : List Char) (hr : r ∈ block1) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block1, block1_mem, hr⟩
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
private theorem block9_mem : block9 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 9) (by decide)
private theorem block9_in_rows (r : List Char) (hr : r ∈ block9) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block9, block9_mem, hr⟩
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
private theorem block27_mem : block27 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 27) (by decide)
private theorem block27_in_rows (r : List Char) (hr : r ∈ block27) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block27, block27_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
theorem relation572_mem : "29,1,188,1;23,1,201,1;15,1,235,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block0[27]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation572_zero : nativeImage "29,1,188,1;23,1,201,1;15,1,235,1" = 0 := by
  change projection (relationPolynomial "29,1,188,1;23,1,201,1;15,1,235,1") = 0
  exact csv_relation_zero _ relation572_mem
theorem relation573_mem : "23,1,201,1;15,1,235,1;9,1,267,1;8,1,286,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block0[28]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation573_zero : nativeImage "23,1,201,1;15,1,235,1;9,1,267,1;8,1,286,1" = 0 := by
  change projection (relationPolynomial "23,1,201,1;15,1,235,1;9,1,267,1;8,1,286,1") = 0
  exact csv_relation_zero _ relation573_mem
theorem relation574_mem : "8,1,286,1;8,1,285,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block0[29]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation574_zero : nativeImage "8,1,286,1;8,1,285,1" = 0 := by
  change projection (relationPolynomial "8,1,286,1;8,1,285,1") = 0
  exact csv_relation_zero _ relation574_mem
theorem relation575_mem : "15,1,235,1;2,1,421,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block1[0]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation575_zero : nativeImage "15,1,235,1;2,1,421,1" = 0 := by
  change projection (relationPolynomial "15,1,235,1;2,1,421,1") = 0
  exact csv_relation_zero _ relation575_mem
theorem relation576_mem : "8,1,285,1;0,1,3,1,359,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block1[1]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation576_zero : nativeImage "8,1,285,1;0,1,3,1,359,1" = 0 := by
  change projection (relationPolynomial "8,1,285,1;0,1,3,1,359,1") = 0
  exact csv_relation_zero _ relation576_mem
theorem relation577_mem : "2,1,421,1;0,3,438,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block1[2]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation577_zero : nativeImage "2,1,421,1;0,3,438,1" = 0 := by
  change projection (relationPolynomial "2,1,421,1;0,3,438,1") = 0
  exact csv_relation_zero _ relation577_mem
theorem relation578_mem : "0,3,438,1;0,5,418,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block1[3]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation578_zero : nativeImage "0,3,438,1;0,5,418,1" = 0 := by
  change projection (relationPolynomial "0,3,438,1;0,5,418,1") = 0
  exact csv_relation_zero _ relation578_mem
theorem relation579_mem : "20,1,212,1;13,1,255,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block1[11]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation579_zero : nativeImage "20,1,212,1;13,1,255,1" = 0 := by
  change projection (relationPolynomial "20,1,212,1;13,1,255,1") = 0
  exact csv_relation_zero _ relation579_mem
theorem relation580_mem : "13,1,255,1;8,1,9,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block1[14]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation580_zero : nativeImage "13,1,255,1;8,1,9,1,188,1" = 0 := by
  change projection (relationPolynomial "13,1,255,1;8,1,9,1,188,1") = 0
  exact csv_relation_zero _ relation580_mem
theorem relation581_mem : "13,1,254,1;8,2,201,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block1[27]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation581_zero : nativeImage "13,1,254,1;8,2,201,1" = 0 := by
  change projection (relationPolynomial "13,1,254,1;8,2,201,1") = 0
  exact csv_relation_zero _ relation581_mem
theorem relation582_mem : "0,1,8,1,17,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block4[12]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation582_zero : nativeImage "0,1,8,1,17,1,149,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,17,1,149,1") = 0
  exact csv_relation_zero _ relation582_mem
theorem relation583_mem : "0,1,8,1,16,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block4[27]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation583_zero : nativeImage "0,1,8,1,16,1,149,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,16,1,149,1") = 0
  exact csv_relation_zero _ relation583_mem
theorem relation584_mem : "17,1,224,1;16,1,225,1;0,1,452,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block5[22]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation584_zero : nativeImage "17,1,224,1;16,1,225,1;0,1,452,1" = 0 := by
  change projection (relationPolynomial "17,1,224,1;16,1,225,1;0,1,452,1") = 0
  exact csv_relation_zero _ relation584_mem
theorem relation585_mem : "17,1,223,1;8,4,77,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block6[8]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation585_zero : nativeImage "17,1,223,1;8,4,77,1" = 0 := by
  change projection (relationPolynomial "17,1,223,1;8,4,77,1") = 0
  exact csv_relation_zero _ relation585_mem
theorem relation586_mem : "17,2,117,1;9,1,265,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block6[25]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation586_zero : nativeImage "17,2,117,1;9,1,265,1" = 0 := by
  change projection (relationPolynomial "17,2,117,1;9,1,265,1") = 0
  exact csv_relation_zero _ relation586_mem
theorem relation587_mem : "9,1,265,1;8,1,283,1;0,3,432,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block6[27]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation587_zero : nativeImage "9,1,265,1;8,1,283,1;0,3,432,1" = 0 := by
  change projection (relationPolynomial "9,1,265,1;8,1,283,1;0,3,432,1") = 0
  exact csv_relation_zero _ relation587_mem
theorem relation588_mem : "1,1,69,1,107,1;0,1,2,1,69,1,95,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block7[29]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation588_zero : nativeImage "1,1,69,1,107,1;0,1,2,1,69,1,95,1" = 0 := by
  change projection (relationPolynomial "1,1,69,1,107,1;0,1,2,1,69,1,95,1") = 0
  exact csv_relation_zero _ relation588_mem
theorem relation589_mem : "7,1,310,1;5,1,323,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block9[3]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation589_zero : nativeImage "7,1,310,1;5,1,323,1" = 0 := by
  change projection (relationPolynomial "7,1,310,1;5,1,323,1") = 0
  exact csv_relation_zero _ relation589_mem
theorem relation590_mem : "5,1,323,1;3,1,387,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block9[4]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation590_zero : nativeImage "5,1,323,1;3,1,387,1" = 0 := by
  change projection (relationPolynomial "5,1,323,1;3,1,387,1") = 0
  exact csv_relation_zero _ relation590_mem
theorem relation591_mem : "3,1,387,1;1,2,442,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block9[8]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation591_zero : nativeImage "3,1,387,1;1,2,442,1" = 0 := by
  change projection (relationPolynomial "3,1,387,1;1,2,442,1") = 0
  exact csv_relation_zero _ relation591_mem
theorem relation592_mem : "7,1,309,1;1,1,459,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block9[30]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation592_zero : nativeImage "7,1,309,1;1,1,459,1" = 0 := by
  change projection (relationPolynomial "7,1,309,1;1,1,459,1") = 0
  exact csv_relation_zero _ relation592_mem
theorem relation593_mem : "3,1,410,1;1,1,477,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block21[27]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation593_zero : nativeImage "3,1,410,1;1,1,477,1" = 0 := by
  change projection (relationPolynomial "3,1,410,1;1,1,477,1") = 0
  exact csv_relation_zero _ relation593_mem
theorem relation594_mem : "75,1,107,1;36,1,174,1;33,1,181,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block22[12]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation594_zero : nativeImage "75,1,107,1;36,1,174,1;33,1,181,1" = 0 := by
  change projection (relationPolynomial "75,1,107,1;36,1,174,1;33,1,181,1") = 0
  exact csv_relation_zero _ relation594_mem
theorem relation595_mem : "33,1,181,1;25,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block22[14]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation595_zero : nativeImage "33,1,181,1;25,1,209,1" = 0 := by
  change projection (relationPolynomial "33,1,181,1;25,1,209,1") = 0
  exact csv_relation_zero _ relation595_mem
theorem relation596_mem : "25,1,209,1;13,1,263,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block22[16]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation596_zero : nativeImage "25,1,209,1;13,1,263,1" = 0 := by
  change projection (relationPolynomial "25,1,209,1;13,1,263,1") = 0
  exact csv_relation_zero _ relation596_mem
theorem relation597_mem : "13,1,263,1;9,1,281,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block22[17]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation597_zero : nativeImage "13,1,263,1;9,1,281,1" = 0 := by
  change projection (relationPolynomial "13,1,263,1;9,1,281,1") = 0
  exact csv_relation_zero _ relation597_mem
theorem relation598_mem : "36,1,174,1;3,1,407,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block22[21]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation598_zero : nativeImage "36,1,174,1;3,1,407,1" = 0 := by
  change projection (relationPolynomial "36,1,174,1;3,1,407,1") = 0
  exact csv_relation_zero _ relation598_mem
theorem relation599_mem : "75,1,105,1;32,1,181,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block23[3]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation599_zero : nativeImage "75,1,105,1;32,1,181,1" = 0 := by
  change projection (relationPolynomial "75,1,105,1;32,1,181,1") = 0
  exact csv_relation_zero _ relation599_mem
theorem relation600_mem : "32,1,181,1;24,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block23[5]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation600_zero : nativeImage "32,1,181,1;24,1,209,1" = 0 := by
  change projection (relationPolynomial "32,1,181,1;24,1,209,1") = 0
  exact csv_relation_zero _ relation600_mem
theorem relation601_mem : "24,1,209,1;13,1,262,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block23[7]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation601_zero : nativeImage "24,1,209,1;13,1,262,1" = 0 := by
  change projection (relationPolynomial "24,1,209,1;13,1,262,1") = 0
  exact csv_relation_zero _ relation601_mem
theorem relation602_mem : "23,1,209,1;17,1,235,1;13,1,261,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block23[27]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation602_zero : nativeImage "23,1,209,1;17,1,235,1;13,1,261,1" = 0 := by
  change projection (relationPolynomial "23,1,209,1;17,1,235,1;13,1,261,1") = 0
  exact csv_relation_zero _ relation602_mem
theorem relation603_mem : "17,1,235,1;0,1,481,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block24[1]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation603_zero : nativeImage "17,1,235,1;0,1,481,1" = 0 := by
  change projection (relationPolynomial "17,1,235,1;0,1,481,1") = 0
  exact csv_relation_zero _ relation603_mem
theorem relation604_mem : "22,1,209,1;9,1,280,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block24[12]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation604_zero : nativeImage "22,1,209,1;9,1,280,1" = 0 := by
  change projection (relationPolynomial "22,1,209,1;9,1,280,1") = 0
  exact csv_relation_zero _ relation604_mem
theorem relation605_mem : "9,1,280,1;8,1,294,1;4,1,361,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block24[16]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation605_zero : nativeImage "9,1,280,1;8,1,294,1;4,1,361,1" = 0 := by
  change projection (relationPolynomial "9,1,280,1;8,1,294,1;4,1,361,1") = 0
  exact csv_relation_zero _ relation605_mem
theorem relation606_mem : "4,1,361,1;1,2,448,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block24[18]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation606_zero : nativeImage "4,1,361,1;1,2,448,1" = 0 := by
  change projection (relationPolynomial "4,1,361,1;1,2,448,1") = 0
  exact csv_relation_zero _ relation606_mem
theorem relation607_mem : "13,1,260,1;12,1,266,1;9,1,278,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block26[9]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation607_zero : nativeImage "13,1,260,1;12,1,266,1;9,1,278,1" = 0 := by
  change projection (relationPolynomial "13,1,260,1;12,1,266,1;9,1,278,1") = 0
  exact csv_relation_zero _ relation607_mem
theorem relation608_mem : "9,1,278,1;8,1,291,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block26[10]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation608_zero : nativeImage "9,1,278,1;8,1,291,1" = 0 := by
  change projection (relationPolynomial "9,1,278,1;8,1,291,1") = 0
  exact csv_relation_zero _ relation608_mem
theorem relation609_mem : "29,1,194,1;23,1,208,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block26[24]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation609_zero : nativeImage "29,1,194,1;23,1,208,1" = 0 := by
  change projection (relationPolynomial "29,1,194,1;23,1,208,1") = 0
  exact csv_relation_zero _ relation609_mem
theorem relation610_mem : "23,1,208,1;9,1,13,1,167,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block26[28]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation610_zero : nativeImage "23,1,208,1;9,1,13,1,167,1" = 0 := by
  change projection (relationPolynomial "23,1,208,1;9,1,13,1,167,1") = 0
  exact csv_relation_zero _ relation610_mem
theorem relation611_mem : "20,1,219,1;8,1,9,1,194,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block27[11]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation611_zero : nativeImage "20,1,219,1;8,1,9,1,194,1" = 0 := by
  change projection (relationPolynomial "20,1,219,1;8,1,9,1,194,1") = 0
  exact csv_relation_zero _ relation611_mem
theorem relation612_mem : "17,1,233,1;13,1,259,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block27[28]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation612_zero : nativeImage "17,1,233,1;13,1,259,1" = 0 := by
  change projection (relationPolynomial "17,1,233,1;13,1,259,1") = 0
  exact csv_relation_zero _ relation612_mem
theorem relation613_mem : "13,1,259,1;8,2,208,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block27[29]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation613_zero : nativeImage "13,1,259,1;8,2,208,1" = 0 := by
  change projection (relationPolynomial "13,1,259,1;8,2,208,1") = 0
  exact csv_relation_zero _ relation613_mem
theorem relation614_mem : "17,1,232,1;16,1,233,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block28[8]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation614_zero : nativeImage "17,1,232,1;16,1,233,1" = 0 := by
  change projection (relationPolynomial "17,1,232,1;16,1,233,1") = 0
  exact csv_relation_zero _ relation614_mem
theorem relation615_mem : "16,1,233,1;13,1,258,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block28[9]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation615_zero : nativeImage "16,1,233,1;13,1,258,1" = 0 := by
  change projection (relationPolynomial "16,1,233,1;13,1,258,1") = 0
  exact csv_relation_zero _ relation615_mem
theorem relation616_mem : "13,1,258,1;9,1,277,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block28[10]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation616_zero : nativeImage "13,1,258,1;9,1,277,1" = 0 := by
  change projection (relationPolynomial "13,1,258,1;9,1,277,1") = 0
  exact csv_relation_zero _ relation616_mem
theorem relation617_mem : "9,1,277,1;8,2,207,1" ∈ LinE2.RawData.relations := by
  exact relation_member 11 chunkBound rows transcription
    (block28[11]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation617_zero : nativeImage "9,1,277,1;8,2,207,1" = 0 := by
  change projection (relationPolynomial "9,1,277,1;8,2,207,1") = 0
  exact csv_relation_zero _ relation617_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk011
