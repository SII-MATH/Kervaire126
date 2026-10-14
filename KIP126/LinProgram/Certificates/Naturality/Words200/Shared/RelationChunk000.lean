module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk000
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[0]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 0 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[0]'(chunkBound) =
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
private theorem block27_mem : block27 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 27) (by decide)
private theorem block27_in_rows (r : List Char) (hr : r ∈ block27) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block27, block27_mem, hr⟩
private theorem block29_mem : block29 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 29) (by decide)
private theorem block29_in_rows (r : List Char) (hr : r ∈ block29) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block29, block29_mem, hr⟩
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
theorem relation2_mem : "2,1,3,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[2]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation2_zero : nativeImage "2,1,3,1" = 0 := by
  change projection (relationPolynomial "2,1,3,1") = 0
  exact csv_relation_zero _ relation2_mem
theorem relation3_mem : "2,3;1,2,3,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[3]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation3_zero : nativeImage "2,3;1,2,3,1" = 0 := by
  change projection (relationPolynomial "2,3;1,2,3,1") = 0
  exact csv_relation_zero _ relation3_mem
theorem relation4_mem : "0,1,4,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[4]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation4_zero : nativeImage "0,1,4,1" = 0 := by
  change projection (relationPolynomial "0,1,4,1") = 0
  exact csv_relation_zero _ relation4_mem
theorem relation5_mem : "0,4,3,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[5]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation5_zero : nativeImage "0,4,3,1" = 0 := by
  change projection (relationPolynomial "0,4,3,1") = 0
  exact csv_relation_zero _ relation5_mem
theorem relation6_mem : "0,1,5,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[8]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation6_zero : nativeImage "0,1,5,1" = 0 := by
  change projection (relationPolynomial "0,1,5,1") = 0
  exact csv_relation_zero _ relation6_mem
theorem relation7_mem : "1,1,3,2" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[9]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation7_zero : nativeImage "1,1,3,2" = 0 := by
  change projection (relationPolynomial "1,1,3,2") = 0
  exact csv_relation_zero _ relation7_mem
theorem relation8_mem : "0,2,3,2" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[10]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation8_zero : nativeImage "0,2,3,2" = 0 := by
  change projection (relationPolynomial "0,2,3,2") = 0
  exact csv_relation_zero _ relation8_mem
theorem relation9_mem : "1,1,6,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[12]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation9_zero : nativeImage "1,1,6,1" = 0 := by
  change projection (relationPolynomial "1,1,6,1") = 0
  exact csv_relation_zero _ relation9_mem
theorem relation10_mem : "0,3,8,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[17]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation10_zero : nativeImage "0,3,8,1" = 0 := by
  change projection (relationPolynomial "0,3,8,1") = 0
  exact csv_relation_zero _ relation10_mem
theorem relation11_mem : "2,1,8,1;0,1,9,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[18]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation11_zero : nativeImage "2,1,8,1;0,1,9,1" = 0 := by
  change projection (relationPolynomial "2,1,8,1;0,1,9,1") = 0
  exact csv_relation_zero _ relation11_mem
theorem relation12_mem : "3,1,7,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[23]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation12_zero : nativeImage "3,1,7,1" = 0 := by
  change projection (relationPolynomial "3,1,7,1") = 0
  exact csv_relation_zero _ relation12_mem
theorem relation13_mem : "0,1,12,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block0[29]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation13_zero : nativeImage "0,1,12,1" = 0 := by
  change projection (relationPolynomial "0,1,12,1") = 0
  exact csv_relation_zero _ relation13_mem
theorem relation14_mem : "0,4,9,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block1[1]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation14_zero : nativeImage "0,4,9,1" = 0 := by
  change projection (relationPolynomial "0,4,9,1") = 0
  exact csv_relation_zero _ relation14_mem
theorem relation15_mem : "3,1,8,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block1[2]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation15_zero : nativeImage "3,1,8,1" = 0 := by
  change projection (relationPolynomial "3,1,8,1") = 0
  exact csv_relation_zero _ relation15_mem
theorem relation16_mem : "2,1,10,1;1,1,13,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block1[3]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation16_zero : nativeImage "2,1,10,1;1,1,13,1" = 0 := by
  change projection (relationPolynomial "2,1,10,1;1,1,13,1") = 0
  exact csv_relation_zero _ relation16_mem
theorem relation17_mem : "0,3,13,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block1[4]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation17_zero : nativeImage "0,3,13,1" = 0 := by
  change projection (relationPolynomial "0,3,13,1") = 0
  exact csv_relation_zero _ relation17_mem
theorem relation18_mem : "0,1,14,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block1[8]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation18_zero : nativeImage "0,1,14,1" = 0 := by
  change projection (relationPolynomial "0,1,14,1") = 0
  exact csv_relation_zero _ relation18_mem
theorem relation19_mem : "3,1,9,1;1,1,4,1,7,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block1[11]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation19_zero : nativeImage "3,1,9,1;1,1,4,1,7,1" = 0 := by
  change projection (relationPolynomial "3,1,9,1;1,1,4,1,7,1") = 0
  exact csv_relation_zero _ relation19_mem
theorem relation20_mem : "4,1,8,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block1[12]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation20_zero : nativeImage "4,1,8,1" = 0 := by
  change projection (relationPolynomial "4,1,8,1") = 0
  exact csv_relation_zero _ relation20_mem
theorem relation21_mem : "5,1,7,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block1[16]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation21_zero : nativeImage "5,1,7,1" = 0 := by
  change projection (relationPolynomial "5,1,7,1") = 0
  exact csv_relation_zero _ relation21_mem
theorem relation22_mem : "3,1,13,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block1[24]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation22_zero : nativeImage "3,1,13,1" = 0 := by
  change projection (relationPolynomial "3,1,13,1") = 0
  exact csv_relation_zero _ relation22_mem
theorem relation23_mem : "1,1,17,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block1[27]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation23_zero : nativeImage "1,1,17,1" = 0 := by
  change projection (relationPolynomial "1,1,17,1") = 0
  exact csv_relation_zero _ relation23_mem
theorem relation24_mem : "5,1,8,1;1,1,16,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block1[28]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation24_zero : nativeImage "5,1,8,1;1,1,16,1" = 0 := by
  change projection (relationPolynomial "5,1,8,1;1,1,16,1") = 0
  exact csv_relation_zero _ relation24_mem
theorem relation25_mem : "0,3,16,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block2[1]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation25_zero : nativeImage "0,3,16,1" = 0 := by
  change projection (relationPolynomial "0,3,16,1") = 0
  exact csv_relation_zero _ relation25_mem
theorem relation26_mem : "7,1,8,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block2[2]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation26_zero : nativeImage "7,1,8,1" = 0 := by
  change projection (relationPolynomial "7,1,8,1") = 0
  exact csv_relation_zero _ relation26_mem
theorem relation27_mem : "6,1,8,1;2,1,16,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block2[4]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation27_zero : nativeImage "6,1,8,1;2,1,16,1" = 0 := by
  change projection (relationPolynomial "6,1,8,1;2,1,16,1") = 0
  exact csv_relation_zero _ relation27_mem
theorem relation28_mem : "2,1,16,1;0,1,19,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block2[5]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation28_zero : nativeImage "2,1,16,1;0,1,19,1" = 0 := by
  change projection (relationPolynomial "2,1,16,1;0,1,19,1") = 0
  exact csv_relation_zero _ relation28_mem
theorem relation29_mem : "0,3,20,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block2[18]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation29_zero : nativeImage "0,3,20,1" = 0 := by
  change projection (relationPolynomial "0,3,20,1") = 0
  exact csv_relation_zero _ relation29_mem
theorem relation30_mem : "0,1,25,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block2[22]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation30_zero : nativeImage "0,1,25,1" = 0 := by
  change projection (relationPolynomial "0,1,25,1") = 0
  exact csv_relation_zero _ relation30_mem
theorem relation31_mem : "1,1,8,2;0,2,22,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block3[9]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation31_zero : nativeImage "1,1,8,2;0,2,22,1" = 0 := by
  change projection (relationPolynomial "1,1,8,2;0,2,22,1") = 0
  exact csv_relation_zero _ relation31_mem
theorem relation32_mem : "1,1,26,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block3[10]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation32_zero : nativeImage "1,1,26,1" = 0 := by
  change projection (relationPolynomial "1,1,26,1") = 0
  exact csv_relation_zero _ relation32_mem
theorem relation33_mem : "0,2,26,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block3[11]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation33_zero : nativeImage "0,2,26,1" = 0 := by
  change projection (relationPolynomial "0,2,26,1") = 0
  exact csv_relation_zero _ relation33_mem
theorem relation34_mem : "0,1,28,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block3[12]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation34_zero : nativeImage "0,1,28,1" = 0 := by
  change projection (relationPolynomial "0,1,28,1") = 0
  exact csv_relation_zero _ relation34_mem
theorem relation35_mem : "0,3,22,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block3[14]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation35_zero : nativeImage "0,3,22,1" = 0 := by
  change projection (relationPolynomial "0,3,22,1") = 0
  exact csv_relation_zero _ relation35_mem
theorem relation36_mem : "0,1,27,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block3[19]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation36_zero : nativeImage "0,1,27,1" = 0 := by
  change projection (relationPolynomial "0,1,27,1") = 0
  exact csv_relation_zero _ relation36_mem
theorem relation37_mem : "7,1,13,1;2,1,25,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block3[20]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation37_zero : nativeImage "7,1,13,1;2,1,25,1" = 0 := by
  change projection (relationPolynomial "7,1,13,1;2,1,25,1") = 0
  exact csv_relation_zero _ relation37_mem
theorem relation38_mem : "2,1,23,1;1,1,28,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block3[22]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation38_zero : nativeImage "2,1,23,1;1,1,28,1" = 0 := by
  change projection (relationPolynomial "2,1,23,1;1,1,28,1") = 0
  exact csv_relation_zero _ relation38_mem
theorem relation39_mem : "8,1,10,1;2,1,22,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block3[23]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation39_zero : nativeImage "8,1,10,1;2,1,22,1" = 0 := by
  change projection (relationPolynomial "8,1,10,1;2,1,22,1") = 0
  exact csv_relation_zero _ relation39_mem
theorem relation40_mem : "2,1,22,1;0,1,29,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block3[24]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation40_zero : nativeImage "2,1,22,1;0,1,29,1" = 0 := by
  change projection (relationPolynomial "2,1,22,1;0,1,29,1") = 0
  exact csv_relation_zero _ relation40_mem
theorem relation41_mem : "3,1,20,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block3[28]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation41_zero : nativeImage "3,1,20,1" = 0 := by
  change projection (relationPolynomial "3,1,20,1") = 0
  exact csv_relation_zero _ relation41_mem
theorem relation42_mem : "8,1,12,1;4,1,16,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block4[0]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation42_zero : nativeImage "8,1,12,1;4,1,16,1" = 0 := by
  change projection (relationPolynomial "8,1,12,1;4,1,16,1") = 0
  exact csv_relation_zero _ relation42_mem
theorem relation43_mem : "4,1,16,1;0,5,23,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block4[1]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation43_zero : nativeImage "4,1,16,1;0,5,23,1" = 0 := by
  change projection (relationPolynomial "4,1,16,1;0,5,23,1") = 0
  exact csv_relation_zero _ relation43_mem
theorem relation44_mem : "9,2;8,1,13,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block4[3]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation44_zero : nativeImage "9,2;8,1,13,1" = 0 := by
  change projection (relationPolynomial "9,2;8,1,13,1") = 0
  exact csv_relation_zero _ relation44_mem
theorem relation45_mem : "2,2,25,1;1,1,34,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block4[24]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation45_zero : nativeImage "2,2,25,1;1,1,34,1" = 0 := by
  change projection (relationPolynomial "2,2,25,1;1,1,34,1") = 0
  exact csv_relation_zero _ relation45_mem
theorem relation46_mem : "2,2,24,1;1,1,33,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block4[26]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation46_zero : nativeImage "2,2,24,1;1,1,33,1" = 0 := by
  change projection (relationPolynomial "2,2,24,1;1,1,33,1") = 0
  exact csv_relation_zero _ relation46_mem
theorem relation47_mem : "4,1,20,1;0,2,8,1,13,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block5[1]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation47_zero : nativeImage "4,1,20,1;0,2,8,1,13,1" = 0 := by
  change projection (relationPolynomial "4,1,20,1;0,2,8,1,13,1") = 0
  exact csv_relation_zero _ relation47_mem
theorem relation48_mem : "8,1,14,1;5,1,16,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block5[5]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation48_zero : nativeImage "8,1,14,1;5,1,16,1" = 0 := by
  change projection (relationPolynomial "8,1,14,1;5,1,16,1") = 0
  exact csv_relation_zero _ relation48_mem
theorem relation49_mem : "5,1,16,1;1,1,31,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block5[6]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation49_zero : nativeImage "5,1,16,1;1,1,31,1" = 0 := by
  change projection (relationPolynomial "5,1,16,1;1,1,31,1") = 0
  exact csv_relation_zero _ relation49_mem
theorem relation50_mem : "0,3,31,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block5[13]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation50_zero : nativeImage "0,3,31,1" = 0 := by
  change projection (relationPolynomial "0,3,31,1") = 0
  exact csv_relation_zero _ relation50_mem
theorem relation51_mem : "2,1,33,1;1,1,36,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block5[21]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation51_zero : nativeImage "2,1,33,1;1,1,36,1" = 0 := by
  change projection (relationPolynomial "2,1,33,1;1,1,36,1") = 0
  exact csv_relation_zero _ relation51_mem
theorem relation52_mem : "0,1,9,1,13,1;0,4,34,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block5[28]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation52_zero : nativeImage "0,1,9,1,13,1;0,4,34,1" = 0 := by
  change projection (relationPolynomial "0,1,9,1,13,1;0,4,34,1") = 0
  exact csv_relation_zero _ relation52_mem
theorem relation53_mem : "8,1,15,1;6,1,16,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block5[30]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation53_zero : nativeImage "8,1,15,1;6,1,16,1" = 0 := by
  change projection (relationPolynomial "8,1,15,1;6,1,16,1") = 0
  exact csv_relation_zero _ relation53_mem
theorem relation54_mem : "6,1,16,1;2,1,31,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block5[31]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation54_zero : nativeImage "6,1,16,1;2,1,31,1" = 0 := by
  change projection (relationPolynomial "6,1,16,1;2,1,31,1") = 0
  exact csv_relation_zero _ relation54_mem
theorem relation55_mem : "2,1,31,1;0,1,39,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block6[0]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation55_zero : nativeImage "2,1,31,1;0,1,39,1" = 0 := by
  change projection (relationPolynomial "2,1,31,1;0,1,39,1") = 0
  exact csv_relation_zero _ relation55_mem
theorem relation56_mem : "3,1,29,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block6[8]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation56_zero : nativeImage "3,1,29,1" = 0 := by
  change projection (relationPolynomial "3,1,29,1") = 0
  exact csv_relation_zero _ relation56_mem
theorem relation57_mem : "4,1,22,1;0,5,34,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block6[10]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation57_zero : nativeImage "4,1,22,1;0,5,34,1" = 0 := by
  change projection (relationPolynomial "4,1,22,1;0,5,34,1") = 0
  exact csv_relation_zero _ relation57_mem
theorem relation58_mem : "12,1,13,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block6[11]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation58_zero : nativeImage "12,1,13,1" = 0 := by
  change projection (relationPolynomial "12,1,13,1") = 0
  exact csv_relation_zero _ relation58_mem
theorem relation59_mem : "7,1,18,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block6[17]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation59_zero : nativeImage "7,1,18,1" = 0 := by
  change projection (relationPolynomial "7,1,18,1") = 0
  exact csv_relation_zero _ relation59_mem
theorem relation60_mem : "0,1,13,2" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block7[3]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation60_zero : nativeImage "0,1,13,2" = 0 := by
  change projection (relationPolynomial "0,1,13,2") = 0
  exact csv_relation_zero _ relation60_mem
theorem relation61_mem : "3,1,33,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block7[16]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation61_zero : nativeImage "3,1,33,1" = 0 := by
  change projection (relationPolynomial "3,1,33,1") = 0
  exact csv_relation_zero _ relation61_mem
theorem relation62_mem : "3,1,32,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block7[17]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation62_zero : nativeImage "3,1,32,1" = 0 := by
  change projection (relationPolynomial "3,1,32,1") = 0
  exact csv_relation_zero _ relation62_mem
theorem relation63_mem : "1,1,8,1,16,1;0,2,8,1,17,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block7[28]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation63_zero : nativeImage "1,1,8,1,16,1;0,2,8,1,17,1" = 0 := by
  change projection (relationPolynomial "1,1,8,1,16,1;0,2,8,1,17,1") = 0
  exact csv_relation_zero _ relation63_mem
theorem relation64_mem : "9,1,17,1;8,1,20,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block7[31]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation64_zero : nativeImage "9,1,17,1;8,1,20,1" = 0 := by
  change projection (relationPolynomial "9,1,17,1;8,1,20,1") = 0
  exact csv_relation_zero _ relation64_mem
theorem relation65_mem : "9,1,16,1;8,1,19,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block8[0]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation65_zero : nativeImage "9,1,16,1;8,1,19,1" = 0 := by
  change projection (relationPolynomial "9,1,16,1;8,1,19,1") = 0
  exact csv_relation_zero _ relation65_mem
theorem relation66_mem : "1,2,43,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block8[11]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation66_zero : nativeImage "1,2,43,1" = 0 := by
  change projection (relationPolynomial "1,2,43,1") = 0
  exact csv_relation_zero _ relation66_mem
theorem relation67_mem : "0,1,48,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block9[19]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation67_zero : nativeImage "0,1,48,1" = 0 := by
  change projection (relationPolynomial "0,1,48,1") = 0
  exact csv_relation_zero _ relation67_mem
theorem relation68_mem : "8,1,24,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block9[20]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation68_zero : nativeImage "8,1,24,1" = 0 := by
  change projection (relationPolynomial "8,1,24,1") = 0
  exact csv_relation_zero _ relation68_mem
theorem relation69_mem : "13,1,17,1;9,1,20,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block9[21]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation69_zero : nativeImage "13,1,17,1;9,1,20,1" = 0 := by
  change projection (relationPolynomial "13,1,17,1;9,1,20,1") = 0
  exact csv_relation_zero _ relation69_mem
theorem relation70_mem : "9,1,20,1;8,1,22,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block9[22]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation70_zero : nativeImage "9,1,20,1;8,1,22,1" = 0 := by
  change projection (relationPolynomial "9,1,20,1;8,1,22,1") = 0
  exact csv_relation_zero _ relation70_mem
theorem relation71_mem : "13,1,16,1;9,1,19,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block9[24]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation71_zero : nativeImage "13,1,16,1;9,1,19,1" = 0 := by
  change projection (relationPolynomial "13,1,16,1;9,1,19,1") = 0
  exact csv_relation_zero _ relation71_mem
theorem relation72_mem : "9,1,19,1;8,3" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block9[25]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation72_zero : nativeImage "9,1,19,1;8,3" = 0 := by
  change projection (relationPolynomial "9,1,19,1;8,3") = 0
  exact csv_relation_zero _ relation72_mem
theorem relation73_mem : "0,1,51,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block10[9]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation73_zero : nativeImage "0,1,51,1" = 0 := by
  change projection (relationPolynomial "0,1,51,1") = 0
  exact csv_relation_zero _ relation73_mem
theorem relation74_mem : "0,1,8,1,23,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block10[13]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation74_zero : nativeImage "0,1,8,1,23,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,23,1") = 0
  exact csv_relation_zero _ relation74_mem
theorem relation75_mem : "13,1,18,1;3,1,43,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block10[18]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation75_zero : nativeImage "13,1,18,1;3,1,43,1" = 0 := by
  change projection (relationPolynomial "13,1,18,1;3,1,43,1") = 0
  exact csv_relation_zero _ relation75_mem
theorem relation76_mem : "8,1,28,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block10[23]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation76_zero : nativeImage "8,1,28,1" = 0 := by
  change projection (relationPolynomial "8,1,28,1") = 0
  exact csv_relation_zero _ relation76_mem
theorem relation77_mem : "5,1,31,1;1,1,49,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block11[7]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation77_zero : nativeImage "5,1,31,1;1,1,49,1" = 0 := by
  change projection (relationPolynomial "5,1,31,1;1,1,49,1") = 0
  exact csv_relation_zero _ relation77_mem
theorem relation78_mem : "13,1,20,1;9,1,22,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block11[17]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation78_zero : nativeImage "13,1,20,1;9,1,22,1" = 0 := by
  change projection (relationPolynomial "13,1,20,1;9,1,22,1") = 0
  exact csv_relation_zero _ relation78_mem
theorem relation79_mem : "9,1,22,1;8,1,29,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block11[18]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation79_zero : nativeImage "9,1,22,1;8,1,29,1" = 0 := by
  change projection (relationPolynomial "9,1,22,1;8,1,29,1") = 0
  exact csv_relation_zero _ relation79_mem
theorem relation80_mem : "0,1,9,1,23,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block12[16]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation80_zero : nativeImage "0,1,9,1,23,1" = 0 := by
  change projection (relationPolynomial "0,1,9,1,23,1") = 0
  exact csv_relation_zero _ relation80_mem
theorem relation81_mem : "0,1,8,2,9,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block12[20]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation81_zero : nativeImage "0,1,8,2,9,1" = 0 := by
  change projection (relationPolynomial "0,1,8,2,9,1") = 0
  exact csv_relation_zero _ relation81_mem
theorem relation82_mem : "8,1,30,1;6,1,31,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block12[24]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation82_zero : nativeImage "8,1,30,1;6,1,31,1" = 0 := by
  change projection (relationPolynomial "8,1,30,1;6,1,31,1") = 0
  exact csv_relation_zero _ relation82_mem
theorem relation83_mem : "6,1,31,1;2,1,49,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block12[25]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation83_zero : nativeImage "6,1,31,1;2,1,49,1" = 0 := by
  change projection (relationPolynomial "6,1,31,1;2,1,49,1") = 0
  exact csv_relation_zero _ relation83_mem
theorem relation84_mem : "2,1,49,1;0,1,55,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block12[26]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation84_zero : nativeImage "2,1,49,1;0,1,55,1" = 0 := by
  change projection (relationPolynomial "2,1,49,1;0,1,55,1") = 0
  exact csv_relation_zero _ relation84_mem
theorem relation85_mem : "8,1,34,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block13[25]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation85_zero : nativeImage "8,1,34,1" = 0 := by
  change projection (relationPolynomial "8,1,34,1") = 0
  exact csv_relation_zero _ relation85_mem
theorem relation86_mem : "13,1,22,1;9,1,29,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block14[0]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation86_zero : nativeImage "13,1,22,1;9,1,29,1" = 0 := by
  change projection (relationPolynomial "13,1,22,1;9,1,29,1") = 0
  exact csv_relation_zero _ relation86_mem
theorem relation87_mem : "9,1,29,1;8,1,32,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block14[1]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation87_zero : nativeImage "9,1,29,1;8,1,32,1" = 0 := by
  change projection (relationPolynomial "9,1,29,1;8,1,32,1") = 0
  exact csv_relation_zero _ relation87_mem
theorem relation88_mem : "16,2;8,1,31,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block14[4]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation88_zero : nativeImage "16,2;8,1,31,1" = 0 := by
  change projection (relationPolynomial "16,2;8,1,31,1") = 0
  exact csv_relation_zero _ relation88_mem
theorem relation89_mem : "0,1,8,2,13,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block14[21]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation89_zero : nativeImage "0,1,8,2,13,1" = 0 := by
  change projection (relationPolynomial "0,1,8,2,13,1") = 0
  exact csv_relation_zero _ relation89_mem
theorem relation90_mem : "2,1,55,1;0,1,8,1,31,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block14[29]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation90_zero : nativeImage "2,1,55,1;0,1,8,1,31,1" = 0 := by
  change projection (relationPolynomial "2,1,55,1;0,1,8,1,31,1") = 0
  exact csv_relation_zero _ relation90_mem
theorem relation91_mem : "1,1,60,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block15[15]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation91_zero : nativeImage "1,1,60,1" = 0 := by
  change projection (relationPolynomial "1,1,60,1") = 0
  exact csv_relation_zero _ relation91_mem
theorem relation92_mem : "13,1,29,1;9,1,32,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block15[31]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation92_zero : nativeImage "13,1,29,1;9,1,32,1" = 0 := by
  change projection (relationPolynomial "13,1,29,1;9,1,32,1") = 0
  exact csv_relation_zero _ relation92_mem
theorem relation93_mem : "17,1,19,1;16,1,20,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block16[1]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation93_zero : nativeImage "17,1,19,1;16,1,20,1" = 0 := by
  change projection (relationPolynomial "17,1,19,1;16,1,20,1") = 0
  exact csv_relation_zero _ relation93_mem
theorem relation94_mem : "16,1,20,1;8,1,40,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block16[2]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation94_zero : nativeImage "16,1,20,1;8,1,40,1" = 0 := by
  change projection (relationPolynomial "16,1,20,1;8,1,40,1") = 0
  exact csv_relation_zero _ relation94_mem
theorem relation95_mem : "16,1,19,1;9,1,31,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block16[3]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation95_zero : nativeImage "16,1,19,1;9,1,31,1" = 0 := by
  change projection (relationPolynomial "16,1,19,1;9,1,31,1") = 0
  exact csv_relation_zero _ relation95_mem
theorem relation96_mem : "9,1,31,1;8,1,39,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block16[4]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation96_zero : nativeImage "9,1,31,1;8,1,39,1" = 0 := by
  change projection (relationPolynomial "9,1,31,1;8,1,39,1") = 0
  exact csv_relation_zero _ relation96_mem
theorem relation97_mem : "17,1,24,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block18[26]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation97_zero : nativeImage "17,1,24,1" = 0 := by
  change projection (relationPolynomial "17,1,24,1") = 0
  exact csv_relation_zero _ relation97_mem
theorem relation98_mem : "17,1,23,1;8,1,42,1;0,3,64,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block18[29]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation98_zero : nativeImage "17,1,23,1;8,1,42,1;0,3,64,1" = 0 := by
  change projection (relationPolynomial "17,1,23,1;8,1,42,1;0,3,64,1") = 0
  exact csv_relation_zero _ relation98_mem
theorem relation99_mem : "17,1,22,1;16,1,23,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block18[31]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation99_zero : nativeImage "17,1,22,1;16,1,23,1" = 0 := by
  change projection (relationPolynomial "17,1,22,1;16,1,23,1") = 0
  exact csv_relation_zero _ relation99_mem
theorem relation100_mem : "2,1,64,1;0,1,72,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block19[23]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation100_zero : nativeImage "2,1,64,1;0,1,72,1" = 0 := by
  change projection (relationPolynomial "2,1,64,1;0,1,72,1") = 0
  exact csv_relation_zero _ relation100_mem
theorem relation101_mem : "0,1,76,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block20[9]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation101_zero : nativeImage "0,1,76,1" = 0 := by
  change projection (relationPolynomial "0,1,76,1") = 0
  exact csv_relation_zero _ relation101_mem
theorem relation102_mem : "8,2,18,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block20[18]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation102_zero : nativeImage "8,2,18,1" = 0 := by
  change projection (relationPolynomial "8,2,18,1") = 0
  exact csv_relation_zero _ relation102_mem
theorem relation103_mem : "2,1,66,1;1,1,72,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block20[20]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation103_zero : nativeImage "2,1,66,1;1,1,72,1" = 0 := by
  change projection (relationPolynomial "2,1,66,1;1,1,72,1") = 0
  exact csv_relation_zero _ relation103_mem
theorem relation104_mem : "1,1,8,1,42,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block20[29]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation104_zero : nativeImage "1,1,8,1,42,1" = 0 := by
  change projection (relationPolynomial "1,1,8,1,42,1") = 0
  exact csv_relation_zero _ relation104_mem
theorem relation105_mem : "0,2,75,1;0,2,74,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block21[25]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation105_zero : nativeImage "0,2,75,1;0,2,74,1" = 0 := by
  change projection (relationPolynomial "0,2,75,1;0,2,74,1") = 0
  exact csv_relation_zero _ relation105_mem
theorem relation106_mem : "20,1,23,1;9,1,42,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block22[0]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation106_zero : nativeImage "20,1,23,1;9,1,42,1" = 0 := by
  change projection (relationPolynomial "20,1,23,1;9,1,42,1") = 0
  exact csv_relation_zero _ relation106_mem
theorem relation107_mem : "9,1,42,1;8,1,46,1;0,3,72,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block22[1]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation107_zero : nativeImage "9,1,42,1;8,1,46,1;0,3,72,1" = 0 := by
  change projection (relationPolynomial "9,1,42,1;8,1,46,1;0,3,72,1") = 0
  exact csv_relation_zero _ relation107_mem
theorem relation108_mem : "17,1,29,1;8,1,45,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block22[4]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation108_zero : nativeImage "17,1,29,1;8,1,45,1" = 0 := by
  change projection (relationPolynomial "17,1,29,1;8,1,45,1") = 0
  exact csv_relation_zero _ relation108_mem
theorem relation109_mem : "0,3,74,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block22[16]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation109_zero : nativeImage "0,3,74,1" = 0 := by
  change projection (relationPolynomial "0,3,74,1") = 0
  exact csv_relation_zero _ relation109_mem
theorem relation110_mem : "0,1,8,2,19,1;0,7,64,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block23[9]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation110_zero : nativeImage "0,1,8,2,19,1;0,7,64,1" = 0 := by
  change projection (relationPolynomial "0,1,8,2,19,1;0,7,64,1") = 0
  exact csv_relation_zero _ relation110_mem
theorem relation111_mem : "8,1,9,1,18,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block23[27]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation111_zero : nativeImage "8,1,9,1,18,1" = 0 := by
  change projection (relationPolynomial "8,1,9,1,18,1") = 0
  exact csv_relation_zero _ relation111_mem
theorem relation112_mem : "0,1,83,1;0,1,82,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block23[29]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation112_zero : nativeImage "0,1,83,1;0,1,82,1" = 0 := by
  change projection (relationPolynomial "0,1,83,1;0,1,82,1") = 0
  exact csv_relation_zero _ relation112_mem
theorem relation113_mem : "0,1,82,1;0,7,18,2" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block23[30]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation113_zero : nativeImage "0,1,82,1;0,7,18,2" = 0 := by
  change projection (relationPolynomial "0,1,82,1;0,7,18,2") = 0
  exact csv_relation_zero _ relation113_mem
theorem relation114_mem : "8,1,48,1;1,1,79,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block24[2]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation114_zero : nativeImage "8,1,48,1;1,1,79,1" = 0 := by
  change projection (relationPolynomial "8,1,48,1;1,1,79,1") = 0
  exact csv_relation_zero _ relation114_mem
theorem relation115_mem : "3,1,64,1;1,1,79,1;0,2,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block24[3]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation115_zero : nativeImage "3,1,64,1;1,1,79,1;0,2,80,1" = 0 := by
  change projection (relationPolynomial "3,1,64,1;1,1,79,1;0,2,80,1") = 0
  exact csv_relation_zero _ relation115_mem
theorem relation116_mem : "0,8,18,2" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block25[5]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation116_zero : nativeImage "0,8,18,2" = 0 := by
  change projection (relationPolynomial "0,8,18,2") = 0
  exact csv_relation_zero _ relation116_mem
theorem relation117_mem : "23,2;17,1,34,1;13,3" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block25[13]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation117_zero : nativeImage "23,2;17,1,34,1;13,3" = 0 := by
  change projection (relationPolynomial "23,2;17,1,34,1;13,3") = 0
  exact csv_relation_zero _ relation117_mem
theorem relation118_mem : "17,1,34,1;0,3,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block25[15]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation118_zero : nativeImage "17,1,34,1;0,3,80,1" = 0 := by
  change projection (relationPolynomial "17,1,34,1;0,3,80,1") = 0
  exact csv_relation_zero _ relation118_mem
theorem relation119_mem : "22,1,23,1;13,1,42,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block25[19]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation119_zero : nativeImage "22,1,23,1;13,1,42,1" = 0 := by
  change projection (relationPolynomial "22,1,23,1;13,1,42,1") = 0
  exact csv_relation_zero _ relation119_mem
theorem relation120_mem : "13,1,42,1;9,1,46,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block25[20]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation120_zero : nativeImage "13,1,42,1;9,1,46,1" = 0 := by
  change projection (relationPolynomial "13,1,42,1;9,1,46,1") = 0
  exact csv_relation_zero _ relation120_mem
theorem relation121_mem : "9,1,46,1;8,1,51,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block25[21]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation121_zero : nativeImage "9,1,46,1;8,1,51,1" = 0 := by
  change projection (relationPolynomial "9,1,46,1;8,1,51,1") = 0
  exact csv_relation_zero _ relation121_mem
theorem relation122_mem : "17,1,32,1;9,1,45,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block25[27]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation122_zero : nativeImage "17,1,32,1;9,1,45,1" = 0 := by
  change projection (relationPolynomial "17,1,32,1;9,1,45,1") = 0
  exact csv_relation_zero _ relation122_mem
theorem relation123_mem : "9,1,45,1;8,2,23,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block25[28]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation123_zero : nativeImage "9,1,45,1;8,2,23,1" = 0 := by
  change projection (relationPolynomial "9,1,45,1;8,2,23,1") = 0
  exact csv_relation_zero _ relation123_mem
theorem relation124_mem : "17,1,31,1;8,1,50,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block26[2]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation124_zero : nativeImage "17,1,31,1;8,1,50,1" = 0 := by
  change projection (relationPolynomial "17,1,31,1;8,1,50,1") = 0
  exact csv_relation_zero _ relation124_mem
theorem relation125_mem : "0,1,8,4" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block27[0]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation125_zero : nativeImage "0,1,8,4" = 0 := by
  change projection (relationPolynomial "0,1,8,4") = 0
  exact csv_relation_zero _ relation125_mem
theorem relation126_mem : "4,1,18,2;1,1,96,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block29[5]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation126_zero : nativeImage "4,1,18,2;1,1,96,1" = 0 := by
  change projection (relationPolynomial "4,1,18,2;1,1,96,1") = 0
  exact csv_relation_zero _ relation126_mem
theorem relation127_mem : "2,2,75,1;1,1,95,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block29[9]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation127_zero : nativeImage "2,2,75,1;1,1,95,1" = 0 := by
  change projection (relationPolynomial "2,2,75,1;1,1,95,1") = 0
  exact csv_relation_zero _ relation127_mem
theorem relation128_mem : "0,2,2,1,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block29[25]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation128_zero : nativeImage "0,2,2,1,80,1" = 0 := by
  change projection (relationPolynomial "0,2,2,1,80,1") = 0
  exact csv_relation_zero _ relation128_mem
theorem relation129_mem : "23,1,29,1;13,1,46,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block29[28]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation129_zero : nativeImage "23,1,29,1;13,1,46,1" = 0 := by
  change projection (relationPolynomial "23,1,29,1;13,1,46,1") = 0
  exact csv_relation_zero _ relation129_mem
theorem relation130_mem : "13,1,46,1;9,1,51,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block29[29]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation130_zero : nativeImage "13,1,46,1;9,1,51,1" = 0 := by
  change projection (relationPolynomial "13,1,46,1;9,1,51,1") = 0
  exact csv_relation_zero _ relation130_mem
theorem relation131_mem : "0,3,89,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block29[31]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation131_zero : nativeImage "0,3,89,1" = 0 := by
  change projection (relationPolynomial "0,3,89,1") = 0
  exact csv_relation_zero _ relation131_mem
theorem relation132_mem : "20,1,32,1;13,1,45,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block30[2]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation132_zero : nativeImage "20,1,32,1;13,1,45,1" = 0 := by
  change projection (relationPolynomial "20,1,32,1;13,1,45,1") = 0
  exact csv_relation_zero _ relation132_mem
theorem relation133_mem : "13,1,45,1;8,1,9,1,23,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block30[3]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation133_zero : nativeImage "13,1,45,1;8,1,9,1,23,1" = 0 := by
  change projection (relationPolynomial "13,1,45,1;8,1,9,1,23,1") = 0
  exact csv_relation_zero _ relation133_mem
theorem relation134_mem : "0,5,81,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block30[4]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation134_zero : nativeImage "0,5,81,1" = 0 := by
  change projection (relationPolynomial "0,5,81,1") = 0
  exact csv_relation_zero _ relation134_mem
theorem relation135_mem : "17,1,39,1;16,1,40,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block30[9]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation135_zero : nativeImage "17,1,39,1;16,1,40,1" = 0 := by
  change projection (relationPolynomial "17,1,39,1;16,1,40,1") = 0
  exact csv_relation_zero _ relation135_mem
theorem relation136_mem : "16,1,40,1;9,1,50,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block30[10]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation136_zero : nativeImage "16,1,40,1;9,1,50,1" = 0 := by
  change projection (relationPolynomial "16,1,40,1;9,1,50,1") = 0
  exact csv_relation_zero _ relation136_mem
theorem relation137_mem : "9,1,50,1;8,1,56,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block30[11]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation137_zero : nativeImage "9,1,50,1;8,1,56,1" = 0 := by
  change projection (relationPolynomial "9,1,50,1;8,1,56,1") = 0
  exact csv_relation_zero _ relation137_mem
theorem relation138_mem : "9,1,49,1;8,1,55,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block30[14]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation138_zero : nativeImage "9,1,49,1;8,1,55,1" = 0 := by
  change projection (relationPolynomial "9,1,49,1;8,1,55,1") = 0
  exact csv_relation_zero _ relation138_mem
theorem relation139_mem : "2,1,94,1;1,1,99,1" ∈ LinE2.RawData.relations := by
  exact relation_member 0 chunkBound rows transcription
    (block30[26]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation139_zero : nativeImage "2,1,94,1;1,1,99,1" = 0 := by
  change projection (relationPolynomial "2,1,94,1;1,1,99,1") = 0
  exact csv_relation_zero _ relation139_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk000
