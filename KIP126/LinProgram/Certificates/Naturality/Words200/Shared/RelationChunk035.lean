module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk035
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[35]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 35 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[35]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block2_mem : block2 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 2) (by decide)
private theorem block2_in_rows (r : List Char) (hr : r ∈ block2) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block2, block2_mem, hr⟩
private theorem block3_mem : block3 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 3) (by decide)
private theorem block3_in_rows (r : List Char) (hr : r ∈ block3) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block3, block3_mem, hr⟩
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
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
private theorem block17_mem : block17 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 17) (by decide)
private theorem block17_in_rows (r : List Char) (hr : r ∈ block17) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block17, block17_mem, hr⟩
private theorem block21_mem : block21 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 21) (by decide)
private theorem block21_in_rows (r : List Char) (hr : r ∈ block21) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block21, block21_mem, hr⟩
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block26_mem : block26 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 26) (by decide)
private theorem block26_in_rows (r : List Char) (hr : r ∈ block26) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block26, block26_mem, hr⟩
theorem relation1431_mem : "17,1,559,1;17,1,558,1;8,3,64,2" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block2[11]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1431_zero : nativeImage "17,1,559,1;17,1,558,1;8,3,64,2" = 0 := by
  change projection (relationPolynomial "17,1,559,1;17,1,558,1;8,3,64,2") = 0
  exact csv_relation_zero _ relation1431_mem
theorem relation1432_mem : "17,1,558,1;0,1,64,1,246,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block2[14]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1432_zero : nativeImage "17,1,558,1;0,1,64,1,246,1" = 0 := by
  change projection (relationPolynomial "17,1,558,1;0,1,64,1,246,1") = 0
  exact csv_relation_zero _ relation1432_mem
theorem relation1433_mem : "17,1,557,1;8,1,665,1;0,1,64,1,245,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block3[6]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1433_zero : nativeImage "17,1,557,1;8,1,665,1;0,1,64,1,245,1" = 0 := by
  change projection (relationPolynomial "17,1,557,1;8,1,665,1;0,1,64,1,245,1") = 0
  exact csv_relation_zero _ relation1433_mem
theorem relation1434_mem : "0,1,64,1,245,1;0,1,17,2,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block3[7]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1434_zero : nativeImage "0,1,64,1,245,1;0,1,17,2,260,1" = 0 := by
  change projection (relationPolynomial "0,1,64,1,245,1;0,1,17,2,260,1") = 0
  exact csv_relation_zero _ relation1434_mem
theorem relation1435_mem : "17,1,64,1,138,1;10,1,623,1;8,1,664,1;0,1,138,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block3[28]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1435_zero : nativeImage "17,1,64,1,138,1;10,1,623,1;8,1,664,1;0,1,138,1,149,1" = 0 := by
  change projection (relationPolynomial "17,1,64,1,138,1;10,1,623,1;8,1,664,1;0,1,138,1,149,1") = 0
  exact csv_relation_zero _ relation1435_mem
theorem relation1436_mem : "10,1,623,1;0,1,16,1,17,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block3[29]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1436_zero : nativeImage "10,1,623,1;0,1,16,1,17,1,260,1" = 0 := by
  change projection (relationPolynomial "10,1,623,1;0,1,16,1,17,1,260,1") = 0
  exact csv_relation_zero _ relation1436_mem
theorem relation1437_mem : "17,1,555,1;8,1,663,1;6,1,685,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block7[31]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1437_zero : nativeImage "17,1,555,1;8,1,663,1;6,1,685,1" = 0 := by
  change projection (relationPolynomial "17,1,555,1;8,1,663,1;6,1,685,1") = 0
  exact csv_relation_zero _ relation1437_mem
theorem relation1438_mem : "6,1,685,1;0,1,871,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block8[0]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1438_zero : nativeImage "6,1,685,1;0,1,871,1" = 0 := by
  change projection (relationPolynomial "6,1,685,1;0,1,871,1") = 0
  exact csv_relation_zero _ relation1438_mem
theorem relation1439_mem : "17,1,553,1;16,1,554,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block10[7]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1439_zero : nativeImage "17,1,553,1;16,1,554,1" = 0 := by
  change projection (relationPolynomial "17,1,553,1;16,1,554,1") = 0
  exact csv_relation_zero _ relation1439_mem
theorem relation1440_mem : "43,1,378,1;26,1,506,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block10[23]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1440_zero : nativeImage "43,1,378,1;26,1,506,1" = 0 := by
  change projection (relationPolynomial "43,1,378,1;26,1,506,1") = 0
  exact csv_relation_zero _ relation1440_mem
theorem relation1441_mem : "26,1,506,1;0,1,7,1,698,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block10[26]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1441_zero : nativeImage "26,1,506,1;0,1,7,1,698,1" = 0 := by
  change projection (relationPolynomial "26,1,506,1;0,1,7,1,698,1") = 0
  exact csv_relation_zero _ relation1441_mem
theorem relation1442_mem : "43,1,377,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block10[28]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1442_zero : nativeImage "43,1,377,1" = 0 := by
  change projection (relationPolynomial "43,1,377,1") = 0
  exact csv_relation_zero _ relation1442_mem
theorem relation1443_mem : "43,1,376,1;1,1,884,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block11[24]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1443_zero : nativeImage "43,1,376,1;1,1,884,1" = 0 := by
  change projection (relationPolynomial "43,1,376,1;1,1,884,1") = 0
  exact csv_relation_zero _ relation1443_mem
theorem relation1444_mem : "32,1,450,1;13,2,373,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block16[10]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1444_zero : nativeImage "32,1,450,1;13,2,373,1" = 0 := by
  change projection (relationPolynomial "32,1,450,1;13,2,373,1") = 0
  exact csv_relation_zero _ relation1444_mem
theorem relation1445_mem : "8,1,13,1,450,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block17[25]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1445_zero : nativeImage "8,1,13,1,450,1" = 0 := by
  change projection (relationPolynomial "8,1,13,1,450,1") = 0
  exact csv_relation_zero _ relation1445_mem
theorem relation1446_mem : "3,2,707,1;1,1,881,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block17[31]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1446_zero : nativeImage "3,2,707,1;1,1,881,1" = 0 := by
  change projection (relationPolynomial "3,2,707,1;1,1,881,1") = 0
  exact csv_relation_zero _ relation1446_mem
theorem relation1447_mem : "8,3,314,1;7,1,704,1;6,1,707,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block21[12]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1447_zero : nativeImage "8,3,314,1;7,1,704,1;6,1,707,1" = 0 := by
  change projection (relationPolynomial "8,3,314,1;7,1,704,1;6,1,707,1") = 0
  exact csv_relation_zero _ relation1447_mem
theorem relation1448_mem : "7,1,704,1;4,1,761,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block21[13]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1448_zero : nativeImage "7,1,704,1;4,1,761,1" = 0 := by
  change projection (relationPolynomial "7,1,704,1;4,1,761,1") = 0
  exact csv_relation_zero _ relation1448_mem
theorem relation1449_mem : "6,1,707,1;4,1,761,1;1,2,64,1,239,1;0,2,879,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block21[15]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1449_zero : nativeImage "6,1,707,1;4,1,761,1;1,2,64,1,239,1;0,2,879,1" = 0 := by
  change projection (relationPolynomial "6,1,707,1;4,1,761,1;1,2,64,1,239,1;0,2,879,1") = 0
  exact csv_relation_zero _ relation1449_mem
theorem relation1450_mem : "17,1,69,1,138,1;14,1,604,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block25[31]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1450_zero : nativeImage "17,1,69,1,138,1;14,1,604,1" = 0 := by
  change projection (relationPolynomial "17,1,69,1,138,1;14,1,604,1") = 0
  exact csv_relation_zero _ relation1450_mem
theorem relation1451_mem : "14,1,604,1;5,1,728,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block26[5]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1451_zero : nativeImage "14,1,604,1;5,1,728,1" = 0 := by
  change projection (relationPolynomial "14,1,604,1;5,1,728,1") = 0
  exact csv_relation_zero _ relation1451_mem
theorem relation1452_mem : "5,1,728,1;3,1,797,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block26[6]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1452_zero : nativeImage "5,1,728,1;3,1,797,1" = 0 := by
  change projection (relationPolynomial "5,1,728,1;3,1,797,1") = 0
  exact csv_relation_zero _ relation1452_mem
theorem relation1453_mem : "3,1,797,1;1,2,856,1" ∈ LinE2.RawData.relations := by
  exact relation_member 35 chunkBound rows transcription
    (block26[10]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1453_zero : nativeImage "3,1,797,1;1,2,856,1" = 0 := by
  change projection (relationPolynomial "3,1,797,1;1,2,856,1") = 0
  exact csv_relation_zero _ relation1453_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk035
