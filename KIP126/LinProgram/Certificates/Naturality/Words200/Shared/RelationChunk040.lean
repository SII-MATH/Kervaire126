module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk040
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[40]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 40 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[40]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block3_mem : block3 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 3) (by decide)
private theorem block3_in_rows (r : List Char) (hr : r ∈ block3) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block3, block3_mem, hr⟩
private theorem block5_mem : block5 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 5) (by decide)
private theorem block5_in_rows (r : List Char) (hr : r ∈ block5) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block5, block5_mem, hr⟩
private theorem block6_mem : block6 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 6) (by decide)
private theorem block6_in_rows (r : List Char) (hr : r ∈ block6) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block6, block6_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
private theorem block18_mem : block18 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 18) (by decide)
private theorem block18_in_rows (r : List Char) (hr : r ∈ block18) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block18, block18_mem, hr⟩
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
theorem relation1567_mem : "16,1,596,1;9,1,686,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block0[0]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1567_zero : nativeImage "16,1,596,1;9,1,686,1" = 0 := by
  change projection (relationPolynomial "16,1,596,1;9,1,686,1") = 0
  exact csv_relation_zero _ relation1567_mem
theorem relation1568_mem : "9,1,686,1;8,1,723,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block0[1]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1568_zero : nativeImage "9,1,686,1;8,1,723,1" = 0 := by
  change projection (relationPolynomial "9,1,686,1;8,1,723,1") = 0
  exact csv_relation_zero _ relation1568_mem
theorem relation1569_mem : "39,1,452,1;9,1,685,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block0[20]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1569_zero : nativeImage "39,1,452,1;9,1,685,1" = 0 := by
  change projection (relationPolynomial "39,1,452,1;9,1,685,1") = 0
  exact csv_relation_zero _ relation1569_mem
theorem relation1570_mem : "9,1,685,1;8,1,722,1;1,1,42,1,402,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block0[22]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1570_zero : nativeImage "9,1,685,1;8,1,722,1;1,1,42,1,402,1" = 0 := by
  change projection (relationPolynomial "9,1,685,1;8,1,722,1;1,1,42,1,402,1") = 0
  exact csv_relation_zero _ relation1570_mem
theorem relation1571_mem : "11,1,699,1;7,1,776,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block3[23]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1571_zero : nativeImage "11,1,699,1;7,1,776,1" = 0 := by
  change projection (relationPolynomial "11,1,699,1;7,1,776,1") = 0
  exact csv_relation_zero _ relation1571_mem
theorem relation1572_mem : "7,1,776,1;3,1,18,1,525,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block3[24]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1572_zero : nativeImage "7,1,776,1;3,1,18,1,525,1" = 0 := by
  change projection (relationPolynomial "7,1,776,1;3,1,18,1,525,1") = 0
  exact csv_relation_zero _ relation1572_mem
theorem relation1573_mem : "2,1,18,1,565,1;1,1,3,1,847,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block5[4]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1573_zero : nativeImage "2,1,18,1,565,1;1,1,3,1,847,1" = 0 := by
  change projection (relationPolynomial "2,1,18,1,565,1;1,1,3,1,847,1") = 0
  exact csv_relation_zero _ relation1573_mem
theorem relation1574_mem : "130,1,191,1;122,1,198,1;96,1,235,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block5[25]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1574_zero : nativeImage "130,1,191,1;122,1,198,1;96,1,235,1" = 0 := by
  change projection (relationPolynomial "130,1,191,1;122,1,198,1;96,1,235,1") = 0
  exact csv_relation_zero _ relation1574_mem
theorem relation1575_mem : "96,1,235,1;74,1,264,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block5[28]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1575_zero : nativeImage "96,1,235,1;74,1,264,1" = 0 := by
  change projection (relationPolynomial "96,1,235,1;74,1,264,1") = 0
  exact csv_relation_zero _ relation1575_mem
theorem relation1576_mem : "122,1,198,1;43,1,444,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block5[30]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1576_zero : nativeImage "122,1,198,1;43,1,444,1" = 0 := by
  change projection (relationPolynomial "122,1,198,1;43,1,444,1") = 0
  exact csv_relation_zero _ relation1576_mem
theorem relation1577_mem : "43,1,444,1;43,1,443,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block5[31]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1577_zero : nativeImage "43,1,444,1;43,1,443,1" = 0 := by
  change projection (relationPolynomial "43,1,444,1;43,1,443,1") = 0
  exact csv_relation_zero _ relation1577_mem
theorem relation1578_mem : "74,1,264,1;43,1,443,1;7,1,769,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block6[6]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1578_zero : nativeImage "74,1,264,1;43,1,443,1;7,1,769,1" = 0 := by
  change projection (relationPolynomial "74,1,264,1;43,1,443,1;7,1,769,1") = 0
  exact csv_relation_zero _ relation1578_mem
theorem relation1579_mem : "8,2,562,1;7,1,761,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block16[6]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1579_zero : nativeImage "8,2,562,1;7,1,761,1" = 0 := by
  change projection (relationPolynomial "8,2,562,1;7,1,761,1") = 0
  exact csv_relation_zero _ relation1579_mem
theorem relation1580_mem : "7,1,761,1;1,2,906,1;0,1,946,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block16[13]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1580_zero : nativeImage "7,1,761,1;1,2,906,1;0,1,946,1" = 0 := by
  change projection (relationPolynomial "7,1,761,1;1,2,906,1;0,1,946,1") = 0
  exact csv_relation_zero _ relation1580_mem
theorem relation1581_mem : "0,1,946,1;0,3,3,1,825,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block16[15]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1581_zero : nativeImage "0,1,946,1;0,3,3,1,825,1" = 0 := by
  change projection (relationPolynomial "0,1,946,1;0,3,3,1,825,1") = 0
  exact csv_relation_zero _ relation1581_mem
theorem relation1582_mem : "0,2,3,1,838,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block18[7]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1582_zero : nativeImage "0,2,3,1,838,1" = 0 := by
  change projection (relationPolynomial "0,2,3,1,838,1") = 0
  exact csv_relation_zero _ relation1582_mem
theorem relation1583_mem : "13,1,668,1;9,1,705,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block22[20]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1583_zero : nativeImage "13,1,668,1;9,1,705,1" = 0 := by
  change projection (relationPolynomial "13,1,668,1;9,1,705,1") = 0
  exact csv_relation_zero _ relation1583_mem
theorem relation1584_mem : "17,1,613,1;5,1,786,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block22[22]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1584_zero : nativeImage "17,1,613,1;5,1,786,1" = 0 := by
  change projection (relationPolynomial "17,1,613,1;5,1,786,1") = 0
  exact csv_relation_zero _ relation1584_mem
theorem relation1585_mem : "5,1,786,1;1,1,64,1,275,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block22[24]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1585_zero : nativeImage "5,1,786,1;1,1,64,1,275,1" = 0 := by
  change projection (relationPolynomial "5,1,786,1;1,1,64,1,275,1") = 0
  exact csv_relation_zero _ relation1585_mem
theorem relation1586_mem : "80,1,255,1;74,1,260,1;72,1,267,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block23[9]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1586_zero : nativeImage "80,1,255,1;74,1,260,1;72,1,267,1" = 0 := by
  change projection (relationPolynomial "80,1,255,1;74,1,260,1;72,1,267,1") = 0
  exact csv_relation_zero _ relation1586_mem
theorem relation1587_mem : "74,1,260,1;68,1,278,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block23[10]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1587_zero : nativeImage "74,1,260,1;68,1,278,1" = 0 := by
  change projection (relationPolynomial "74,1,260,1;68,1,278,1") = 0
  exact csv_relation_zero _ relation1587_mem
theorem relation1588_mem : "68,1,278,1;64,1,286,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block23[12]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1588_zero : nativeImage "68,1,278,1;64,1,286,1" = 0 := by
  change projection (relationPolynomial "68,1,278,1;64,1,286,1") = 0
  exact csv_relation_zero _ relation1588_mem
theorem relation1589_mem : "64,1,286,1;64,1,285,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block23[13]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1589_zero : nativeImage "64,1,286,1;64,1,285,1" = 0 := by
  change projection (relationPolynomial "64,1,286,1;64,1,285,1") = 0
  exact csv_relation_zero _ relation1589_mem
theorem relation1590_mem : "64,1,285,1;56,1,333,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block23[17]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1590_zero : nativeImage "64,1,285,1;56,1,333,1" = 0 := by
  change projection (relationPolynomial "64,1,285,1;56,1,333,1") = 0
  exact csv_relation_zero _ relation1590_mem
theorem relation1591_mem : "56,1,333,1;50,1,366,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block23[20]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1591_zero : nativeImage "56,1,333,1;50,1,366,1" = 0 := by
  change projection (relationPolynomial "56,1,333,1;50,1,366,1") = 0
  exact csv_relation_zero _ relation1591_mem
theorem relation1592_mem : "50,1,366,1;49,1,367,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block23[21]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1592_zero : nativeImage "50,1,366,1;49,1,367,1" = 0 := by
  change projection (relationPolynomial "50,1,366,1;49,1,367,1") = 0
  exact csv_relation_zero _ relation1592_mem
theorem relation1593_mem : "49,1,367,1;40,1,475,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block23[26]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1593_zero : nativeImage "49,1,367,1;40,1,475,1" = 0 := by
  change projection (relationPolynomial "49,1,367,1;40,1,475,1") = 0
  exact csv_relation_zero _ relation1593_mem
theorem relation1594_mem : "40,1,475,1;22,1,561,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block24[4]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1594_zero : nativeImage "40,1,475,1;22,1,561,1" = 0 := by
  change projection (relationPolynomial "40,1,475,1;22,1,561,1") = 0
  exact csv_relation_zero _ relation1594_mem
theorem relation1595_mem : "22,1,561,1;20,1,582,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block24[5]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1595_zero : nativeImage "22,1,561,1;20,1,582,1" = 0 := by
  change projection (relationPolynomial "22,1,561,1;20,1,582,1") = 0
  exact csv_relation_zero _ relation1595_mem
theorem relation1596_mem : "20,1,582,1;17,1,612,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block24[6]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1596_zero : nativeImage "20,1,582,1;17,1,612,1" = 0 := by
  change projection (relationPolynomial "20,1,582,1;17,1,612,1") = 0
  exact csv_relation_zero _ relation1596_mem
theorem relation1597_mem : "17,1,612,1;16,1,613,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block24[7]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1597_zero : nativeImage "17,1,612,1;16,1,613,1" = 0 := by
  change projection (relationPolynomial "17,1,612,1;16,1,613,1") = 0
  exact csv_relation_zero _ relation1597_mem
theorem relation1598_mem : "72,1,267,1;16,1,613,1;13,1,667,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block24[10]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1598_zero : nativeImage "72,1,267,1;16,1,613,1;13,1,667,1" = 0 := by
  change projection (relationPolynomial "72,1,267,1;16,1,613,1;13,1,667,1") = 0
  exact csv_relation_zero _ relation1598_mem
theorem relation1599_mem : "13,1,667,1;9,1,704,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block24[13]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1599_zero : nativeImage "13,1,667,1;9,1,704,1" = 0 := by
  change projection (relationPolynomial "13,1,667,1;9,1,704,1") = 0
  exact csv_relation_zero _ relation1599_mem
theorem relation1600_mem : "9,1,704,1;8,1,738,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block24[16]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1600_zero : nativeImage "9,1,704,1;8,1,738,1" = 0 := by
  change projection (relationPolynomial "9,1,704,1;8,1,738,1") = 0
  exact csv_relation_zero _ relation1600_mem
theorem relation1601_mem : "17,1,610,1;8,1,72,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 40 chunkBound rows transcription
    (block26[16]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1601_zero : nativeImage "17,1,610,1;8,1,72,1,188,1" = 0 := by
  change projection (relationPolynomial "17,1,610,1;8,1,72,1,188,1") = 0
  exact csv_relation_zero _ relation1601_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk040
