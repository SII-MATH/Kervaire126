module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk050
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[50]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 50 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[50]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block2_mem : block2 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 2) (by decide)
private theorem block2_in_rows (r : List Char) (hr : r ∈ block2) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block2, block2_mem, hr⟩
private theorem block3_mem : block3 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 3) (by decide)
private theorem block3_in_rows (r : List Char) (hr : r ∈ block3) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block3, block3_mem, hr⟩
private theorem block5_mem : block5 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 5) (by decide)
private theorem block5_in_rows (r : List Char) (hr : r ∈ block5) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block5, block5_mem, hr⟩
private theorem block7_mem : block7 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 7) (by decide)
private theorem block7_in_rows (r : List Char) (hr : r ∈ block7) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block7, block7_mem, hr⟩
private theorem block8_mem : block8 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 8) (by decide)
private theorem block8_in_rows (r : List Char) (hr : r ∈ block8) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block8, block8_mem, hr⟩
private theorem block15_mem : block15 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 15) (by decide)
private theorem block15_in_rows (r : List Char) (hr : r ∈ block15) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block15, block15_mem, hr⟩
private theorem block17_mem : block17 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 17) (by decide)
private theorem block17_in_rows (r : List Char) (hr : r ∈ block17) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block17, block17_mem, hr⟩
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
theorem relation1775_mem : "17,1,689,1;8,2,64,1,160,1;8,4,278,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block2[1]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1775_zero : nativeImage "17,1,689,1;8,2,64,1,160,1;8,4,278,1" = 0 := by
  change projection (relationPolynomial "17,1,689,1;8,2,64,1,160,1;8,4,278,1") = 0
  exact csv_relation_zero _ relation1775_mem
theorem relation1776_mem : "46,1,491,1;44,1,501,1;42,1,516,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block2[29]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1776_zero : nativeImage "46,1,491,1;44,1,501,1;42,1,516,1" = 0 := by
  change projection (relationPolynomial "46,1,491,1;44,1,501,1;42,1,516,1") = 0
  exact csv_relation_zero _ relation1776_mem
theorem relation1777_mem : "44,1,501,1;39,1,549,1;31,1,574,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block2[31]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1777_zero : nativeImage "44,1,501,1;39,1,549,1;31,1,574,1" = 0 := by
  change projection (relationPolynomial "44,1,501,1;39,1,549,1;31,1,574,1") = 0
  exact csv_relation_zero _ relation1777_mem
theorem relation1778_mem : "39,1,549,1;19,1,653,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block3[2]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1778_zero : nativeImage "39,1,549,1;19,1,653,1" = 0 := by
  change projection (relationPolynomial "39,1,549,1;19,1,653,1") = 0
  exact csv_relation_zero _ relation1778_mem
theorem relation1779_mem : "19,1,653,1;17,1,688,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block3[3]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1779_zero : nativeImage "19,1,653,1;17,1,688,1" = 0 := by
  change projection (relationPolynomial "19,1,653,1;17,1,688,1") = 0
  exact csv_relation_zero _ relation1779_mem
theorem relation1780_mem : "31,1,574,1;16,1,689,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block3[4]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1780_zero : nativeImage "31,1,574,1;16,1,689,1" = 0 := by
  change projection (relationPolynomial "31,1,574,1;16,1,689,1") = 0
  exact csv_relation_zero _ relation1780_mem
theorem relation1781_mem : "16,1,689,1;9,1,796,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block3[5]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1781_zero : nativeImage "16,1,689,1;9,1,796,1" = 0 := by
  change projection (relationPolynomial "16,1,689,1;9,1,796,1") = 0
  exact csv_relation_zero _ relation1781_mem
theorem relation1782_mem : "17,1,688,1;9,1,796,1;9,1,795,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block3[6]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1782_zero : nativeImage "17,1,688,1;9,1,796,1;9,1,795,1" = 0 := by
  change projection (relationPolynomial "17,1,688,1;9,1,796,1;9,1,795,1") = 0
  exact csv_relation_zero _ relation1782_mem
theorem relation1783_mem : "9,1,796,1;8,1,831,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block3[7]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1783_zero : nativeImage "9,1,796,1;8,1,831,1" = 0 := by
  change projection (relationPolynomial "9,1,796,1;8,1,831,1") = 0
  exact csv_relation_zero _ relation1783_mem
theorem relation1784_mem : "9,1,795,1;1,2,1009,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block3[8]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1784_zero : nativeImage "9,1,795,1;1,2,1009,1" = 0 := by
  change projection (relationPolynomial "9,1,795,1;1,2,1009,1") = 0
  exact csv_relation_zero _ relation1784_mem
theorem relation1785_mem : "1,2,1009,1;0,1,1060,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block3[9]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1785_zero : nativeImage "1,2,1009,1;0,1,1060,1" = 0 := by
  change projection (relationPolynomial "1,2,1009,1;0,1,1060,1") = 0
  exact csv_relation_zero _ relation1785_mem
theorem relation1786_mem : "31,1,573,1;16,1,688,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block3[30]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1786_zero : nativeImage "31,1,573,1;16,1,688,1" = 0 := by
  change projection (relationPolynomial "31,1,573,1;16,1,688,1") = 0
  exact csv_relation_zero _ relation1786_mem
theorem relation1787_mem : "16,1,688,1;8,1,830,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block3[31]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1787_zero : nativeImage "16,1,688,1;8,1,830,1" = 0 := by
  change projection (relationPolynomial "16,1,688,1;8,1,830,1") = 0
  exact csv_relation_zero _ relation1787_mem
theorem relation1788_mem : "112,1,244,1;64,1,343,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block5[0]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1788_zero : nativeImage "112,1,244,1;64,1,343,1" = 0 := by
  change projection (relationPolynomial "112,1,244,1;64,1,343,1") = 0
  exact csv_relation_zero _ relation1788_mem
theorem relation1789_mem : "0,2,8,1,64,1,224,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block7[4]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1789_zero : nativeImage "0,2,8,1,64,1,224,1" = 0 := by
  change projection (relationPolynomial "0,2,8,1,64,1,224,1") = 0
  exact csv_relation_zero _ relation1789_mem
theorem relation1790_mem : "17,1,687,1;8,3,452,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block8[0]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1790_zero : nativeImage "17,1,687,1;8,3,452,1" = 0 := by
  change projection (relationPolynomial "17,1,687,1;8,3,452,1") = 0
  exact csv_relation_zero _ relation1790_mem
theorem relation1791_mem : "17,1,686,1;8,1,829,1;0,3,1033,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block8[13]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1791_zero : nativeImage "17,1,686,1;8,1,829,1;0,3,1033,1" = 0 := by
  change projection (relationPolynomial "17,1,686,1;8,1,829,1;0,3,1033,1") = 0
  exact csv_relation_zero _ relation1791_mem
theorem relation1792_mem : "7,1,92,1,209,1;4,1,935,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block15[27]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1792_zero : nativeImage "7,1,92,1,209,1;4,1,935,1" = 0 := by
  change projection (relationPolynomial "7,1,92,1,209,1;4,1,935,1") = 0
  exact csv_relation_zero _ relation1792_mem
theorem relation1793_mem : "4,1,935,1;1,1,1072,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block15[31]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1793_zero : nativeImage "4,1,935,1;1,1,1072,1" = 0 := by
  change projection (relationPolynomial "4,1,935,1;1,1,1072,1") = 0
  exact csv_relation_zero _ relation1793_mem
theorem relation1794_mem : "3,1,966,1;0,1,1087,1;0,1,8,2,17,1,324,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block17[8]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1794_zero : nativeImage "3,1,966,1;0,1,1087,1;0,1,8,2,17,1,324,1" = 0 := by
  change projection (relationPolynomial "3,1,966,1;0,1,1087,1;0,1,8,2,17,1,324,1") = 0
  exact csv_relation_zero _ relation1794_mem
theorem relation1795_mem : "0,1,1087,1;0,1,8,2,17,1,324,1;0,3,1055,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block17[11]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1795_zero : nativeImage "0,1,1087,1;0,1,8,2,17,1,324,1;0,3,1055,1" = 0 := by
  change projection (relationPolynomial "0,1,1087,1;0,1,8,2,17,1,324,1;0,3,1055,1") = 0
  exact csv_relation_zero _ relation1795_mem
theorem relation1796_mem : "23,1,640,1;13,1,80,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block29[29]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1796_zero : nativeImage "23,1,640,1;13,1,80,1,188,1" = 0 := by
  change projection (relationPolynomial "23,1,640,1;13,1,80,1,188,1") = 0
  exact csv_relation_zero _ relation1796_mem
theorem relation1797_mem : "64,1,360,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block30[31]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1797_zero : nativeImage "64,1,360,1" = 0 := by
  change projection (relationPolynomial "64,1,360,1") = 0
  exact csv_relation_zero _ relation1797_mem
theorem relation1798_mem : "22,1,640,1;8,1,80,1,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 50 chunkBound rows transcription
    (block31[22]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1798_zero : nativeImage "22,1,640,1;8,1,80,1,212,1" = 0 := by
  change projection (relationPolynomial "22,1,640,1;8,1,80,1,212,1") = 0
  exact csv_relation_zero _ relation1798_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk050
