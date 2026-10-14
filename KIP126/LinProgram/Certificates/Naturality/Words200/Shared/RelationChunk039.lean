module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk039
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[39]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 39 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[39]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block6_mem : block6 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 6) (by decide)
private theorem block6_in_rows (r : List Char) (hr : r ∈ block6) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block6, block6_mem, hr⟩
private theorem block15_mem : block15 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 15) (by decide)
private theorem block15_in_rows (r : List Char) (hr : r ∈ block15) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block15, block15_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
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
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation1538_mem : "8,1,18,1,415,1;3,1,861,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block6[12]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1538_zero : nativeImage "8,1,18,1,415,1;3,1,861,1" = 0 := by
  change projection (relationPolynomial "8,1,18,1,415,1;3,1,861,1") = 0
  exact csv_relation_zero _ relation1538_mem
theorem relation1539_mem : "80,1,250,1;9,1,692,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block15[8]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1539_zero : nativeImage "80,1,250,1;9,1,692,1" = 0 := by
  change projection (relationPolynomial "80,1,250,1;9,1,692,1") = 0
  exact csv_relation_zero _ relation1539_mem
theorem relation1540_mem : "79,1,250,1;72,1,261,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block15[20]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1540_zero : nativeImage "79,1,250,1;72,1,261,1" = 0 := by
  change projection (relationPolynomial "79,1,250,1;72,1,261,1") = 0
  exact csv_relation_zero _ relation1540_mem
theorem relation1541_mem : "72,1,261,1;8,1,729,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block16[11]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1541_zero : nativeImage "72,1,261,1;8,1,729,1" = 0 := by
  change projection (relationPolynomial "72,1,261,1;8,1,729,1") = 0
  exact csv_relation_zero _ relation1541_mem
theorem relation1542_mem : "113,1,209,1;64,1,280,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block16[29]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1542_zero : nativeImage "113,1,209,1;64,1,280,1" = 0 := by
  change projection (relationPolynomial "113,1,209,1;64,1,280,1") = 0
  exact csv_relation_zero _ relation1542_mem
theorem relation1543_mem : "17,1,602,1;17,1,600,1;8,3,346,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block24[21]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1543_zero : nativeImage "17,1,602,1;17,1,600,1;8,3,346,1" = 0 := by
  change projection (relationPolynomial "17,1,602,1;17,1,600,1;8,3,346,1") = 0
  exact csv_relation_zero _ relation1543_mem
theorem relation1544_mem : "17,1,600,1;0,3,897,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block24[24]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1544_zero : nativeImage "17,1,600,1;0,3,897,1" = 0 := by
  change projection (relationPolynomial "17,1,600,1;0,3,897,1") = 0
  exact csv_relation_zero _ relation1544_mem
theorem relation1545_mem : "17,1,599,1;13,1,653,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block25[25]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1545_zero : nativeImage "17,1,599,1;13,1,653,1" = 0 := by
  change projection (relationPolynomial "17,1,599,1;13,1,653,1") = 0
  exact csv_relation_zero _ relation1545_mem
theorem relation1546_mem : "13,1,653,1;9,1,689,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block25[26]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1546_zero : nativeImage "13,1,653,1;9,1,689,1" = 0 := by
  change projection (relationPolynomial "13,1,653,1;9,1,689,1") = 0
  exact csv_relation_zero _ relation1546_mem
theorem relation1547_mem : "9,1,689,1;8,2,549,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block25[28]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1547_zero : nativeImage "9,1,689,1;8,2,549,1" = 0 := by
  change projection (relationPolynomial "9,1,689,1;8,2,549,1") = 0
  exact csv_relation_zero _ relation1547_mem
theorem relation1548_mem : "17,2,292,1;8,1,42,1,260,1;0,3,64,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block26[0]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1548_zero : nativeImage "17,2,292,1;8,1,42,1,260,1;0,3,64,1,260,1" = 0 := by
  change projection (relationPolynomial "17,2,292,1;8,1,42,1,260,1;0,3,64,1,260,1") = 0
  exact csv_relation_zero _ relation1548_mem
theorem relation1549_mem : "17,1,598,1;8,1,726,1;0,1,927,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block26[26]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1549_zero : nativeImage "17,1,598,1;8,1,726,1;0,1,927,1" = 0 := by
  change projection (relationPolynomial "17,1,598,1;8,1,726,1;0,1,927,1") = 0
  exact csv_relation_zero _ relation1549_mem
theorem relation1550_mem : "39,1,454,1;32,1,491,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block27[15]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1550_zero : nativeImage "39,1,454,1;32,1,491,1" = 0 := by
  change projection (relationPolynomial "39,1,454,1;32,1,491,1") = 0
  exact csv_relation_zero _ relation1550_mem
theorem relation1551_mem : "32,1,491,1;29,1,516,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block27[17]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1551_zero : nativeImage "32,1,491,1;29,1,516,1" = 0 := by
  change projection (relationPolynomial "32,1,491,1;29,1,516,1") = 0
  exact csv_relation_zero _ relation1551_mem
theorem relation1552_mem : "29,1,516,1;8,2,17,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block27[20]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1552_zero : nativeImage "29,1,516,1;8,2,17,1,260,1" = 0 := by
  change projection (relationPolynomial "29,1,516,1;8,2,17,1,260,1") = 0
  exact csv_relation_zero _ relation1552_mem
theorem relation1553_mem : "17,1,64,1,149,1;16,1,598,1;8,2,17,1,260,1;0,1,149,2" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block27[21]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1553_zero : nativeImage "17,1,64,1,149,1;16,1,598,1;8,2,17,1,260,1;0,1,149,2" = 0 := by
  change projection (relationPolynomial "17,1,64,1,149,1;16,1,598,1;8,2,17,1,260,1;0,1,149,2") = 0
  exact csv_relation_zero _ relation1553_mem
theorem relation1554_mem : "146,1,160,1;137,1,166,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block27[22]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1554_zero : nativeImage "146,1,160,1;137,1,166,1" = 0 := by
  change projection (relationPolynomial "146,1,160,1;137,1,166,1") = 0
  exact csv_relation_zero _ relation1554_mem
theorem relation1555_mem : "137,1,166,1;112,1,206,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block27[27]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1555_zero : nativeImage "137,1,166,1;112,1,206,1" = 0 := by
  change projection (relationPolynomial "137,1,166,1;112,1,206,1") = 0
  exact csv_relation_zero _ relation1555_mem
theorem relation1556_mem : "112,1,206,1;79,1,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block27[28]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1556_zero : nativeImage "112,1,206,1;79,1,244,1" = 0 := by
  change projection (relationPolynomial "112,1,206,1;79,1,244,1") = 0
  exact csv_relation_zero _ relation1556_mem
theorem relation1557_mem : "79,1,244,1;72,1,257,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block27[30]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1557_zero : nativeImage "79,1,244,1;72,1,257,1" = 0 := by
  change projection (relationPolynomial "79,1,244,1;72,1,257,1") = 0
  exact csv_relation_zero _ relation1557_mem
theorem relation1558_mem : "72,1,257,1;55,1,316,1;49,1,347,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block28[6]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1558_zero : nativeImage "72,1,257,1;55,1,316,1;49,1,347,1" = 0 := by
  change projection (relationPolynomial "72,1,257,1;55,1,316,1;49,1,347,1") = 0
  exact csv_relation_zero _ relation1558_mem
theorem relation1559_mem : "49,1,347,1;49,1,346,1;16,1,64,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block28[11]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1559_zero : nativeImage "49,1,347,1;49,1,346,1;16,1,64,1,149,1" = 0 := by
  change projection (relationPolynomial "49,1,347,1;49,1,346,1;16,1,64,1,149,1") = 0
  exact csv_relation_zero _ relation1559_mem
theorem relation1560_mem : "49,1,346,1;8,2,16,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block28[12]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1560_zero : nativeImage "49,1,346,1;8,2,16,1,260,1" = 0 := by
  change projection (relationPolynomial "49,1,346,1;8,2,16,1,260,1") = 0
  exact csv_relation_zero _ relation1560_mem
theorem relation1561_mem : "17,1,597,1;8,3,343,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block31[1]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1561_zero : nativeImage "17,1,597,1;8,3,343,1" = 0 := by
  change projection (relationPolynomial "17,1,597,1;8,3,343,1") = 0
  exact csv_relation_zero _ relation1561_mem
theorem relation1562_mem : "17,1,596,1;9,1,687,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block31[21]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1562_zero : nativeImage "17,1,596,1;9,1,687,1" = 0 := by
  change projection (relationPolynomial "17,1,596,1;9,1,687,1") = 0
  exact csv_relation_zero _ relation1562_mem
theorem relation1563_mem : "9,1,687,1;8,1,724,1;0,3,896,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block31[23]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1563_zero : nativeImage "9,1,687,1;8,1,724,1;0,3,896,1" = 0 := by
  change projection (relationPolynomial "9,1,687,1;8,1,724,1;0,3,896,1") = 0
  exact csv_relation_zero _ relation1563_mem
theorem relation1564_mem : "71,1,258,1;49,1,344,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block31[29]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1564_zero : nativeImage "71,1,258,1;49,1,344,1" = 0 := by
  change projection (relationPolynomial "71,1,258,1;49,1,344,1") = 0
  exact csv_relation_zero _ relation1564_mem
theorem relation1565_mem : "49,1,344,1;31,1,489,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block31[30]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1565_zero : nativeImage "49,1,344,1;31,1,489,1" = 0 := by
  change projection (relationPolynomial "49,1,344,1;31,1,489,1") = 0
  exact csv_relation_zero _ relation1565_mem
theorem relation1566_mem : "31,1,489,1;16,1,596,1" ∈ LinE2.RawData.relations := by
  exact relation_member 39 chunkBound rows transcription
    (block31[31]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1566_zero : nativeImage "31,1,489,1;16,1,596,1" = 0 := by
  change projection (relationPolynomial "31,1,489,1;16,1,596,1") = 0
  exact csv_relation_zero _ relation1566_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk039
