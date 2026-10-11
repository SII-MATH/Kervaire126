module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk037
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[37]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 37 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[37]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block1_mem : block1 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 1) (by decide)
private theorem block1_in_rows (r : List Char) (hr : r ∈ block1) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block1, block1_mem, hr⟩
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
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
private theorem block13_mem : block13 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 13) (by decide)
private theorem block13_in_rows (r : List Char) (hr : r ∈ block13) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block13, block13_mem, hr⟩
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
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation1480_mem : "0,2,16,1,64,1,137,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block0[15]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1480_zero : nativeImage "0,2,16,1,64,1,137,1" = 0 := by
  change projection (relationPolynomial "0,2,16,1,64,1,137,1") = 0
  exact csv_relation_zero _ relation1480_mem
theorem relation1481_mem : "17,1,572,1;8,2,16,1,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block1[12]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1481_zero : nativeImage "17,1,572,1;8,2,16,1,244,1" = 0 := by
  change projection (relationPolynomial "17,1,572,1;8,2,16,1,244,1") = 0
  exact csv_relation_zero _ relation1481_mem
theorem relation1482_mem : "71,1,247,1;49,1,315,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block1[18]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1482_zero : nativeImage "71,1,247,1;49,1,315,1" = 0 := by
  change projection (relationPolynomial "71,1,247,1;49,1,315,1") = 0
  exact csv_relation_zero _ relation1482_mem
theorem relation1483_mem : "49,1,315,1;31,1,453,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block1[19]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1483_zero : nativeImage "49,1,315,1;31,1,453,1" = 0 := by
  change projection (relationPolynomial "49,1,315,1;31,1,453,1") = 0
  exact csv_relation_zero _ relation1483_mem
theorem relation1484_mem : "31,1,453,1;16,1,572,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block1[20]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1484_zero : nativeImage "31,1,453,1;16,1,572,1" = 0 := by
  change projection (relationPolynomial "31,1,453,1;16,1,572,1") = 0
  exact csv_relation_zero _ relation1484_mem
theorem relation1485_mem : "16,1,572,1;8,1,687,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block1[21]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1485_zero : nativeImage "16,1,572,1;8,1,687,1" = 0 := by
  change projection (relationPolynomial "16,1,572,1;8,1,687,1") = 0
  exact csv_relation_zero _ relation1485_mem
theorem relation1486_mem : "43,1,415,1;26,1,524,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block5[3]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1486_zero : nativeImage "43,1,415,1;26,1,524,1" = 0 := by
  change projection (relationPolynomial "43,1,415,1;26,1,524,1") = 0
  exact csv_relation_zero _ relation1486_mem
theorem relation1487_mem : "76,1,251,1;43,1,413,1;43,1,412,1;36,1,451,1;26,1,521,1;17,1,584,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block6[24]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1487_zero : nativeImage "76,1,251,1;43,1,413,1;43,1,412,1;36,1,451,1;26,1,521,1;17,1,584,1" = 0 := by
  change projection (relationPolynomial "76,1,251,1;43,1,413,1;43,1,412,1;36,1,451,1;26,1,521,1;17,1,584,1") = 0
  exact csv_relation_zero _ relation1487_mem
theorem relation1488_mem : "43,1,413,1;8,1,714,1;8,1,18,1,373,1;3,2,732,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block7[0]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1488_zero : nativeImage "43,1,413,1;8,1,714,1;8,1,18,1,373,1;3,2,732,1" = 0 := by
  change projection (relationPolynomial "43,1,413,1;8,1,714,1;8,1,18,1,373,1;3,2,732,1") = 0
  exact csv_relation_zero _ relation1488_mem
theorem relation1489_mem : "107,1,209,1;81,1,235,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block11[0]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1489_zero : nativeImage "107,1,209,1;81,1,235,1" = 0 := by
  change projection (relationPolynomial "107,1,209,1;81,1,235,1") = 0
  exact csv_relation_zero _ relation1489_mem
theorem relation1490_mem : "23,1,532,1;13,2,411,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block13[18]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1490_zero : nativeImage "23,1,532,1;13,2,411,1" = 0 := by
  change projection (relationPolynomial "23,1,532,1;13,2,411,1") = 0
  exact csv_relation_zero _ relation1490_mem
theorem relation1491_mem : "8,1,17,1,415,1;7,1,729,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block13[24]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1491_zero : nativeImage "8,1,17,1,415,1;7,1,729,1" = 0 := by
  change projection (relationPolynomial "8,1,17,1,415,1;7,1,729,1") = 0
  exact csv_relation_zero _ relation1491_mem
theorem relation1492_mem : "9,1,668,1;8,1,705,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block19[5]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1492_zero : nativeImage "9,1,668,1;8,1,705,1" = 0 := by
  change projection (relationPolynomial "9,1,668,1;8,1,705,1") = 0
  exact csv_relation_zero _ relation1492_mem
theorem relation1493_mem : "118,1,188,1;64,1,267,1;17,1,582,1;10,1,655,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block20[2]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1493_zero : nativeImage "118,1,188,1;64,1,267,1;17,1,582,1;10,1,655,1" = 0 := by
  change projection (relationPolynomial "118,1,188,1;64,1,267,1;17,1,582,1;10,1,655,1") = 0
  exact csv_relation_zero _ relation1493_mem
theorem relation1494_mem : "64,1,267,1;17,1,582,1;9,1,667,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block20[3]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1494_zero : nativeImage "64,1,267,1;17,1,582,1;9,1,667,1" = 0 := by
  change projection (relationPolynomial "64,1,267,1;17,1,582,1;9,1,667,1") = 0
  exact csv_relation_zero _ relation1494_mem
theorem relation1495_mem : "9,1,667,1;8,1,704,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block20[4]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1495_zero : nativeImage "9,1,667,1;8,1,704,1" = 0 := by
  change projection (relationPolynomial "9,1,667,1;8,1,704,1") = 0
  exact csv_relation_zero _ relation1495_mem
theorem relation1496_mem : "10,1,655,1;8,1,703,1;2,1,875,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block20[6]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1496_zero : nativeImage "10,1,655,1;8,1,703,1;2,1,875,1" = 0 := by
  change projection (relationPolynomial "10,1,655,1;8,1,703,1;2,1,875,1") = 0
  exact csv_relation_zero _ relation1496_mem
theorem relation1497_mem : "8,1,703,1;2,1,875,1;2,1,874,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block20[7]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1497_zero : nativeImage "8,1,703,1;2,1,875,1;2,1,874,1" = 0 := by
  change projection (relationPolynomial "8,1,703,1;2,1,875,1;2,1,874,1") = 0
  exact csv_relation_zero _ relation1497_mem
theorem relation1498_mem : "2,1,874,1;0,1,901,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block20[10]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1498_zero : nativeImage "2,1,874,1;0,1,901,1" = 0 := by
  change projection (relationPolynomial "2,1,874,1;0,1,901,1") = 0
  exact csv_relation_zero _ relation1498_mem
theorem relation1499_mem : "113,1,201,1;89,1,226,1;72,1,255,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block20[25]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1499_zero : nativeImage "113,1,201,1;89,1,226,1;72,1,255,1" = 0 := by
  change projection (relationPolynomial "113,1,201,1;89,1,226,1;72,1,255,1") = 0
  exact csv_relation_zero _ relation1499_mem
theorem relation1500_mem : "89,1,226,1;67,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block20[27]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1500_zero : nativeImage "89,1,226,1;67,1,260,1" = 0 := by
  change projection (relationPolynomial "89,1,226,1;67,1,260,1") = 0
  exact csv_relation_zero _ relation1500_mem
theorem relation1501_mem : "67,1,260,1;64,1,266,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block20[28]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1501_zero : nativeImage "67,1,260,1;64,1,266,1" = 0 := by
  change projection (relationPolynomial "67,1,260,1;64,1,266,1") = 0
  exact csv_relation_zero _ relation1501_mem
theorem relation1502_mem : "64,1,266,1;53,1,317,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block20[29]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1502_zero : nativeImage "64,1,266,1;53,1,317,1" = 0 := by
  change projection (relationPolynomial "64,1,266,1;53,1,317,1") = 0
  exact csv_relation_zero _ relation1502_mem
theorem relation1503_mem : "53,1,317,1;53,1,316,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block20[30]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1503_zero : nativeImage "53,1,317,1;53,1,316,1" = 0 := by
  change projection (relationPolynomial "53,1,317,1;53,1,316,1") = 0
  exact csv_relation_zero _ relation1503_mem
theorem relation1504_mem : "53,1,316,1;49,1,333,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block21[0]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1504_zero : nativeImage "53,1,316,1;49,1,333,1" = 0 := by
  change projection (relationPolynomial "53,1,316,1;49,1,333,1") = 0
  exact csv_relation_zero _ relation1504_mem
theorem relation1505_mem : "49,1,333,1;31,1,475,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block21[10]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1505_zero : nativeImage "49,1,333,1;31,1,475,1" = 0 := by
  change projection (relationPolynomial "49,1,333,1;31,1,475,1") = 0
  exact csv_relation_zero _ relation1505_mem
theorem relation1506_mem : "31,1,475,1;19,1,561,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block21[19]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1506_zero : nativeImage "31,1,475,1;19,1,561,1" = 0 := by
  change projection (relationPolynomial "31,1,475,1;19,1,561,1") = 0
  exact csv_relation_zero _ relation1506_mem
theorem relation1507_mem : "19,1,561,1;16,1,582,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block21[21]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1507_zero : nativeImage "19,1,561,1;16,1,582,1" = 0 := by
  change projection (relationPolynomial "19,1,561,1;16,1,582,1") = 0
  exact csv_relation_zero _ relation1507_mem
theorem relation1508_mem : "16,1,582,1;9,1,666,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block21[25]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1508_zero : nativeImage "16,1,582,1;9,1,666,1" = 0 := by
  change projection (relationPolynomial "16,1,582,1;9,1,666,1") = 0
  exact csv_relation_zero _ relation1508_mem
theorem relation1509_mem : "9,1,666,1;8,1,702,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block21[26]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1509_zero : nativeImage "9,1,666,1;8,1,702,1" = 0 := by
  change projection (relationPolynomial "9,1,666,1;8,1,702,1") = 0
  exact csv_relation_zero _ relation1509_mem
theorem relation1510_mem : "72,1,255,1;8,1,64,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block21[27]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1510_zero : nativeImage "72,1,255,1;8,1,64,1,188,1" = 0 := by
  change projection (relationPolynomial "72,1,255,1;8,1,64,1,188,1") = 0
  exact csv_relation_zero _ relation1510_mem
theorem relation1511_mem : "8,1,702,1;0,1,900,1;0,1,899,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block21[31]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1511_zero : nativeImage "8,1,702,1;0,1,900,1;0,1,899,1" = 0 := by
  change projection (relationPolynomial "8,1,702,1;0,1,900,1;0,1,899,1") = 0
  exact csv_relation_zero _ relation1511_mem
theorem relation1512_mem : "0,1,900,1;0,1,899,1;0,1,8,1,690,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block22[0]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1512_zero : nativeImage "0,1,900,1;0,1,899,1;0,1,8,1,690,1" = 0 := by
  change projection (relationPolynomial "0,1,900,1;0,1,899,1;0,1,8,1,690,1") = 0
  exact csv_relation_zero _ relation1512_mem
theorem relation1513_mem : "17,1,20,1,267,1;8,3,9,1,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block25[26]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1513_zero : nativeImage "17,1,20,1,267,1;8,3,9,1,212,1" = 0 := by
  change projection (relationPolynomial "17,1,20,1,267,1;8,3,9,1,212,1") = 0
  exact csv_relation_zero _ relation1513_mem
theorem relation1514_mem : "17,1,580,1;8,3,64,1,72,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block28[29]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1514_zero : nativeImage "17,1,580,1;8,3,64,1,72,1" = 0 := by
  change projection (relationPolynomial "17,1,580,1;8,3,64,1,72,1") = 0
  exact csv_relation_zero _ relation1514_mem
theorem relation1515_mem : "17,1,64,1,147,1;15,1,598,1;13,1,637,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block30[11]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1515_zero : nativeImage "17,1,64,1,147,1;15,1,598,1;13,1,637,1" = 0 := by
  change projection (relationPolynomial "17,1,64,1,147,1;15,1,598,1;13,1,637,1") = 0
  exact csv_relation_zero _ relation1515_mem
theorem relation1516_mem : "13,1,637,1;9,1,664,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block30[12]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1516_zero : nativeImage "13,1,637,1;9,1,664,1" = 0 := by
  change projection (relationPolynomial "13,1,637,1;9,1,664,1") = 0
  exact csv_relation_zero _ relation1516_mem
theorem relation1517_mem : "9,1,664,1;8,2,529,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block30[13]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1517_zero : nativeImage "9,1,664,1;8,2,529,1" = 0 := by
  change projection (relationPolynomial "9,1,664,1;8,2,529,1") = 0
  exact csv_relation_zero _ relation1517_mem
theorem relation1518_mem : "15,1,598,1;0,1,138,1,160,1;0,1,8,1,17,1,380,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block30[15]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1518_zero : nativeImage "15,1,598,1;0,1,138,1,160,1;0,1,8,1,17,1,380,1" = 0 := by
  change projection (relationPolynomial "15,1,598,1;0,1,138,1,160,1;0,1,8,1,17,1,380,1") = 0
  exact csv_relation_zero _ relation1518_mem
theorem relation1519_mem : "0,1,138,1,160,1;0,1,8,1,17,1,380,1;0,5,862,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block30[16]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1519_zero : nativeImage "0,1,138,1,160,1;0,1,8,1,17,1,380,1;0,5,862,1" = 0 := by
  change projection (relationPolynomial "0,1,138,1,160,1;0,1,8,1,17,1,380,1;0,5,862,1") = 0
  exact csv_relation_zero _ relation1519_mem
theorem relation1520_mem : "0,1,64,1,257,1;0,1,8,2,516,1;0,4,59,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 37 chunkBound rows transcription
    (block31[3]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1520_zero : nativeImage "0,1,64,1,257,1;0,1,8,2,516,1;0,4,59,1,260,1" = 0 := by
  change projection (relationPolynomial "0,1,64,1,257,1;0,1,8,2,516,1;0,4,59,1,260,1") = 0
  exact csv_relation_zero _ relation1520_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk037
