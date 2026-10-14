module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk047
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[47]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 47 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[47]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
private theorem block13_mem : block13 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 13) (by decide)
private theorem block13_in_rows (r : List Char) (hr : r ∈ block13) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block13, block13_mem, hr⟩
private theorem block15_mem : block15 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 15) (by decide)
private theorem block15_in_rows (r : List Char) (hr : r ∈ block15) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block15, block15_mem, hr⟩
private theorem block17_mem : block17 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 17) (by decide)
private theorem block17_in_rows (r : List Char) (hr : r ∈ block17) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block17, block17_mem, hr⟩
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
theorem relation1713_mem : "2,1,987,1;1,1,1019,1;1,1,1017,1;1,2,988,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block0[8]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1713_zero : nativeImage "2,1,987,1;1,1,1019,1;1,1,1017,1;1,2,988,1" = 0 := by
  change projection (relationPolynomial "2,1,987,1;1,1,1019,1;1,1,1017,1;1,2,988,1") = 0
  exact csv_relation_zero _ relation1713_mem
theorem relation1714_mem : "1,2,988,1;0,1,1046,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block0[9]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1714_zero : nativeImage "1,2,988,1;0,1,1046,1" = 0 := by
  change projection (relationPolynomial "1,2,988,1;0,1,1046,1") = 0
  exact csv_relation_zero _ relation1714_mem
theorem relation1715_mem : "1,1,1017,1;0,1,1046,1;0,2,1021,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block0[10]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1715_zero : nativeImage "1,1,1017,1;0,1,1046,1;0,2,1021,1" = 0 := by
  change projection (relationPolynomial "1,1,1017,1;0,1,1046,1;0,2,1021,1") = 0
  exact csv_relation_zero _ relation1715_mem
theorem relation1716_mem : "68,1,319,1;1,1,1014,1;1,1,1013,1;0,1,1043,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block4[11]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1716_zero : nativeImage "68,1,319,1;1,1,1014,1;1,1,1013,1;0,1,1043,1" = 0 := by
  change projection (relationPolynomial "68,1,319,1;1,1,1014,1;1,1,1013,1;0,1,1043,1") = 0
  exact csv_relation_zero _ relation1716_mem
theorem relation1717_mem : "0,1,1043,1;0,2,1016,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block4[12]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1717_zero : nativeImage "0,1,1043,1;0,2,1016,1" = 0 := by
  change projection (relationPolynomial "0,1,1043,1;0,2,1016,1") = 0
  exact csv_relation_zero _ relation1717_mem
theorem relation1718_mem : "0,2,1016,1;0,2,1015,1;0,4,17,2,324,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block4[14]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1718_zero : nativeImage "0,2,1016,1;0,2,1015,1;0,4,17,2,324,1" = 0 := by
  change projection (relationPolynomial "0,2,1016,1;0,2,1015,1;0,4,17,2,324,1") = 0
  exact csv_relation_zero _ relation1718_mem
theorem relation1719_mem : "23,1,610,1;13,1,738,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block13[14]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1719_zero : nativeImage "23,1,610,1;13,1,738,1" = 0 := by
  change projection (relationPolynomial "23,1,610,1;13,1,738,1") = 0
  exact csv_relation_zero _ relation1719_mem
theorem relation1720_mem : "13,1,738,1;9,1,80,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block13[15]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1720_zero : nativeImage "13,1,738,1;9,1,80,1,188,1" = 0 := by
  change projection (relationPolynomial "13,1,738,1;9,1,80,1,188,1") = 0
  exact csv_relation_zero _ relation1720_mem
theorem relation1721_mem : "68,1,317,1;3,1,929,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block13[17]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1721_zero : nativeImage "68,1,317,1;3,1,929,1" = 0 := by
  change projection (relationPolynomial "68,1,317,1;3,1,929,1") = 0
  exact csv_relation_zero _ relation1721_mem
theorem relation1722_mem : "20,1,640,1;8,1,80,1,201,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block15[13]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1722_zero : nativeImage "20,1,640,1;8,1,80,1,201,1" = 0 := by
  change projection (relationPolynomial "20,1,640,1;8,1,80,1,201,1") = 0
  exact csv_relation_zero _ relation1722_mem
theorem relation1723_mem : "17,1,668,1;8,2,610,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block17[3]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1723_zero : nativeImage "17,1,668,1;8,2,610,1" = 0 := by
  change projection (relationPolynomial "17,1,668,1;8,2,610,1") = 0
  exact csv_relation_zero _ relation1723_mem
theorem relation1724_mem : "2,1,975,1;1,2,978,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block17[9]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1724_zero : nativeImage "2,1,975,1;1,2,978,1" = 0 := by
  change projection (relationPolynomial "2,1,975,1;1,2,978,1") = 0
  exact csv_relation_zero _ relation1724_mem
theorem relation1725_mem : "17,1,667,1;9,1,779,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block18[20]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1725_zero : nativeImage "17,1,667,1;9,1,779,1" = 0 := by
  change projection (relationPolynomial "17,1,667,1;9,1,779,1") = 0
  exact csv_relation_zero _ relation1725_mem
theorem relation1726_mem : "9,1,779,1;8,1,813,1;0,1,64,1,318,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block18[24]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1726_zero : nativeImage "9,1,779,1;8,1,813,1;0,1,64,1,318,1" = 0 := by
  change projection (relationPolynomial "9,1,779,1;8,1,813,1;0,1,64,1,318,1") = 0
  exact csv_relation_zero _ relation1726_mem
theorem relation1727_mem : "147,1,188,1;17,1,666,1;8,1,812,1;8,1,811,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block19[25]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1727_zero : nativeImage "147,1,188,1;17,1,666,1;8,1,812,1;8,1,811,1" = 0 := by
  change projection (relationPolynomial "147,1,188,1;17,1,666,1;8,1,812,1;8,1,811,1") = 0
  exact csv_relation_zero _ relation1727_mem
theorem relation1728_mem : "17,1,666,1;8,1,811,1;0,1,17,1,655,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block19[28]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1728_zero : nativeImage "17,1,666,1;8,1,811,1;0,1,17,1,655,1" = 0 := by
  change projection (relationPolynomial "17,1,666,1;8,1,811,1;0,1,17,1,655,1") = 0
  exact csv_relation_zero _ relation1728_mem
theorem relation1729_mem : "138,1,201,1;64,1,327,1;31,1,561,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block20[28]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1729_zero : nativeImage "138,1,201,1;64,1,327,1;31,1,561,1" = 0 := by
  change projection (relationPolynomial "138,1,201,1;64,1,327,1;31,1,561,1") = 0
  exact csv_relation_zero _ relation1729_mem
theorem relation1730_mem : "31,1,561,1;16,1,666,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block20[30]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1730_zero : nativeImage "31,1,561,1;16,1,666,1" = 0 := by
  change projection (relationPolynomial "31,1,561,1;16,1,666,1") = 0
  exact csv_relation_zero _ relation1730_mem
theorem relation1731_mem : "16,1,666,1;15,1,690,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block20[31]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1731_zero : nativeImage "16,1,666,1;15,1,690,1" = 0 := by
  change projection (relationPolynomial "16,1,666,1;15,1,690,1") = 0
  exact csv_relation_zero _ relation1731_mem
theorem relation1732_mem : "15,1,690,1;8,1,810,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block21[1]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1732_zero : nativeImage "15,1,690,1;8,1,810,1" = 0 := by
  change projection (relationPolynomial "15,1,690,1;8,1,810,1") = 0
  exact csv_relation_zero _ relation1732_mem
theorem relation1733_mem : "8,1,810,1;0,1,8,1,797,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block21[2]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1733_zero : nativeImage "8,1,810,1;0,1,8,1,797,1" = 0 := by
  change projection (relationPolynomial "8,1,810,1;0,1,8,1,797,1") = 0
  exact csv_relation_zero _ relation1733_mem
theorem relation1734_mem : "31,1,560,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block22[5]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1734_zero : nativeImage "31,1,560,1" = 0 := by
  change projection (relationPolynomial "31,1,560,1") = 0
  exact csv_relation_zero _ relation1734_mem
theorem relation1735_mem : "0,1,8,2,16,1,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block25[17]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1735_zero : nativeImage "0,1,8,2,16,1,292,1" = 0 := by
  change projection (relationPolynomial "0,1,8,2,16,1,292,1") = 0
  exact csv_relation_zero _ relation1735_mem
theorem relation1736_mem : "17,1,665,1;8,2,16,1,64,2" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block26[13]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1736_zero : nativeImage "17,1,665,1;8,2,16,1,64,2" = 0 := by
  change projection (relationPolynomial "17,1,665,1;8,2,16,1,64,2") = 0
  exact csv_relation_zero _ relation1736_mem
theorem relation1737_mem : "17,1,664,1;16,1,665,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block27[3]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1737_zero : nativeImage "17,1,664,1;16,1,665,1" = 0 := by
  change projection (relationPolynomial "17,1,664,1;16,1,665,1") = 0
  exact csv_relation_zero _ relation1737_mem
theorem relation1738_mem : "16,1,665,1;8,1,808,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block27[7]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1738_zero : nativeImage "16,1,665,1;8,1,808,1" = 0 := by
  change projection (relationPolynomial "16,1,665,1;8,1,808,1") = 0
  exact csv_relation_zero _ relation1738_mem
theorem relation1739_mem : "113,1,238,1;49,1,434,1;47,1,454,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block27[20]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1739_zero : nativeImage "113,1,238,1;49,1,434,1;47,1,454,1" = 0 := by
  change projection (relationPolynomial "113,1,238,1;49,1,434,1;47,1,454,1") = 0
  exact csv_relation_zero _ relation1739_mem
theorem relation1740_mem : "49,1,434,1;39,1,529,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block27[21]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1740_zero : nativeImage "49,1,434,1;39,1,529,1" = 0 := by
  change projection (relationPolynomial "49,1,434,1;39,1,529,1") = 0
  exact csv_relation_zero _ relation1740_mem
theorem relation1741_mem : "47,1,454,1;39,1,529,1;31,1,557,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block27[22]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1741_zero : nativeImage "47,1,454,1;39,1,529,1;31,1,557,1" = 0 := by
  change projection (relationPolynomial "47,1,454,1;39,1,529,1;31,1,557,1") = 0
  exact csv_relation_zero _ relation1741_mem
theorem relation1742_mem : "31,1,557,1;16,1,664,1;10,1,759,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block27[26]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1742_zero : nativeImage "31,1,557,1;16,1,664,1;10,1,759,1" = 0 := by
  change projection (relationPolynomial "31,1,557,1;16,1,664,1;10,1,759,1") = 0
  exact csv_relation_zero _ relation1742_mem
theorem relation1743_mem : "16,1,664,1;9,1,778,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block27[27]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1743_zero : nativeImage "16,1,664,1;9,1,778,1" = 0 := by
  change projection (relationPolynomial "16,1,664,1;9,1,778,1") = 0
  exact csv_relation_zero _ relation1743_mem
theorem relation1744_mem : "10,1,759,1;9,1,778,1;8,1,138,2" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block27[28]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1744_zero : nativeImage "10,1,759,1;9,1,778,1;8,1,138,2" = 0 := by
  change projection (relationPolynomial "10,1,759,1;9,1,778,1;8,1,138,2") = 0
  exact csv_relation_zero _ relation1744_mem
theorem relation1745_mem : "113,1,237,1;112,1,238,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block28[3]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1745_zero : nativeImage "113,1,237,1;112,1,238,1" = 0 := by
  change projection (relationPolynomial "113,1,237,1;112,1,238,1") = 0
  exact csv_relation_zero _ relation1745_mem
theorem relation1746_mem : "112,1,238,1;72,1,298,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block28[6]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1746_zero : nativeImage "112,1,238,1;72,1,298,1" = 0 := by
  change projection (relationPolynomial "112,1,238,1;72,1,298,1") = 0
  exact csv_relation_zero _ relation1746_mem
theorem relation1747_mem : "72,1,298,1;71,1,299,1;65,1,317,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block28[8]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1747_zero : nativeImage "72,1,298,1;71,1,299,1;65,1,317,1" = 0 := by
  change projection (relationPolynomial "72,1,298,1;71,1,299,1;65,1,317,1") = 0
  exact csv_relation_zero _ relation1747_mem
theorem relation1748_mem : "65,1,317,1;65,1,316,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block28[9]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1748_zero : nativeImage "65,1,317,1;65,1,316,1" = 0 := by
  change projection (relationPolynomial "65,1,317,1;65,1,316,1") = 0
  exact csv_relation_zero _ relation1748_mem
theorem relation1749_mem : "71,1,299,1;65,1,316,1;8,1,64,1,225,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block28[12]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1749_zero : nativeImage "71,1,299,1;65,1,316,1;8,1,64,1,225,1" = 0 := by
  change projection (relationPolynomial "71,1,299,1;65,1,316,1;8,1,64,1,225,1") = 0
  exact csv_relation_zero _ relation1749_mem
theorem relation1750_mem : "17,1,662,1;16,1,663,1;15,1,685,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block31[30]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1750_zero : nativeImage "17,1,662,1;16,1,663,1;15,1,685,1" = 0 := by
  change projection (relationPolynomial "17,1,662,1;16,1,663,1;15,1,685,1") = 0
  exact csv_relation_zero _ relation1750_mem
theorem relation1751_mem : "16,1,663,1;8,1,806,1" ∈ LinE2.RawData.relations := by
  exact relation_member 47 chunkBound rows transcription
    (block31[31]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1751_zero : nativeImage "16,1,663,1;8,1,806,1" = 0 := by
  change projection (relationPolynomial "16,1,663,1;8,1,806,1") = 0
  exact csv_relation_zero _ relation1751_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk047
