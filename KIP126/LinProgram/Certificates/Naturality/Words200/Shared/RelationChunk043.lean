module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk043
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[43]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 43 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[43]'(chunkBound) =
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
private theorem block7_mem : block7 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 7) (by decide)
private theorem block7_in_rows (r : List Char) (hr : r ∈ block7) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block7, block7_mem, hr⟩
private theorem block23_mem : block23 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 23) (by decide)
private theorem block23_in_rows (r : List Char) (hr : r ∈ block23) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block23, block23_mem, hr⟩
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
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
theorem relation1639_mem : "17,1,625,1;8,2,9,1,346,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block0[7]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1639_zero : nativeImage "17,1,625,1;8,2,9,1,346,1" = 0 := by
  change projection (relationPolynomial "17,1,625,1;8,2,9,1,346,1") = 0
  exact csv_relation_zero _ relation1639_mem
theorem relation1640_mem : "17,1,20,1,292,1;16,1,625,1;15,1,643,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block1[24]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1640_zero : nativeImage "17,1,20,1,292,1;16,1,625,1;15,1,643,1" = 0 := by
  change projection (relationPolynomial "17,1,20,1,292,1;16,1,625,1;15,1,643,1") = 0
  exact csv_relation_zero _ relation1640_mem
theorem relation1641_mem : "16,1,625,1;8,1,42,1,278,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block1[26]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1641_zero : nativeImage "16,1,625,1;8,1,42,1,278,1" = 0 := by
  change projection (relationPolynomial "16,1,625,1;8,1,42,1,278,1") = 0
  exact csv_relation_zero _ relation1641_mem
theorem relation1642_mem : "0,1,8,1,753,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block1[30]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1642_zero : nativeImage "0,1,8,1,753,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,753,1") = 0
  exact csv_relation_zero _ relation1642_mem
theorem relation1643_mem : "15,1,643,1;0,3,64,1,278,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block1[31]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1643_zero : nativeImage "15,1,643,1;0,3,64,1,278,1" = 0 := by
  change projection (relationPolynomial "15,1,643,1;0,3,64,1,278,1") = 0
  exact csv_relation_zero _ relation1643_mem
theorem relation1644_mem : "17,1,624,1;13,1,688,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block2[22]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1644_zero : nativeImage "17,1,624,1;13,1,688,1" = 0 := by
  change projection (relationPolynomial "17,1,624,1;13,1,688,1") = 0
  exact csv_relation_zero _ relation1644_mem
theorem relation1645_mem : "13,1,688,1;9,1,726,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block2[23]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1645_zero : nativeImage "13,1,688,1;9,1,726,1" = 0 := by
  change projection (relationPolynomial "13,1,688,1;9,1,726,1") = 0
  exact csv_relation_zero _ relation1645_mem
theorem relation1646_mem : "9,1,726,1;8,2,573,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block2[25]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1646_zero : nativeImage "9,1,726,1;8,2,573,1" = 0 := by
  change projection (relationPolynomial "9,1,726,1;8,2,573,1") = 0
  exact csv_relation_zero _ relation1646_mem
theorem relation1647_mem : "17,1,64,1,160,1;15,1,642,1;8,1,113,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block3[19]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1647_zero : nativeImage "17,1,64,1,160,1;15,1,642,1;8,1,113,1,149,1" = 0 := by
  change projection (relationPolynomial "17,1,64,1,160,1;15,1,642,1;8,1,113,1,149,1") = 0
  exact csv_relation_zero _ relation1647_mem
theorem relation1648_mem : "15,1,642,1;0,1,149,1,160,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block3[21]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1648_zero : nativeImage "15,1,642,1;0,1,149,1,160,1" = 0 := by
  change projection (relationPolynomial "15,1,642,1;0,1,149,1,160,1") = 0
  exact csv_relation_zero _ relation1648_mem
theorem relation1649_mem : "0,1,149,1,160,1;0,4,64,1,274,1;0,6,897,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block3[23]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1649_zero : nativeImage "0,1,149,1,160,1;0,4,64,1,274,1;0,6,897,1" = 0 := by
  change projection (relationPolynomial "0,1,149,1,160,1;0,4,64,1,274,1;0,6,897,1") = 0
  exact csv_relation_zero _ relation1649_mem
theorem relation1650_mem : "110,1,218,1;77,1,258,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block7[23]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1650_zero : nativeImage "110,1,218,1;77,1,258,1" = 0 := by
  change projection (relationPolynomial "110,1,218,1;77,1,258,1") = 0
  exact csv_relation_zero _ relation1650_mem
theorem relation1651_mem : "77,1,258,1;71,1,277,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block7[24]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1651_zero : nativeImage "77,1,258,1;71,1,277,1" = 0 := by
  change projection (relationPolynomial "77,1,258,1;71,1,277,1") = 0
  exact csv_relation_zero _ relation1651_mem
theorem relation1652_mem : "71,1,277,1;55,1,344,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block7[26]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1652_zero : nativeImage "71,1,277,1;55,1,344,1" = 0 := by
  change projection (relationPolynomial "71,1,277,1;55,1,344,1") = 0
  exact csv_relation_zero _ relation1652_mem
theorem relation1653_mem : "55,1,344,1;39,1,489,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block7[27]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1653_zero : nativeImage "55,1,344,1;39,1,489,1" = 0 := by
  change projection (relationPolynomial "55,1,344,1;39,1,489,1") = 0
  exact csv_relation_zero _ relation1653_mem
theorem relation1654_mem : "39,1,489,1;19,1,596,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block7[28]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1654_zero : nativeImage "39,1,489,1;19,1,596,1" = 0 := by
  change projection (relationPolynomial "39,1,489,1;19,1,596,1") = 0
  exact csv_relation_zero _ relation1654_mem
theorem relation1655_mem : "19,1,596,1;13,1,686,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block7[29]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1655_zero : nativeImage "19,1,596,1;13,1,686,1" = 0 := by
  change projection (relationPolynomial "19,1,596,1;13,1,686,1") = 0
  exact csv_relation_zero _ relation1655_mem
theorem relation1656_mem : "13,1,686,1;9,1,723,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block7[30]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1656_zero : nativeImage "13,1,686,1;9,1,723,1" = 0 := by
  change projection (relationPolynomial "13,1,686,1;9,1,723,1") = 0
  exact csv_relation_zero _ relation1656_mem
theorem relation1657_mem : "9,1,723,1;8,1,49,1,245,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block7[31]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1657_zero : nativeImage "9,1,723,1;8,1,49,1,245,1" = 0 := by
  change projection (relationPolynomial "9,1,723,1;8,1,49,1,245,1") = 0
  exact csv_relation_zero _ relation1657_mem
theorem relation1658_mem : "8,3,415,1;7,1,798,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block23[15]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1658_zero : nativeImage "8,3,415,1;7,1,798,1" = 0 := by
  change projection (relationPolynomial "8,3,415,1;7,1,798,1") = 0
  exact csv_relation_zero _ relation1658_mem
theorem relation1659_mem : "7,1,798,1;5,1,825,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block23[17]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1659_zero : nativeImage "7,1,798,1;5,1,825,1" = 0 := by
  change projection (relationPolynomial "7,1,798,1;5,1,825,1") = 0
  exact csv_relation_zero _ relation1659_mem
theorem relation1660_mem : "119,1,209,1;64,1,308,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block26[9]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1660_zero : nativeImage "119,1,209,1;64,1,308,1" = 0 := by
  change projection (relationPolynomial "119,1,209,1;64,1,308,1") = 0
  exact csv_relation_zero _ relation1660_mem
theorem relation1661_mem : "80,1,267,1;13,1,705,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block27[1]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1661_zero : nativeImage "80,1,267,1;13,1,705,1" = 0 := by
  change projection (relationPolynomial "80,1,267,1;13,1,705,1") = 0
  exact csv_relation_zero _ relation1661_mem
theorem relation1662_mem : "23,1,581,1;13,2,473,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block28[17]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1662_zero : nativeImage "23,1,581,1;13,2,473,1" = 0 := by
  change projection (relationPolynomial "23,1,581,1;13,2,473,1") = 0
  exact csv_relation_zero _ relation1662_mem
theorem relation1663_mem : "17,1,640,1;8,1,79,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 43 chunkBound rows transcription
    (block30[16]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1663_zero : nativeImage "17,1,640,1;8,1,79,1,188,1" = 0 := by
  change projection (relationPolynomial "17,1,640,1;8,1,79,1,188,1") = 0
  exact csv_relation_zero _ relation1663_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk043
