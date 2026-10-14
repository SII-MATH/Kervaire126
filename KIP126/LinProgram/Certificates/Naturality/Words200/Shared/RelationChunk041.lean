module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk041
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[41]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 41 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[41]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block3_mem : block3 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 3) (by decide)
private theorem block3_in_rows (r : List Char) (hr : r ∈ block3) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block3, block3_mem, hr⟩
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
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
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block27_mem : block27 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 27) (by decide)
private theorem block27_in_rows (r : List Char) (hr : r ∈ block27) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block27, block27_mem, hr⟩
theorem relation1602_mem : "0,1,16,1,598,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block3[29]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1602_zero : nativeImage "0,1,16,1,598,1" = 0 := by
  change projection (relationPolynomial "0,1,16,1,598,1") = 0
  exact csv_relation_zero _ relation1602_mem
theorem relation1603_mem : "0,1,16,1,64,1,149,1;0,1,8,2,16,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block4[20]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1603_zero : nativeImage "0,1,16,1,64,1,149,1;0,1,8,2,16,1,260,1" = 0 := by
  change projection (relationPolynomial "0,1,16,1,64,1,149,1;0,1,8,2,16,1,260,1") = 0
  exact csv_relation_zero _ relation1603_mem
theorem relation1604_mem : "0,1,8,1,722,1;0,12,807,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block8[21]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1604_zero : nativeImage "0,1,8,1,722,1;0,12,807,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,722,1;0,12,807,1") = 0
  exact csv_relation_zero _ relation1604_mem
theorem relation1605_mem : "17,1,607,1;17,1,606,1;8,4,236,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block9[25]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1605_zero : nativeImage "17,1,607,1;17,1,606,1;8,4,236,1" = 0 := by
  change projection (relationPolynomial "17,1,607,1;17,1,606,1;8,4,236,1") = 0
  exact csv_relation_zero _ relation1605_mem
theorem relation1606_mem : "17,1,606,1;0,3,917,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block9[26]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1606_zero : nativeImage "17,1,606,1;0,3,917,1" = 0 := by
  change projection (relationPolynomial "17,1,606,1;0,3,917,1") = 0
  exact csv_relation_zero _ relation1606_mem
theorem relation1607_mem : "17,2,296,1;8,1,736,1;0,3,916,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block10[10]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1607_zero : nativeImage "17,2,296,1;8,1,736,1;0,3,916,1" = 0 := by
  change projection (relationPolynomial "17,2,296,1;8,1,736,1;0,3,916,1") = 0
  exact csv_relation_zero _ relation1607_mem
theorem relation1608_mem : "2,2,885,1;1,1,13,1,660,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block12[5]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1608_zero : nativeImage "2,2,885,1;1,1,13,1,660,1" = 0 := by
  change projection (relationPolynomial "2,2,885,1;1,1,13,1,660,1") = 0
  exact csv_relation_zero _ relation1608_mem
theorem relation1609_mem : "76,1,270,1;69,1,287,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block13[24]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1609_zero : nativeImage "76,1,270,1;69,1,287,1" = 0 := by
  change projection (relationPolynomial "76,1,270,1;69,1,287,1") = 0
  exact csv_relation_zero _ relation1609_mem
theorem relation1610_mem : "74,1,270,1;69,1,285,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block14[30]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1610_zero : nativeImage "74,1,270,1;69,1,285,1" = 0 := by
  change projection (relationPolynomial "74,1,270,1;69,1,285,1") = 0
  exact csv_relation_zero _ relation1610_mem
theorem relation1611_mem : "69,1,285,1;3,1,882,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block15[27]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1611_zero : nativeImage "69,1,285,1;3,1,882,1" = 0 := by
  change projection (relationPolynomial "69,1,285,1;3,1,882,1") = 0
  exact csv_relation_zero _ relation1611_mem
theorem relation1612_mem : "133,1,190,1;67,1,288,1;52,1,373,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block17[15]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1612_zero : nativeImage "133,1,190,1;67,1,288,1;52,1,373,1" = 0 := by
  change projection (relationPolynomial "133,1,190,1;67,1,288,1;52,1,373,1") = 0
  exact csv_relation_zero _ relation1612_mem
theorem relation1613_mem : "52,1,373,1;51,1,376,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block17[16]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1613_zero : nativeImage "52,1,373,1;51,1,376,1" = 0 := by
  change projection (relationPolynomial "52,1,373,1;51,1,376,1") = 0
  exact csv_relation_zero _ relation1613_mem
theorem relation1614_mem : "51,1,376,1;24,1,569,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block17[25]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1614_zero : nativeImage "51,1,376,1;24,1,569,1" = 0 := by
  change projection (relationPolynomial "51,1,376,1;24,1,569,1") = 0
  exact csv_relation_zero _ relation1614_mem
theorem relation1615_mem : "24,1,569,1;23,1,570,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block17[26]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1615_zero : nativeImage "24,1,569,1;23,1,570,1" = 0 := by
  change projection (relationPolynomial "24,1,569,1;23,1,570,1") = 0
  exact csv_relation_zero _ relation1615_mem
theorem relation1616_mem : "23,1,570,1;13,1,682,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block17[30]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1616_zero : nativeImage "23,1,570,1;13,1,682,1" = 0 := by
  change projection (relationPolynomial "23,1,570,1;13,1,682,1") = 0
  exact csv_relation_zero _ relation1616_mem
theorem relation1617_mem : "67,1,288,1;13,1,682,1;13,1,681,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block17[31]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1617_zero : nativeImage "67,1,288,1;13,1,682,1;13,1,681,1" = 0 := by
  change projection (relationPolynomial "67,1,288,1;13,1,682,1;13,1,681,1") = 0
  exact csv_relation_zero _ relation1617_mem
theorem relation1618_mem : "23,1,569,1;13,1,680,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block18[31]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1618_zero : nativeImage "23,1,569,1;13,1,680,1" = 0 := by
  change projection (relationPolynomial "23,1,569,1;13,1,680,1") = 0
  exact csv_relation_zero _ relation1618_mem
theorem relation1619_mem : "13,1,680,1;13,2,450,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block19[0]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1619_zero : nativeImage "13,1,680,1;13,2,450,1" = 0 := by
  change projection (relationPolynomial "13,1,680,1;13,2,450,1") = 0
  exact csv_relation_zero _ relation1619_mem
theorem relation1620_mem : "75,1,268,1;13,1,679,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block20[12]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1620_zero : nativeImage "75,1,268,1;13,1,679,1" = 0 := by
  change projection (relationPolynomial "75,1,268,1;13,1,679,1") = 0
  exact csv_relation_zero _ relation1620_mem
theorem relation1621_mem : "68,1,286,1;68,1,285,1;67,1,287,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block20[31]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1621_zero : nativeImage "68,1,286,1;68,1,285,1;67,1,287,1" = 0 := by
  change projection (relationPolynomial "68,1,286,1;68,1,285,1;67,1,287,1") = 0
  exact csv_relation_zero _ relation1621_mem
theorem relation1622_mem : "75,1,267,1;68,1,285,1;67,1,287,1;13,1,677,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block21[13]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1622_zero : nativeImage "75,1,267,1;68,1,285,1;67,1,287,1;13,1,677,1" = 0 := by
  change projection (relationPolynomial "75,1,267,1;68,1,285,1;67,1,287,1;13,1,677,1") = 0
  exact csv_relation_zero _ relation1622_mem
theorem relation1623_mem : "68,1,285,1;0,1,960,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block21[21]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1623_zero : nativeImage "68,1,285,1;0,1,960,1" = 0 := by
  change projection (relationPolynomial "68,1,285,1;0,1,960,1") = 0
  exact csv_relation_zero _ relation1623_mem
theorem relation1624_mem : "73,1,267,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block21[27]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1624_zero : nativeImage "73,1,267,1" = 0 := by
  change projection (relationPolynomial "73,1,267,1") = 0
  exact csv_relation_zero _ relation1624_mem
theorem relation1625_mem : "75,1,266,1;67,1,286,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block21[29]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1625_zero : nativeImage "75,1,266,1;67,1,286,1" = 0 := by
  change projection (relationPolynomial "75,1,266,1;67,1,286,1") = 0
  exact csv_relation_zero _ relation1625_mem
theorem relation1626_mem : "1,1,8,1,729,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block25[18]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1626_zero : nativeImage "1,1,8,1,729,1" = 0 := by
  change projection (relationPolynomial "1,1,8,1,729,1") = 0
  exact csv_relation_zero _ relation1626_mem
theorem relation1627_mem : "0,6,891,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block25[19]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1627_zero : nativeImage "0,6,891,1" = 0 := by
  change projection (relationPolynomial "0,6,891,1") = 0
  exact csv_relation_zero _ relation1627_mem
theorem relation1628_mem : "2,2,876,1;1,1,941,1" ∈ LinE2.RawData.relations := by
  exact relation_member 41 chunkBound rows transcription
    (block27[13]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1628_zero : nativeImage "2,2,876,1;1,1,941,1" = 0 := by
  change projection (relationPolynomial "2,2,876,1;1,1,941,1") = 0
  exact csv_relation_zero _ relation1628_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk041
