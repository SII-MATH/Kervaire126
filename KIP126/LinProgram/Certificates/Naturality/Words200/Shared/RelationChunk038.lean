module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk038
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[38]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 38 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[38]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
private theorem block7_mem : block7 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 7) (by decide)
private theorem block7_in_rows (r : List Char) (hr : r ∈ block7) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block7, block7_mem, hr⟩
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
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
private theorem block26_mem : block26 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 26) (by decide)
private theorem block26_in_rows (r : List Char) (hr : r ∈ block26) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block26, block26_mem, hr⟩
private theorem block27_mem : block27 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 27) (by decide)
private theorem block27_in_rows (r : List Char) (hr : r ∈ block27) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block27, block27_mem, hr⟩
theorem relation1521_mem : "17,1,578,1;16,1,579,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block4[20]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1521_zero : nativeImage "17,1,578,1;16,1,579,1" = 0 := by
  change projection (relationPolynomial "17,1,578,1;16,1,579,1") = 0
  exact csv_relation_zero _ relation1521_mem
theorem relation1522_mem : "16,1,579,1;8,1,701,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block4[21]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1522_zero : nativeImage "16,1,579,1;8,1,701,1" = 0 := by
  change projection (relationPolynomial "16,1,579,1;8,1,701,1") = 0
  exact csv_relation_zero _ relation1522_mem
theorem relation1523_mem : "70,1,264,1;7,1,746,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block7[6]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1523_zero : nativeImage "70,1,264,1;7,1,746,1" = 0 := by
  change projection (relationPolynomial "70,1,264,1;7,1,746,1") = 0
  exact csv_relation_zero _ relation1523_mem
theorem relation1524_mem : "68,1,270,1;8,1,719,1;3,1,843,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block11[19]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1524_zero : nativeImage "68,1,270,1;8,1,719,1;3,1,843,1" = 0 := by
  change projection (relationPolynomial "68,1,270,1;8,1,719,1;3,1,843,1") = 0
  exact csv_relation_zero _ relation1524_mem
theorem relation1525_mem : "8,1,719,1;6,1,746,1;0,2,8,3,324,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block11[22]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1525_zero : nativeImage "8,1,719,1;6,1,746,1;0,2,8,3,324,1" = 0 := by
  change projection (relationPolynomial "8,1,719,1;6,1,746,1;0,2,8,3,324,1") = 0
  exact csv_relation_zero _ relation1525_mem
theorem relation1526_mem : "6,1,746,1;0,2,8,3,324,1;0,2,3,1,817,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block11[23]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1526_zero : nativeImage "6,1,746,1;0,2,8,3,324,1;0,2,3,1,817,1" = 0 := by
  change projection (relationPolynomial "6,1,746,1;0,2,8,3,324,1;0,2,3,1,817,1") = 0
  exact csv_relation_zero _ relation1526_mem
theorem relation1527_mem : "23,1,541,1;9,1,680,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block16[23]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1527_zero : nativeImage "23,1,541,1;9,1,680,1" = 0 := by
  change projection (relationPolynomial "23,1,541,1;9,1,680,1") = 0
  exact csv_relation_zero _ relation1527_mem
theorem relation1528_mem : "9,1,680,1;9,1,13,1,450,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block16[24]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1528_zero : nativeImage "9,1,680,1;9,1,13,1,450,1" = 0 := by
  change projection (relationPolynomial "9,1,680,1;9,1,13,1,450,1") = 0
  exact csv_relation_zero _ relation1528_mem
theorem relation1529_mem : "52,1,335,1;13,1,649,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block19[23]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1529_zero : nativeImage "52,1,335,1;13,1,649,1" = 0 := by
  change projection (relationPolynomial "52,1,335,1;13,1,649,1") = 0
  exact csv_relation_zero _ relation1529_mem
theorem relation1530_mem : "13,1,649,1;13,1,648,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block19[24]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1530_zero : nativeImage "13,1,649,1;13,1,648,1" = 0 := by
  change projection (relationPolynomial "13,1,649,1;13,1,648,1") = 0
  exact csv_relation_zero _ relation1530_mem
theorem relation1531_mem : "13,1,648,1;9,1,677,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block19[26]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1531_zero : nativeImage "13,1,648,1;9,1,677,1" = 0 := by
  change projection (relationPolynomial "13,1,648,1;9,1,677,1") = 0
  exact csv_relation_zero _ relation1531_mem
theorem relation1532_mem : "68,1,266,1;67,1,267,1;51,1,335,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block20[17]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1532_zero : nativeImage "68,1,266,1;67,1,267,1;51,1,335,1" = 0 := by
  change projection (relationPolynomial "68,1,266,1;67,1,267,1;51,1,335,1") = 0
  exact csv_relation_zero _ relation1532_mem
theorem relation1533_mem : "51,1,335,1;13,2,417,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block20[27]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1533_zero : nativeImage "51,1,335,1;13,2,417,1" = 0 := by
  change projection (relationPolynomial "51,1,335,1;13,2,417,1") = 0
  exact csv_relation_zero _ relation1533_mem
theorem relation1534_mem : "73,1,255,1;48,1,350,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block21[15]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1534_zero : nativeImage "73,1,255,1;48,1,350,1" = 0 := by
  change projection (relationPolynomial "73,1,255,1;48,1,350,1") = 0
  exact csv_relation_zero _ relation1534_mem
theorem relation1535_mem : "2,2,833,1;1,1,13,1,628,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block22[31]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1535_zero : nativeImage "2,2,833,1;1,1,13,1,628,1" = 0 := by
  change projection (relationPolynomial "2,2,833,1;1,1,13,1,628,1") = 0
  exact csv_relation_zero _ relation1535_mem
theorem relation1536_mem : "17,1,18,1,278,1;8,1,69,1,185,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block26[18]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1536_zero : nativeImage "17,1,18,1,278,1;8,1,69,1,185,1" = 0 := by
  change projection (relationPolynomial "17,1,18,1,278,1;8,1,69,1,185,1") = 0
  exact csv_relation_zero _ relation1536_mem
theorem relation1537_mem : "0,1,8,1,64,1,187,1" ∈ LinE2.RawData.relations := by
  exact relation_member 38 chunkBound rows transcription
    (block27[19]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1537_zero : nativeImage "0,1,8,1,64,1,187,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,64,1,187,1") = 0
  exact csv_relation_zero _ relation1537_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk038
