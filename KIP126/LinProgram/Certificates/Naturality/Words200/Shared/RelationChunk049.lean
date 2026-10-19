module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk049
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[49]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 49 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[49]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
private theorem block13_mem : block13 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 13) (by decide)
private theorem block13_in_rows (r : List Char) (hr : r ∈ block13) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block13, block13_mem, hr⟩
private theorem block20_mem : block20 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 20) (by decide)
private theorem block20_in_rows (r : List Char) (hr : r ∈ block20) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block20, block20_mem, hr⟩
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
private theorem block29_mem : block29 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 29) (by decide)
private theorem block29_in_rows (r : List Char) (hr : r ∈ block29) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block29, block29_mem, hr⟩
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
theorem relation1764_mem : "69,1,340,1;18,2,341,1" ∈ LinE2.RawData.relations := by
  exact relation_member 49 chunkBound rows transcription
    (block4[21]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1764_zero : nativeImage "69,1,340,1;18,2,341,1" = 0 := by
  change projection (relationPolynomial "69,1,340,1;18,2,341,1") = 0
  exact csv_relation_zero _ relation1764_mem
theorem relation1765_mem : "68,1,335,1;67,1,336,1" ∈ LinE2.RawData.relations := by
  exact relation_member 49 chunkBound rows transcription
    (block13[27]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1765_zero : nativeImage "68,1,335,1;67,1,336,1" = 0 := by
  change projection (relationPolynomial "68,1,335,1;67,1,336,1") = 0
  exact csv_relation_zero _ relation1765_mem
theorem relation1766_mem : "80,1,294,1;13,1,761,1" ∈ LinE2.RawData.relations := by
  exact relation_member 49 chunkBound rows transcription
    (block20[7]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1766_zero : nativeImage "80,1,294,1;13,1,761,1" = 0 := by
  change projection (relationPolynomial "80,1,294,1;13,1,761,1") = 0
  exact csv_relation_zero _ relation1766_mem
theorem relation1767_mem : "17,1,692,1;8,1,79,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 49 chunkBound rows transcription
    (block23[17]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1767_zero : nativeImage "17,1,692,1;8,1,79,1,209,1" = 0 := by
  change projection (relationPolynomial "17,1,692,1;8,1,79,1,209,1") = 0
  exact csv_relation_zero _ relation1767_mem
theorem relation1768_mem : "113,1,250,1;79,1,293,1" ∈ LinE2.RawData.relations := by
  exact relation_member 49 chunkBound rows transcription
    (block23[28]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1768_zero : nativeImage "113,1,250,1;79,1,293,1" = 0 := by
  change projection (relationPolynomial "113,1,250,1;79,1,293,1") = 0
  exact csv_relation_zero _ relation1768_mem
theorem relation1769_mem : "79,1,293,1;64,1,350,1" ∈ LinE2.RawData.relations := by
  exact relation_member 49 chunkBound rows transcription
    (block23[31]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1769_zero : nativeImage "79,1,293,1;64,1,350,1" = 0 := by
  change projection (relationPolynomial "79,1,293,1;64,1,350,1") = 0
  exact csv_relation_zero _ relation1769_mem
theorem relation1770_mem : "64,1,350,1;16,1,692,1" ∈ LinE2.RawData.relations := by
  exact relation_member 49 chunkBound rows transcription
    (block24[13]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1770_zero : nativeImage "64,1,350,1;16,1,692,1" = 0 := by
  change projection (relationPolynomial "64,1,350,1;16,1,692,1") = 0
  exact csv_relation_zero _ relation1770_mem
theorem relation1771_mem : "16,1,692,1;8,1,834,1" ∈ LinE2.RawData.relations := by
  exact relation_member 49 chunkBound rows transcription
    (block24[16]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1771_zero : nativeImage "16,1,692,1;8,1,834,1" = 0 := by
  change projection (relationPolynomial "16,1,692,1;8,1,834,1") = 0
  exact csv_relation_zero _ relation1771_mem
theorem relation1772_mem : "80,1,292,1;23,1,627,1;8,1,9,1,13,2,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 49 chunkBound rows transcription
    (block25[13]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1772_zero : nativeImage "80,1,292,1;23,1,627,1;8,1,9,1,13,2,209,1" = 0 := by
  change projection (relationPolynomial "80,1,292,1;23,1,627,1;8,1,9,1,13,2,209,1") = 0
  exact csv_relation_zero _ relation1772_mem
theorem relation1773_mem : "23,1,625,1;9,1,13,2,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 49 chunkBound rows transcription
    (block29[12]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1773_zero : nativeImage "23,1,625,1;9,1,13,2,292,1" = 0 := by
  change projection (relationPolynomial "23,1,625,1;9,1,13,2,292,1") = 0
  exact csv_relation_zero _ relation1773_mem
theorem relation1774_mem : "0,3,17,1,655,1" ∈ LinE2.RawData.relations := by
  exact relation_member 49 chunkBound rows transcription
    (block30[25]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1774_zero : nativeImage "0,3,17,1,655,1" = 0 := by
  change projection (relationPolynomial "0,3,17,1,655,1") = 0
  exact csv_relation_zero _ relation1774_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk049
