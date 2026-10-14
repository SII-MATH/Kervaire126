module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk016
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[16]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 16 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[16]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block1_mem : block1 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 1) (by decide)
private theorem block1_in_rows (r : List Char) (hr : r ∈ block1) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block1, block1_mem, hr⟩
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
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
private theorem block20_mem : block20 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 20) (by decide)
private theorem block20_in_rows (r : List Char) (hr : r ∈ block20) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block20, block20_mem, hr⟩
private theorem block27_mem : block27 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 27) (by decide)
private theorem block27_in_rows (r : List Char) (hr : r ∈ block27) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block27, block27_mem, hr⟩
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation789_mem : "9,1,359,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block1[8]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation789_zero : nativeImage "9,1,359,1" = 0 := by
  change projection (relationPolynomial "9,1,359,1") = 0
  exact csv_relation_zero _ relation789_mem
theorem relation790_mem : "46,1,188,1;9,1,13,1,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block1[9]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation790_zero : nativeImage "46,1,188,1;9,1,13,1,212,1" = 0 := by
  change projection (relationPolynomial "46,1,188,1;9,1,13,1,212,1") = 0
  exact csv_relation_zero _ relation790_mem
theorem relation791_mem : "72,1,138,1;64,1,147,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block4[21]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation791_zero : nativeImage "72,1,138,1;64,1,147,1" = 0 := by
  change projection (relationPolynomial "72,1,138,1;64,1,147,1") = 0
  exact csv_relation_zero _ relation791_mem
theorem relation792_mem : "72,1,137,1;64,1,146,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block4[30]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation792_zero : nativeImage "72,1,137,1;64,1,146,1" = 0 := by
  change projection (relationPolynomial "72,1,137,1;64,1,146,1") = 0
  exact csv_relation_zero _ relation792_mem
theorem relation793_mem : "17,2,154,1;8,5,64,1;0,3,64,1,138,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block5[26]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation793_zero : nativeImage "17,2,154,1;8,5,64,1;0,3,64,1,138,1" = 0 := by
  change projection (relationPolynomial "17,2,154,1;8,5,64,1;0,3,64,1,138,1") = 0
  exact csv_relation_zero _ relation793_mem
theorem relation794_mem : "16,1,17,1,154,1;8,1,42,1,137,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block6[9]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation794_zero : nativeImage "16,1,17,1,154,1;8,1,42,1,137,1" = 0 := by
  change projection (relationPolynomial "16,1,17,1,154,1;8,1,42,1,137,1") = 0
  exact csv_relation_zero _ relation794_mem
theorem relation795_mem : "0,1,8,2,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block7[5]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation795_zero : nativeImage "0,1,8,2,244,1" = 0 := by
  change projection (relationPolynomial "0,1,8,2,244,1") = 0
  exact csv_relation_zero _ relation795_mem
theorem relation796_mem : "71,1,138,1;31,1,225,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block7[28]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation796_zero : nativeImage "71,1,138,1;31,1,225,1" = 0 := by
  change projection (relationPolynomial "71,1,138,1;31,1,225,1") = 0
  exact csv_relation_zero _ relation796_mem
theorem relation797_mem : "31,1,225,1;8,1,403,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block7[29]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation797_zero : nativeImage "31,1,225,1;8,1,403,1" = 0 := by
  change projection (relationPolynomial "31,1,225,1;8,1,403,1") = 0
  exact csv_relation_zero _ relation797_mem
theorem relation798_mem : "17,1,283,1;8,4,116,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block8[18]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation798_zero : nativeImage "17,1,283,1;8,4,116,1" = 0 := by
  change projection (relationPolynomial "17,1,283,1;8,4,116,1") = 0
  exact csv_relation_zero _ relation798_mem
theorem relation799_mem : "17,2,153,1;9,1,354,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block9[6]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation799_zero : nativeImage "17,2,153,1;9,1,354,1" = 0 := by
  change projection (relationPolynomial "17,2,153,1;9,1,354,1") = 0
  exact csv_relation_zero _ relation799_mem
theorem relation800_mem : "9,1,354,1;8,1,401,1;0,3,555,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block9[8]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation800_zero : nativeImage "9,1,354,1;8,1,401,1;0,3,555,1" = 0 := by
  change projection (relationPolynomial "9,1,354,1;8,1,401,1;0,3,555,1") = 0
  exact csv_relation_zero _ relation800_mem
theorem relation801_mem : "2,2,526,1;1,1,3,1,506,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block9[21]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation801_zero : nativeImage "2,2,526,1;1,1,3,1,506,1" = 0 := by
  change projection (relationPolynomial "2,2,526,1;1,1,3,1,506,1") = 0
  exact csv_relation_zero _ relation801_mem
theorem relation802_mem : "2,1,563,1;1,1,3,1,504,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block10[30]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation802_zero : nativeImage "2,1,563,1;1,1,3,1,504,1" = 0 := by
  change projection (relationPolynomial "2,1,563,1;1,1,3,1,504,1") = 0
  exact csv_relation_zero _ relation802_mem
theorem relation803_mem : "13,1,338,1;9,1,373,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block12[6]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation803_zero : nativeImage "13,1,338,1;9,1,373,1" = 0 := by
  change projection (relationPolynomial "13,1,338,1;9,1,373,1") = 0
  exact csv_relation_zero _ relation803_mem
theorem relation804_mem : "9,1,69,1,80,1;8,1,419,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block12[29]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation804_zero : nativeImage "9,1,69,1,80,1;8,1,419,1" = 0 := by
  change projection (relationPolynomial "9,1,69,1,80,1;8,1,419,1") = 0
  exact csv_relation_zero _ relation804_mem
theorem relation805_mem : "0,1,8,2,255,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block20[23]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation805_zero : nativeImage "0,1,8,2,255,1" = 0 := by
  change projection (relationPolynomial "0,1,8,2,255,1") = 0
  exact csv_relation_zero _ relation805_mem
theorem relation806_mem : "11,1,376,1;7,1,450,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block27[21]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation806_zero : nativeImage "11,1,376,1;7,1,450,1" = 0 := by
  change projection (relationPolynomial "11,1,376,1;7,1,450,1") = 0
  exact csv_relation_zero _ relation806_mem
theorem relation807_mem : "23,1,263,1;13,1,67,1,76,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block30[21]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation807_zero : nativeImage "23,1,263,1;13,1,67,1,76,1" = 0 := by
  change projection (relationPolynomial "23,1,263,1;13,1,67,1,76,1") = 0
  exact csv_relation_zero _ relation807_mem
theorem relation808_mem : "13,1,67,1,76,1;9,1,18,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block30[23]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation808_zero : nativeImage "13,1,67,1,76,1;9,1,18,1,188,1" = 0 := by
  change projection (relationPolynomial "13,1,67,1,76,1;9,1,18,1,188,1") = 0
  exact csv_relation_zero _ relation808_mem
theorem relation809_mem : "9,1,18,1,188,1;8,1,426,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block30[24]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation809_zero : nativeImage "9,1,18,1,188,1;8,1,426,1" = 0 := by
  change projection (relationPolynomial "9,1,18,1,188,1;8,1,426,1") = 0
  exact csv_relation_zero _ relation809_mem
theorem relation810_mem : "8,1,426,1;8,1,425,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block30[25]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation810_zero : nativeImage "8,1,426,1;8,1,425,1" = 0 := by
  change projection (relationPolynomial "8,1,426,1;8,1,425,1") = 0
  exact csv_relation_zero _ relation810_mem
theorem relation811_mem : "23,1,262,1;13,1,67,1,75,1" ∈ LinE2.RawData.relations := by
  exact relation_member 16 chunkBound rows transcription
    (block31[19]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation811_zero : nativeImage "23,1,262,1;13,1,67,1,75,1" = 0 := by
  change projection (relationPolynomial "23,1,262,1;13,1,67,1,75,1") = 0
  exact csv_relation_zero _ relation811_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk016
