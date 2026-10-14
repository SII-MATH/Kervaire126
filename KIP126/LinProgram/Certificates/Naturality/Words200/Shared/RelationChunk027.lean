module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk027
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[27]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 27 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[27]'(chunkBound) =
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
private theorem block5_mem : block5 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 5) (by decide)
private theorem block5_in_rows (r : List Char) (hr : r ∈ block5) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block5, block5_mem, hr⟩
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
private theorem block15_mem : block15 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 15) (by decide)
private theorem block15_in_rows (r : List Char) (hr : r ∈ block15) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block15, block15_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
private theorem block17_mem : block17 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 17) (by decide)
private theorem block17_in_rows (r : List Char) (hr : r ∈ block17) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block17, block17_mem, hr⟩
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
theorem relation1141_mem : "69,1,206,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block0[26]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1141_zero : nativeImage "69,1,206,1" = 0 := by
  change projection (relationPolynomial "69,1,206,1") = 0
  exact csv_relation_zero _ relation1141_mem
theorem relation1142_mem : "80,1,187,1;79,1,188,1;0,1,64,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block1[23]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1142_zero : nativeImage "80,1,187,1;79,1,188,1;0,1,64,1,209,1" = 0 := by
  change projection (relationPolynomial "80,1,187,1;79,1,188,1;0,1,64,1,209,1") = 0
  exact csv_relation_zero _ relation1142_mem
theorem relation1143_mem : "32,1,328,1;13,2,286,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block2[23]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1143_zero : nativeImage "32,1,328,1;13,2,286,1" = 0 := by
  change projection (relationPolynomial "32,1,328,1;13,2,286,1") = 0
  exact csv_relation_zero _ relation1143_mem
theorem relation1144_mem : "0,7,693,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block5[6]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1144_zero : nativeImage "0,7,693,1" = 0 := by
  change projection (relationPolynomial "0,7,693,1") = 0
  exact csv_relation_zero _ relation1144_mem
theorem relation1145_mem : "20,1,435,1;8,3,254,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block8[4]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1145_zero : nativeImage "20,1,435,1;8,3,254,1" = 0 := by
  change projection (relationPolynomial "20,1,435,1;8,3,254,1") = 0
  exact csv_relation_zero _ relation1145_mem
theorem relation1146_mem : "17,1,471,1;14,1,510,1;9,1,559,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block8[25]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1146_zero : nativeImage "17,1,471,1;14,1,510,1;9,1,559,1" = 0 := by
  change projection (relationPolynomial "17,1,471,1;14,1,510,1;9,1,559,1") = 0
  exact csv_relation_zero _ relation1146_mem
theorem relation1147_mem : "14,1,510,1;9,1,558,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block8[26]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1147_zero : nativeImage "14,1,510,1;9,1,558,1" = 0 := by
  change projection (relationPolynomial "14,1,510,1;9,1,558,1") = 0
  exact csv_relation_zero _ relation1147_mem
theorem relation1148_mem : "9,1,559,1;8,1,580,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block8[27]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1148_zero : nativeImage "9,1,559,1;8,1,580,1" = 0 := by
  change projection (relationPolynomial "9,1,559,1;8,1,580,1") = 0
  exact csv_relation_zero _ relation1148_mem
theorem relation1149_mem : "9,1,558,1;0,1,17,1,454,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block8[30]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1149_zero : nativeImage "9,1,558,1;0,1,17,1,454,1" = 0 := by
  change projection (relationPolynomial "9,1,558,1;0,1,17,1,454,1") = 0
  exact csv_relation_zero _ relation1149_mem
theorem relation1150_mem : "17,1,64,1,113,1;13,1,529,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block9[18]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1150_zero : nativeImage "17,1,64,1,113,1;13,1,529,1" = 0 := by
  change projection (relationPolynomial "17,1,64,1,113,1;13,1,529,1") = 0
  exact csv_relation_zero _ relation1150_mem
theorem relation1151_mem : "13,1,529,1;8,2,404,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block9[20]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1151_zero : nativeImage "13,1,529,1;8,2,404,1" = 0 := by
  change projection (relationPolynomial "13,1,529,1;8,2,404,1") = 0
  exact csv_relation_zero _ relation1151_mem
theorem relation1152_mem : "0,1,64,1,206,1;0,1,8,2,380,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block10[11]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1152_zero : nativeImage "0,1,64,1,206,1;0,1,8,2,380,1" = 0 := by
  change projection (relationPolynomial "0,1,64,1,206,1;0,1,8,2,380,1") = 0
  exact csv_relation_zero _ relation1152_mem
theorem relation1153_mem : "17,1,469,1;16,1,470,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block15[23]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1153_zero : nativeImage "17,1,469,1;16,1,470,1" = 0 := by
  change projection (relationPolynomial "17,1,469,1;16,1,470,1") = 0
  exact csv_relation_zero _ relation1153_mem
theorem relation1154_mem : "16,1,470,1;9,1,554,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block15[24]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1154_zero : nativeImage "16,1,470,1;9,1,554,1" = 0 := by
  change projection (relationPolynomial "16,1,470,1;9,1,554,1") = 0
  exact csv_relation_zero _ relation1154_mem
theorem relation1155_mem : "9,1,554,1;8,1,579,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block15[25]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1155_zero : nativeImage "9,1,554,1;8,1,579,1" = 0 := by
  change projection (relationPolynomial "9,1,554,1;8,1,579,1") = 0
  exact csv_relation_zero _ relation1155_mem
theorem relation1156_mem : "2,1,750,1;1,2,751,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block16[25]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1156_zero : nativeImage "2,1,750,1;1,2,751,1" = 0 := by
  change projection (relationPolynomial "2,1,750,1;1,2,751,1") = 0
  exact csv_relation_zero _ relation1156_mem
theorem relation1157_mem : "4,1,660,1;2,2,699,1;1,1,18,1,446,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block17[9]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1157_zero : nativeImage "4,1,660,1;2,2,699,1;1,1,18,1,446,1" = 0 := by
  change projection (relationPolynomial "4,1,660,1;2,2,699,1;1,1,18,1,446,1") = 0
  exact csv_relation_zero _ relation1157_mem
theorem relation1158_mem : "2,1,748,1;2,2,699,1;1,2,749,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block17[10]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1158_zero : nativeImage "2,1,748,1;2,2,699,1;1,2,749,1" = 0 := by
  change projection (relationPolynomial "2,1,748,1;2,2,699,1;1,2,749,1") = 0
  exact csv_relation_zero _ relation1158_mem
theorem relation1159_mem : "2,2,699,1;0,4,751,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block17[11]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1159_zero : nativeImage "2,2,699,1;0,4,751,1" = 0 := by
  change projection (relationPolynomial "2,2,699,1;0,4,751,1") = 0
  exact csv_relation_zero _ relation1159_mem
theorem relation1160_mem : "2,2,698,1;1,1,776,1;1,2,748,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block17[19]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1160_zero : nativeImage "2,2,698,1;1,1,776,1;1,2,748,1" = 0 := by
  change projection (relationPolynomial "2,2,698,1;1,1,776,1;1,2,748,1") = 0
  exact csv_relation_zero _ relation1160_mem
theorem relation1161_mem : "1,1,776,1;1,2,748,1;1,2,747,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block17[20]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1161_zero : nativeImage "1,1,776,1;1,2,748,1;1,2,747,1" = 0 := by
  change projection (relationPolynomial "1,1,776,1;1,2,748,1;1,2,747,1") = 0
  exact csv_relation_zero _ relation1161_mem
theorem relation1162_mem : "23,1,419,1;13,1,542,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block23[24]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1162_zero : nativeImage "23,1,419,1;13,1,542,1" = 0 := by
  change projection (relationPolynomial "23,1,419,1;13,1,542,1") = 0
  exact csv_relation_zero _ relation1162_mem
theorem relation1163_mem : "13,1,542,1;13,1,541,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block23[25]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1163_zero : nativeImage "13,1,542,1;13,1,541,1" = 0 := by
  change projection (relationPolynomial "13,1,542,1;13,1,541,1") = 0
  exact csv_relation_zero _ relation1163_mem
theorem relation1164_mem : "13,1,541,1;9,1,569,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block23[26]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1164_zero : nativeImage "13,1,541,1;9,1,569,1" = 0 := by
  change projection (relationPolynomial "13,1,541,1;9,1,569,1") = 0
  exact csv_relation_zero _ relation1164_mem
theorem relation1165_mem : "17,1,486,1;8,2,419,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block26[19]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1165_zero : nativeImage "17,1,486,1;8,2,419,1" = 0 := by
  change projection (relationPolynomial "17,1,486,1;8,2,419,1") = 0
  exact csv_relation_zero _ relation1165_mem
theorem relation1166_mem : "8,2,419,1;3,1,692,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block26[21]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1166_zero : nativeImage "8,2,419,1;3,1,692,1" = 0 := by
  change projection (relationPolynomial "8,2,419,1;3,1,692,1") = 0
  exact csv_relation_zero _ relation1166_mem
theorem relation1167_mem : "3,1,692,1;1,1,762,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block26[23]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1167_zero : nativeImage "3,1,692,1;1,1,762,1" = 0 := by
  change projection (relationPolynomial "3,1,692,1;1,1,762,1") = 0
  exact csv_relation_zero _ relation1167_mem
theorem relation1168_mem : "73,1,201,1;48,1,261,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block27[9]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1168_zero : nativeImage "73,1,201,1;48,1,261,1" = 0 := by
  change projection (relationPolynomial "73,1,201,1;48,1,261,1") = 0
  exact csv_relation_zero _ relation1168_mem
theorem relation1169_mem : "8,2,69,1,89,1;7,1,611,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block27[24]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1169_zero : nativeImage "8,2,69,1,89,1;7,1,611,1" = 0 := by
  change projection (relationPolynomial "8,2,69,1,89,1;7,1,611,1") = 0
  exact csv_relation_zero _ relation1169_mem
theorem relation1170_mem : "7,1,611,1;1,1,761,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block27[26]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1170_zero : nativeImage "7,1,611,1;1,1,761,1" = 0 := by
  change projection (relationPolynomial "7,1,611,1;1,1,761,1") = 0
  exact csv_relation_zero _ relation1170_mem
theorem relation1171_mem : "17,1,483,1;1,1,760,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block28[26]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1171_zero : nativeImage "17,1,483,1;1,1,760,1" = 0 := by
  change projection (relationPolynomial "17,1,483,1;1,1,760,1") = 0
  exact csv_relation_zero _ relation1171_mem
theorem relation1172_mem : "0,1,80,1,188,1;0,2,760,1" ∈ LinE2.RawData.relations := by
  exact relation_member 27 chunkBound rows transcription
    (block30[5]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1172_zero : nativeImage "0,1,80,1,188,1;0,2,760,1" = 0 := by
  change projection (relationPolynomial "0,1,80,1,188,1;0,2,760,1") = 0
  exact csv_relation_zero _ relation1172_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk027
