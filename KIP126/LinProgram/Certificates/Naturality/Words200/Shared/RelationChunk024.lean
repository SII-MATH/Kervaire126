module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk024
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[24]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 24 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[24]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
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
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
private theorem block15_mem : block15 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 15) (by decide)
private theorem block15_in_rows (r : List Char) (hr : r ∈ block15) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block15, block15_mem, hr⟩
private theorem block16_mem : block16 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 16) (by decide)
private theorem block16_in_rows (r : List Char) (hr : r ∈ block16) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block16, block16_mem, hr⟩
private theorem block18_mem : block18 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 18) (by decide)
private theorem block18_in_rows (r : List Char) (hr : r ∈ block18) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block18, block18_mem, hr⟩
private theorem block19_mem : block19 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 19) (by decide)
private theorem block19_in_rows (r : List Char) (hr : r ∈ block19) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block19, block19_mem, hr⟩
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
private theorem block27_mem : block27 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 27) (by decide)
private theorem block27_in_rows (r : List Char) (hr : r ∈ block27) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block27, block27_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
theorem relation1037_mem : "17,1,423,1;8,2,13,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block4[12]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1037_zero : nativeImage "17,1,423,1;8,2,13,1,209,1" = 0 := by
  change projection (relationPolynomial "17,1,423,1;8,2,13,1,209,1") = 0
  exact csv_relation_zero _ relation1037_mem
theorem relation1038_mem : "32,1,292,1;23,1,346,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block5[31]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1038_zero : nativeImage "32,1,292,1;23,1,346,1" = 0 := by
  change projection (relationPolynomial "32,1,292,1;23,1,346,1") = 0
  exact csv_relation_zero _ relation1038_mem
theorem relation1039_mem : "17,2,209,1;8,2,348,1;0,2,64,1,187,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block6[10]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1039_zero : nativeImage "17,2,209,1;8,2,348,1;0,2,64,1,187,1" = 0 := by
  change projection (relationPolynomial "17,2,209,1;8,2,348,1;0,2,64,1,187,1") = 0
  exact csv_relation_zero _ relation1039_mem
theorem relation1040_mem : "16,1,17,1,209,1;9,1,518,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block7[8]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1040_zero : nativeImage "16,1,17,1,209,1;9,1,518,1" = 0 := by
  change projection (relationPolynomial "16,1,17,1,209,1;9,1,518,1") = 0
  exact csv_relation_zero _ relation1040_mem
theorem relation1041_mem : "9,1,518,1;8,1,550,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block7[9]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1041_zero : nativeImage "9,1,518,1;8,1,550,1" = 0 := by
  change projection (relationPolynomial "9,1,518,1;8,1,550,1") = 0
  exact csv_relation_zero _ relation1041_mem
theorem relation1042_mem : "22,1,346,1;8,1,13,1,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block7[10]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1042_zero : nativeImage "22,1,346,1;8,1,13,1,292,1" = 0 := by
  change projection (relationPolynomial "22,1,346,1;8,1,13,1,292,1") = 0
  exact csv_relation_zero _ relation1042_mem
theorem relation1043_mem : "17,1,420,1;9,1,517,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block8[0]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1043_zero : nativeImage "17,1,420,1;9,1,517,1" = 0 := by
  change projection (relationPolynomial "17,1,420,1;9,1,517,1") = 0
  exact csv_relation_zero _ relation1043_mem
theorem relation1044_mem : "9,1,517,1;8,2,347,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block8[1]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1044_zero : nativeImage "9,1,517,1;8,2,347,1" = 0 := by
  change projection (relationPolynomial "9,1,517,1;8,2,347,1") = 0
  exact csv_relation_zero _ relation1044_mem
theorem relation1045_mem : "31,1,291,1;19,1,380,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block9[17]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1045_zero : nativeImage "31,1,291,1;19,1,380,1" = 0 := by
  change projection (relationPolynomial "31,1,291,1;19,1,380,1") = 0
  exact csv_relation_zero _ relation1045_mem
theorem relation1046_mem : "19,1,380,1;13,1,491,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block9[18]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1046_zero : nativeImage "19,1,380,1;13,1,491,1" = 0 := by
  change projection (relationPolynomial "19,1,380,1;13,1,491,1") = 0
  exact csv_relation_zero _ relation1046_mem
theorem relation1047_mem : "13,1,491,1;9,1,516,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block9[20]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1047_zero : nativeImage "13,1,491,1;9,1,516,1" = 0 := by
  change projection (relationPolynomial "13,1,491,1;9,1,516,1") = 0
  exact csv_relation_zero _ relation1047_mem
theorem relation1048_mem : "9,1,516,1;8,1,16,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block9[21]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1048_zero : nativeImage "9,1,516,1;8,1,16,1,260,1" = 0 := by
  change projection (relationPolynomial "9,1,516,1;8,1,16,1,260,1") = 0
  exact csv_relation_zero _ relation1048_mem
theorem relation1049_mem : "0,6,654,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block9[24]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1049_zero : nativeImage "0,6,654,1" = 0 := by
  change projection (relationPolynomial "0,6,654,1") = 0
  exact csv_relation_zero _ relation1049_mem
theorem relation1050_mem : "17,2,206,1;13,1,489,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block11[30]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1050_zero : nativeImage "17,2,206,1;13,1,489,1" = 0 := by
  change projection (relationPolynomial "17,2,206,1;13,1,489,1") = 0
  exact csv_relation_zero _ relation1050_mem
theorem relation1051_mem : "13,1,489,1;8,2,344,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block11[31]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1051_zero : nativeImage "13,1,489,1;8,2,344,1" = 0 := by
  change projection (relationPolynomial "13,1,489,1;8,2,344,1") = 0
  exact csv_relation_zero _ relation1051_mem
theorem relation1052_mem : "2,1,696,1;1,1,720,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block15[15]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1052_zero : nativeImage "2,1,696,1;1,1,720,1" = 0 := by
  change projection (relationPolynomial "2,1,696,1;1,1,720,1") = 0
  exact csv_relation_zero _ relation1052_mem
theorem relation1053_mem : "24,1,368,1;18,1,419,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block16[2]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1053_zero : nativeImage "24,1,368,1;18,1,419,1" = 0 := by
  change projection (relationPolynomial "24,1,368,1;18,1,419,1") = 0
  exact csv_relation_zero _ relation1053_mem
theorem relation1054_mem : "23,1,367,1;18,1,418,1;8,1,564,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block18[2]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1054_zero : nativeImage "23,1,367,1;18,1,418,1;8,1,564,1" = 0 := by
  change projection (relationPolynomial "23,1,367,1;18,1,418,1;8,1,564,1") = 0
  exact csv_relation_zero _ relation1054_mem
theorem relation1055_mem : "8,1,564,1;8,1,563,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block18[3]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1055_zero : nativeImage "8,1,564,1;8,1,563,1" = 0 := by
  change projection (relationPolynomial "8,1,564,1;8,1,563,1") = 0
  exact csv_relation_zero _ relation1055_mem
theorem relation1056_mem : "18,1,418,1;0,6,676,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block18[8]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1056_zero : nativeImage "18,1,418,1;0,6,676,1" = 0 := by
  change projection (relationPolynomial "18,1,418,1;0,6,676,1") = 0
  exact csv_relation_zero _ relation1056_mem
theorem relation1057_mem : "17,1,445,1;8,1,562,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block18[25]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1057_zero : nativeImage "17,1,445,1;8,1,562,1" = 0 := by
  change projection (relationPolynomial "17,1,445,1;8,1,562,1") = 0
  exact csv_relation_zero _ relation1057_mem
theorem relation1058_mem : "17,1,443,1;16,1,445,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block19[11]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1058_zero : nativeImage "17,1,443,1;16,1,445,1" = 0 := by
  change projection (relationPolynomial "17,1,443,1;16,1,445,1") = 0
  exact csv_relation_zero _ relation1058_mem
theorem relation1059_mem : "16,1,445,1;9,1,534,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block19[15]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1059_zero : nativeImage "16,1,445,1;9,1,534,1" = 0 := by
  change projection (relationPolynomial "16,1,445,1;9,1,534,1") = 0
  exact csv_relation_zero _ relation1059_mem
theorem relation1060_mem : "9,1,534,1;8,2,367,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block19[16]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1060_zero : nativeImage "9,1,534,1;8,2,367,1" = 0 := by
  change projection (relationPolynomial "9,1,534,1;8,2,367,1") = 0
  exact csv_relation_zero _ relation1060_mem
theorem relation1061_mem : "68,1,195,1;43,1,267,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block21[8]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1061_zero : nativeImage "68,1,195,1;43,1,267,1" = 0 := by
  change projection (relationPolynomial "68,1,195,1;43,1,267,1") = 0
  exact csv_relation_zero _ relation1061_mem
theorem relation1062_mem : "23,1,364,1;9,1,13,1,288,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block22[0]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1062_zero : nativeImage "23,1,364,1;9,1,13,1,288,1" = 0 := by
  change projection (relationPolynomial "23,1,364,1;9,1,13,1,288,1") = 0
  exact csv_relation_zero _ relation1062_mem
theorem relation1063_mem : "2,1,691,1;1,1,3,1,629,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block22[6]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1063_zero : nativeImage "2,1,691,1;1,1,3,1,629,1" = 0 := by
  change projection (relationPolynomial "2,1,691,1;1,1,3,1,629,1") = 0
  exact csv_relation_zero _ relation1063_mem
theorem relation1064_mem : "23,1,360,1;13,2,268,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block25[30]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1064_zero : nativeImage "23,1,360,1;13,2,268,1" = 0 := by
  change projection (relationPolynomial "23,1,360,1;13,2,268,1") = 0
  exact csv_relation_zero _ relation1064_mem
theorem relation1065_mem : "23,1,359,1;9,1,13,1,286,1;3,1,644,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block27[26]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1065_zero : nativeImage "23,1,359,1;9,1,13,1,286,1;3,1,644,1" = 0 := by
  change projection (relationPolynomial "23,1,359,1;9,1,13,1,286,1;3,1,644,1") = 0
  exact csv_relation_zero _ relation1065_mem
theorem relation1066_mem : "3,1,644,1;0,2,717,1;0,3,706,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block27[31]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1066_zero : nativeImage "3,1,644,1;0,2,717,1;0,3,706,1" = 0 := by
  change projection (relationPolynomial "3,1,644,1;0,2,717,1;0,3,706,1") = 0
  exact csv_relation_zero _ relation1066_mem
theorem relation1067_mem : "23,1,357,1;13,2,266,1" ∈ LinE2.RawData.relations := by
  exact relation_member 24 chunkBound rows transcription
    (block28[28]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1067_zero : nativeImage "23,1,357,1;13,2,266,1" = 0 := by
  change projection (relationPolynomial "23,1,357,1;13,2,266,1") = 0
  exact csv_relation_zero _ relation1067_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk024
