module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk023
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[23]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 23 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[23]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
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
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
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
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
private theorem block14_mem : block14 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 14) (by decide)
private theorem block14_in_rows (r : List Char) (hr : r ∈ block14) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block14, block14_mem, hr⟩
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
theorem relation1002_mem : "0,1,8,1,16,1,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block1[12]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1002_zero : nativeImage "0,1,8,1,16,1,244,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,16,1,244,1") = 0
  exact csv_relation_zero _ relation1002_mem
theorem relation1003_mem : "17,1,402,1;16,1,403,1;0,1,685,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block2[10]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1003_zero : nativeImage "17,1,402,1;16,1,403,1;0,1,685,1" = 0 := by
  change projection (relationPolynomial "17,1,402,1;16,1,403,1;0,1,685,1") = 0
  exact csv_relation_zero _ relation1003_mem
theorem relation1004_mem : "17,1,401,1;8,4,152,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block3[0]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1004_zero : nativeImage "17,1,401,1;8,4,152,1" = 0 := by
  change projection (relationPolynomial "17,1,401,1;8,4,152,1") = 0
  exact csv_relation_zero _ relation1004_mem
theorem relation1005_mem : "17,2,200,1;9,1,498,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block3[21]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1005_zero : nativeImage "17,2,200,1;9,1,498,1" = 0 := by
  change projection (relationPolynomial "17,2,200,1;9,1,498,1") = 0
  exact csv_relation_zero _ relation1005_mem
theorem relation1006_mem : "9,1,498,1;8,1,528,1;0,3,662,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block3[23]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1006_zero : nativeImage "9,1,498,1;8,1,528,1;0,3,662,1" = 0 := by
  change projection (relationPolynomial "9,1,498,1;8,1,528,1;0,3,662,1") = 0
  exact csv_relation_zero _ relation1006_mem
theorem relation1007_mem : "18,1,399,1;7,2,400,1;1,1,699,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block4[5]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1007_zero : nativeImage "18,1,399,1;7,2,400,1;1,1,699,1" = 0 := by
  change projection (relationPolynomial "18,1,399,1;7,2,400,1;1,1,699,1") = 0
  exact csv_relation_zero _ relation1007_mem
theorem relation1008_mem : "1,1,699,1;0,1,18,1,378,1;0,1,2,1,660,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block4[7]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1008_zero : nativeImage "1,1,699,1;0,1,18,1,378,1;0,1,2,1,660,1" = 0 := by
  change projection (relationPolynomial "1,1,699,1;0,1,18,1,378,1;0,1,2,1,660,1") = 0
  exact csv_relation_zero _ relation1008_mem
theorem relation1009_mem : "69,1,191,1;18,1,397,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block4[9]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1009_zero : nativeImage "69,1,191,1;18,1,397,1" = 0 := by
  change projection (relationPolynomial "69,1,191,1;18,1,397,1") = 0
  exact csv_relation_zero _ relation1009_mem
theorem relation1010_mem : "18,1,397,1;18,1,396,1;11,1,506,1;7,2,398,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block4[14]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1010_zero : nativeImage "18,1,397,1;18,1,396,1;11,1,506,1;7,2,398,1" = 0 := by
  change projection (relationPolynomial "18,1,397,1;18,1,396,1;11,1,506,1;7,2,398,1") = 0
  exact csv_relation_zero _ relation1010_mem
theorem relation1011_mem : "18,1,396,1;1,1,698,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block4[15]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1011_zero : nativeImage "18,1,396,1;1,1,698,1" = 0 := by
  change projection (relationPolynomial "18,1,396,1;1,1,698,1") = 0
  exact csv_relation_zero _ relation1011_mem
theorem relation1012_mem : "11,1,506,1;1,1,18,1,368,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block4[16]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1012_zero : nativeImage "11,1,506,1;1,1,18,1,368,1" = 0 := by
  change projection (relationPolynomial "11,1,506,1;1,1,18,1,368,1") = 0
  exact csv_relation_zero _ relation1012_mem
theorem relation1013_mem : "1,1,698,1;0,2,699,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block4[17]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1013_zero : nativeImage "1,1,698,1;0,2,699,1" = 0 := by
  change projection (relationPolynomial "1,1,698,1;0,2,699,1") = 0
  exact csv_relation_zero _ relation1013_mem
theorem relation1014_mem : "18,1,394,1;18,1,393,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block4[21]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1014_zero : nativeImage "18,1,394,1;18,1,393,1" = 0 := by
  change projection (relationPolynomial "18,1,394,1;18,1,393,1") = 0
  exact csv_relation_zero _ relation1014_mem
theorem relation1015_mem : "18,1,390,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block5[7]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1015_zero : nativeImage "18,1,390,1" = 0 := by
  change projection (relationPolynomial "18,1,390,1") = 0
  exact csv_relation_zero _ relation1015_mem
theorem relation1016_mem : "18,1,391,1;3,1,633,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block5[12]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1016_zero : nativeImage "18,1,391,1;3,1,633,1" = 0 := by
  change projection (relationPolynomial "18,1,391,1;3,1,633,1") = 0
  exact csv_relation_zero _ relation1016_mem
theorem relation1017_mem : "3,1,633,1;1,1,7,1,546,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block5[13]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1017_zero : nativeImage "3,1,633,1;1,1,7,1,546,1" = 0 := by
  change projection (relationPolynomial "3,1,633,1;1,1,7,1,546,1") = 0
  exact csv_relation_zero _ relation1017_mem
theorem relation1018_mem : "68,1,190,1;67,1,191,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block8[0]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1018_zero : nativeImage "68,1,190,1;67,1,191,1" = 0 := by
  change projection (relationPolynomial "68,1,190,1;67,1,191,1") = 0
  exact csv_relation_zero _ relation1018_mem
theorem relation1019_mem : "23,1,338,1;13,1,486,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block9[0]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1019_zero : nativeImage "23,1,338,1;13,1,486,1" = 0 := by
  change projection (relationPolynomial "23,1,338,1;13,1,486,1") = 0
  exact csv_relation_zero _ relation1019_mem
theorem relation1020_mem : "13,1,486,1;13,1,485,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block9[1]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1020_zero : nativeImage "13,1,486,1;13,1,485,1" = 0 := by
  change projection (relationPolynomial "13,1,486,1;13,1,485,1") = 0
  exact csv_relation_zero _ relation1020_mem
theorem relation1021_mem : "68,1,189,1;3,1,630,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block10[5]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1021_zero : nativeImage "68,1,189,1;3,1,630,1" = 0 := by
  change projection (relationPolynomial "68,1,189,1;3,1,630,1") = 0
  exact csv_relation_zero _ relation1021_mem
theorem relation1022_mem : "2,1,669,1;1,1,694,1;1,2,671,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block10[9]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1022_zero : nativeImage "2,1,669,1;1,1,694,1;1,2,671,1" = 0 := by
  change projection (relationPolynomial "2,1,669,1;1,1,694,1;1,2,671,1") = 0
  exact csv_relation_zero _ relation1022_mem
theorem relation1023_mem : "1,2,671,1;0,1,17,1,415,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block10[11]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1023_zero : nativeImage "1,2,671,1;0,1,17,1,415,1" = 0 := by
  change projection (relationPolynomial "1,2,671,1;0,1,17,1,415,1") = 0
  exact csv_relation_zero _ relation1023_mem
theorem relation1024_mem : "17,1,419,1;15,1,445,1;13,1,483,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block11[1]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1024_zero : nativeImage "17,1,419,1;15,1,445,1;13,1,483,1" = 0 := by
  change projection (relationPolynomial "17,1,419,1;15,1,445,1;13,1,483,1") = 0
  exact csv_relation_zero _ relation1024_mem
theorem relation1025_mem : "15,1,445,1;10,1,502,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block11[2]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1025_zero : nativeImage "15,1,445,1;10,1,502,1" = 0 := by
  change projection (relationPolynomial "15,1,445,1;10,1,502,1") = 0
  exact csv_relation_zero _ relation1025_mem
theorem relation1026_mem : "13,1,483,1;10,1,502,1;8,1,540,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block11[3]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1026_zero : nativeImage "13,1,483,1;10,1,502,1;8,1,540,1" = 0 := by
  change projection (relationPolynomial "13,1,483,1;10,1,502,1;8,1,540,1") = 0
  exact csv_relation_zero _ relation1026_mem
theorem relation1027_mem : "2,2,630,1;1,2,669,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block11[7]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1027_zero : nativeImage "2,2,630,1;1,2,669,1" = 0 := by
  change projection (relationPolynomial "2,2,630,1;1,2,669,1") = 0
  exact csv_relation_zero _ relation1027_mem
theorem relation1028_mem : "8,1,540,1;8,2,338,1;0,1,8,1,534,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block11[9]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1028_zero : nativeImage "8,1,540,1;8,2,338,1;0,1,8,1,534,1" = 0 := by
  change projection (relationPolynomial "8,1,540,1;8,2,338,1;0,1,8,1,534,1") = 0
  exact csv_relation_zero _ relation1028_mem
theorem relation1029_mem : "8,2,337,1;7,1,561,1;1,1,693,1;1,1,692,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block11[26]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1029_zero : nativeImage "8,2,337,1;7,1,561,1;1,1,693,1;1,1,692,1" = 0 := by
  change projection (relationPolynomial "8,2,337,1;7,1,561,1;1,1,693,1;1,1,692,1") = 0
  exact csv_relation_zero _ relation1029_mem
theorem relation1030_mem : "7,1,561,1;0,1,8,2,333,1;0,4,671,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block11[29]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1030_zero : nativeImage "7,1,561,1;0,1,8,2,333,1;0,4,671,1" = 0 := by
  change projection (relationPolynomial "7,1,561,1;0,1,8,2,333,1;0,4,671,1") = 0
  exact csv_relation_zero _ relation1030_mem
theorem relation1031_mem : "66,1,188,1;3,1,627,1;1,1,690,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block14[16]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1031_zero : nativeImage "66,1,188,1;3,1,627,1;1,1,690,1" = 0 := by
  change projection (relationPolynomial "66,1,188,1;3,1,627,1;1,1,690,1") = 0
  exact csv_relation_zero _ relation1031_mem
theorem relation1032_mem : "69,1,192,1;18,1,413,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block25[31]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1032_zero : nativeImage "69,1,192,1;18,1,413,1" = 0 := by
  change projection (relationPolynomial "69,1,192,1;18,1,413,1") = 0
  exact csv_relation_zero _ relation1032_mem
theorem relation1033_mem : "18,1,413,1;7,1,571,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block26[3]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1033_zero : nativeImage "18,1,413,1;7,1,571,1" = 0 := by
  change projection (relationPolynomial "18,1,413,1;7,1,571,1") = 0
  exact csv_relation_zero _ relation1033_mem
theorem relation1034_mem : "1,1,714,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block26[5]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1034_zero : nativeImage "1,1,714,1" = 0 := by
  change projection (relationPolynomial "1,1,714,1") = 0
  exact csv_relation_zero _ relation1034_mem
theorem relation1035_mem : "23,1,69,1,76,1;18,1,411,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block26[12]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1035_zero : nativeImage "23,1,69,1,76,1;18,1,411,1" = 0 := by
  change projection (relationPolynomial "23,1,69,1,76,1;18,1,411,1") = 0
  exact csv_relation_zero _ relation1035_mem
theorem relation1036_mem : "23,1,69,1,75,1;18,1,408,1" ∈ LinE2.RawData.relations := by
  exact relation_member 23 chunkBound rows transcription
    (block27[5]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1036_zero : nativeImage "23,1,69,1,75,1;18,1,408,1" = 0 := by
  change projection (relationPolynomial "23,1,69,1,75,1;18,1,408,1") = 0
  exact csv_relation_zero _ relation1036_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk023
