module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk019
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[19]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 19 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[19]'(chunkBound) =
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
private theorem block4_mem : block4 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 4) (by decide)
private theorem block4_in_rows (r : List Char) (hr : r ∈ block4) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block4, block4_mem, hr⟩
private theorem block6_mem : block6 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 6) (by decide)
private theorem block6_in_rows (r : List Char) (hr : r ∈ block6) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block6, block6_mem, hr⟩
private theorem block10_mem : block10 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 10) (by decide)
private theorem block10_in_rows (r : List Char) (hr : r ∈ block10) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block10, block10_mem, hr⟩
private theorem block12_mem : block12 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 12) (by decide)
private theorem block12_in_rows (r : List Char) (hr : r ∈ block12) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block12, block12_mem, hr⟩
private theorem block14_mem : block14 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 14) (by decide)
private theorem block14_in_rows (r : List Char) (hr : r ∈ block14) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block14, block14_mem, hr⟩
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
theorem relation881_mem : "13,1,414,1;9,1,443,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block0[2]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation881_zero : nativeImage "13,1,414,1;9,1,443,1" = 0 := by
  change projection (relationPolynomial "13,1,414,1;9,1,443,1") = 0
  exact csv_relation_zero _ relation881_mem
theorem relation882_mem : "9,1,443,1;8,1,479,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block0[3]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation882_zero : nativeImage "9,1,443,1;8,1,479,1" = 0 := by
  change projection (relationPolynomial "9,1,443,1;8,1,479,1") = 0
  exact csv_relation_zero _ relation882_mem
theorem relation883_mem : "25,1,288,1;13,1,412,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block0[25]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation883_zero : nativeImage "25,1,288,1;13,1,412,1" = 0 := by
  change projection (relationPolynomial "25,1,288,1;13,1,412,1") = 0
  exact csv_relation_zero _ relation883_mem
theorem relation884_mem : "13,1,412,1;8,1,478,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block0[30]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation884_zero : nativeImage "13,1,412,1;8,1,478,1" = 0 := by
  change projection (relationPolynomial "13,1,412,1;8,1,478,1") = 0
  exact csv_relation_zero _ relation884_mem
theorem relation885_mem : "8,1,478,1;7,1,496,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block0[31]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation885_zero : nativeImage "8,1,478,1;7,1,496,1" = 0 := by
  change projection (relationPolynomial "8,1,478,1;7,1,496,1") = 0
  exact csv_relation_zero _ relation885_mem
theorem relation886_mem : "7,1,496,1;5,1,513,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block1[1]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation886_zero : nativeImage "7,1,496,1;5,1,513,1" = 0 := by
  change projection (relationPolynomial "7,1,496,1;5,1,513,1") = 0
  exact csv_relation_zero _ relation886_mem
theorem relation887_mem : "5,1,513,1;4,1,543,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block1[2]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation887_zero : nativeImage "5,1,513,1;4,1,543,1" = 0 := by
  change projection (relationPolynomial "5,1,513,1;4,1,543,1") = 0
  exact csv_relation_zero _ relation887_mem
theorem relation888_mem : "4,1,543,1;1,1,621,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block1[3]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation888_zero : nativeImage "4,1,543,1;1,1,621,1" = 0 := by
  change projection (relationPolynomial "4,1,543,1;1,1,621,1") = 0
  exact csv_relation_zero _ relation888_mem
theorem relation889_mem : "24,1,288,1;13,1,411,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block1[14]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation889_zero : nativeImage "24,1,288,1;13,1,411,1" = 0 := by
  change projection (relationPolynomial "24,1,288,1;13,1,411,1") = 0
  exact csv_relation_zero _ relation889_mem
theorem relation890_mem : "23,1,288,1;13,1,408,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block2[5]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation890_zero : nativeImage "23,1,288,1;13,1,408,1" = 0 := by
  change projection (relationPolynomial "23,1,288,1;13,1,408,1") = 0
  exact csv_relation_zero _ relation890_mem
theorem relation891_mem : "69,1,160,1;14,1,375,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block2[27]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation891_zero : nativeImage "69,1,160,1;14,1,375,1" = 0 := by
  change projection (relationPolynomial "69,1,160,1;14,1,375,1") = 0
  exact csv_relation_zero _ relation891_mem
theorem relation892_mem : "2,1,604,1;1,1,618,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block3[4]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation892_zero : nativeImage "2,1,604,1;1,1,618,1" = 0 := by
  change projection (relationPolynomial "2,1,604,1;1,1,618,1") = 0
  exact csv_relation_zero _ relation892_mem
theorem relation893_mem : "24,1,287,1;7,1,493,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block4[0]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation893_zero : nativeImage "24,1,287,1;7,1,493,1" = 0 := by
  change projection (relationPolynomial "24,1,287,1;7,1,493,1") = 0
  exact csv_relation_zero _ relation893_mem
theorem relation894_mem : "7,1,493,1;1,2,604,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block4[2]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation894_zero : nativeImage "7,1,493,1;1,2,604,1" = 0 := by
  change projection (relationPolynomial "7,1,493,1;1,2,604,1") = 0
  exact csv_relation_zero _ relation894_mem
theorem relation895_mem : "29,1,267,1;9,1,23,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block6[25]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation895_zero : nativeImage "29,1,267,1;9,1,23,1,188,1" = 0 := by
  change projection (relationPolynomial "29,1,267,1;9,1,23,1,188,1") = 0
  exact csv_relation_zero _ relation895_mem
theorem relation896_mem : "17,1,327,1;8,1,471,1;2,1,598,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block10[6]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation896_zero : nativeImage "17,1,327,1;8,1,471,1;2,1,598,1" = 0 := by
  change projection (relationPolynomial "17,1,327,1;8,1,471,1;2,1,598,1") = 0
  exact csv_relation_zero _ relation896_mem
theorem relation897_mem : "0,1,624,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block10[7]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation897_zero : nativeImage "0,1,624,1" = 0 := by
  change projection (relationPolynomial "0,1,624,1") = 0
  exact csv_relation_zero _ relation897_mem
theorem relation898_mem : "2,1,598,1;0,5,586,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block10[9]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation898_zero : nativeImage "2,1,598,1;0,5,586,1" = 0 := by
  change projection (relationPolynomial "2,1,598,1;0,5,586,1") = 0
  exact csv_relation_zero _ relation898_mem
theorem relation899_mem : "0,1,64,1,160,1;0,1,8,2,278,1;0,4,601,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block10[27]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation899_zero : nativeImage "0,1,64,1,160,1;0,1,8,2,278,1;0,4,601,1" = 0 := by
  change projection (relationPolynomial "0,1,64,1,160,1;0,1,8,2,278,1;0,4,601,1") = 0
  exact csv_relation_zero _ relation899_mem
theorem relation900_mem : "88,1,138,1;42,1,225,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block12[9]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation900_zero : nativeImage "88,1,138,1;42,1,225,1" = 0 := by
  change projection (relationPolynomial "88,1,138,1;42,1,225,1") = 0
  exact csv_relation_zero _ relation900_mem
theorem relation901_mem : "42,1,225,1;8,4,137,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block12[12]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation901_zero : nativeImage "42,1,225,1;8,4,137,1" = 0 := by
  change projection (relationPolynomial "42,1,225,1;8,4,137,1") = 0
  exact csv_relation_zero _ relation901_mem
theorem relation902_mem : "13,1,402,1;9,1,432,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block14[15]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation902_zero : nativeImage "13,1,402,1;9,1,432,1" = 0 := by
  change projection (relationPolynomial "13,1,402,1;9,1,432,1") = 0
  exact csv_relation_zero _ relation902_mem
theorem relation903_mem : "9,1,432,1;8,1,16,1,224,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block14[16]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation903_zero : nativeImage "9,1,432,1;8,1,16,1,224,1" = 0 := by
  change projection (relationPolynomial "9,1,432,1;8,1,16,1,224,1") = 0
  exact csv_relation_zero _ relation903_mem
theorem relation904_mem : "17,1,325,1;16,1,326,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block15[23]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation904_zero : nativeImage "17,1,325,1;16,1,326,1" = 0 := by
  change projection (relationPolynomial "17,1,325,1;16,1,326,1") = 0
  exact csv_relation_zero _ relation904_mem
theorem relation905_mem : "16,1,326,1;8,1,470,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block15[24]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation905_zero : nativeImage "16,1,326,1;8,1,470,1" = 0 := by
  change projection (relationPolynomial "16,1,326,1;8,1,470,1") = 0
  exact csv_relation_zero _ relation905_mem
theorem relation906_mem : "9,1,431,1;8,1,469,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block16[2]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation906_zero : nativeImage "9,1,431,1;8,1,469,1" = 0 := by
  change projection (relationPolynomial "9,1,431,1;8,1,469,1") = 0
  exact csv_relation_zero _ relation906_mem
theorem relation907_mem : "7,2,323,1;3,1,577,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block17[2]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation907_zero : nativeImage "7,2,323,1;3,1,577,1" = 0 := by
  change projection (relationPolynomial "7,2,323,1;3,1,577,1") = 0
  exact csv_relation_zero _ relation907_mem
theorem relation908_mem : "3,2,504,1;1,1,16,1,69,2;0,2,17,1,69,2" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block17[20]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation908_zero : nativeImage "3,2,504,1;1,1,16,1,69,2;0,2,17,1,69,2" = 0 := by
  change projection (relationPolynomial "3,2,504,1;1,1,16,1,69,2;0,2,17,1,69,2") = 0
  exact csv_relation_zero _ relation908_mem
theorem relation909_mem : "2,1,615,1;1,1,631,1;0,1,18,1,311,1;0,1,7,2,314,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block18[2]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation909_zero : nativeImage "2,1,615,1;1,1,631,1;0,1,18,1,311,1;0,1,7,2,314,1" = 0 := by
  change projection (relationPolynomial "2,1,615,1;1,1,631,1;0,1,18,1,311,1;0,1,7,2,314,1") = 0
  exact csv_relation_zero _ relation909_mem
theorem relation910_mem : "0,1,8,1,479,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block19[13]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation910_zero : nativeImage "0,1,8,1,479,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,479,1") = 0
  exact csv_relation_zero _ relation910_mem
theorem relation911_mem : "9,1,18,1,209,1;8,1,486,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block20[4]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation911_zero : nativeImage "9,1,18,1,209,1;8,1,486,1" = 0 := by
  change projection (relationPolynomial "9,1,18,1,209,1;8,1,486,1") = 0
  exact csv_relation_zero _ relation911_mem
theorem relation912_mem : "17,1,337,1;16,1,338,1;15,1,367,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block21[21]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation912_zero : nativeImage "17,1,337,1;16,1,338,1;15,1,367,1" = 0 := by
  change projection (relationPolynomial "17,1,337,1;16,1,338,1;15,1,367,1") = 0
  exact csv_relation_zero _ relation912_mem
theorem relation913_mem : "16,1,338,1;8,1,483,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block21[30]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation913_zero : nativeImage "16,1,338,1;8,1,483,1" = 0 := by
  change projection (relationPolynomial "16,1,338,1;8,1,483,1") = 0
  exact csv_relation_zero _ relation913_mem
theorem relation914_mem : "15,1,367,1;2,1,613,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block21[31]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation914_zero : nativeImage "15,1,367,1;2,1,613,1" = 0 := by
  change projection (relationPolynomial "15,1,367,1;2,1,613,1") = 0
  exact csv_relation_zero _ relation914_mem
theorem relation915_mem : "2,1,613,1;0,1,17,1,333,1" ∈ LinE2.RawData.relations := by
  exact relation_member 19 chunkBound rows transcription
    (block22[0]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation915_zero : nativeImage "2,1,613,1;0,1,17,1,333,1" = 0 := by
  change projection (relationPolynomial "2,1,613,1;0,1,17,1,333,1") = 0
  exact csv_relation_zero _ relation915_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk019
