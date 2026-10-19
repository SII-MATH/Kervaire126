module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk034
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[34]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 34 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[34]'(chunkBound) =
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
private theorem block6_mem : block6 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 6) (by decide)
private theorem block6_in_rows (r : List Char) (hr : r ∈ block6) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block6, block6_mem, hr⟩
private theorem block10_mem : block10 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 10) (by decide)
private theorem block10_in_rows (r : List Char) (hr : r ∈ block10) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block10, block10_mem, hr⟩
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
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
theorem relation1382_mem : "42,1,346,1;13,1,602,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block0[3]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1382_zero : nativeImage "42,1,346,1;13,1,602,1" = 0 := by
  change projection (relationPolynomial "42,1,346,1;13,1,602,1") = 0
  exact csv_relation_zero _ relation1382_mem
theorem relation1383_mem : "13,1,602,1;9,1,625,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block0[7]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1383_zero : nativeImage "13,1,602,1;9,1,625,1" = 0 := by
  change projection (relationPolynomial "13,1,602,1;9,1,625,1") = 0
  exact csv_relation_zero _ relation1383_mem
theorem relation1384_mem : "9,1,625,1;8,1,23,1,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block0[8]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1384_zero : nativeImage "9,1,625,1;8,1,23,1,292,1" = 0 := by
  change projection (relationPolynomial "9,1,625,1;8,1,23,1,292,1") = 0
  exact csv_relation_zero _ relation1384_mem
theorem relation1385_mem : "17,1,550,1;13,1,599,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block1[3]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1385_zero : nativeImage "17,1,550,1;13,1,599,1" = 0 := by
  change projection (relationPolynomial "17,1,550,1;13,1,599,1") = 0
  exact csv_relation_zero _ relation1385_mem
theorem relation1386_mem : "8,1,654,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block1[4]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1386_zero : nativeImage "8,1,654,1" = 0 := by
  change projection (relationPolynomial "8,1,654,1") = 0
  exact csv_relation_zero _ relation1386_mem
theorem relation1387_mem : "13,1,599,1;8,2,492,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block1[6]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1387_zero : nativeImage "13,1,599,1;8,2,492,1" = 0 := by
  change projection (relationPolynomial "13,1,599,1;8,2,492,1") = 0
  exact csv_relation_zero _ relation1387_mem
theorem relation1388_mem : "17,1,549,1;8,1,16,1,347,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block2[30]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1388_zero : nativeImage "17,1,549,1;8,1,16,1,347,1" = 0 := by
  change projection (relationPolynomial "17,1,549,1;8,1,16,1,347,1") = 0
  exact csv_relation_zero _ relation1388_mem
theorem relation1389_mem : "64,1,247,1;64,1,246,1;60,1,260,1;59,1,260,1;49,1,293,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block3[4]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1389_zero : nativeImage "64,1,247,1;64,1,246,1;60,1,260,1;59,1,260,1;49,1,293,1" = 0 := by
  change projection (relationPolynomial "64,1,247,1;64,1,246,1;60,1,260,1;59,1,260,1;49,1,293,1") = 0
  exact csv_relation_zero _ relation1389_mem
theorem relation1390_mem : "49,1,293,1;31,1,420,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block3[7]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1390_zero : nativeImage "49,1,293,1;31,1,420,1" = 0 := by
  change projection (relationPolynomial "49,1,293,1;31,1,420,1") = 0
  exact csv_relation_zero _ relation1390_mem
theorem relation1391_mem : "31,1,420,1;16,1,549,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block3[9]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1391_zero : nativeImage "31,1,420,1;16,1,549,1" = 0 := by
  change projection (relationPolynomial "31,1,420,1;16,1,549,1") = 0
  exact csv_relation_zero _ relation1391_mem
theorem relation1392_mem : "16,1,549,1;8,1,653,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block3[10]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1392_zero : nativeImage "16,1,549,1;8,1,653,1" = 0 := by
  change projection (relationPolynomial "16,1,549,1;8,1,653,1") = 0
  exact csv_relation_zero _ relation1392_mem
theorem relation1393_mem : "17,2,257,1;13,1,596,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block6[25]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1393_zero : nativeImage "17,2,257,1;13,1,596,1" = 0 := by
  change projection (relationPolynomial "17,2,257,1;13,1,596,1") = 0
  exact csv_relation_zero _ relation1393_mem
theorem relation1394_mem : "13,1,596,1;8,2,489,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block6[26]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1394_zero : nativeImage "13,1,596,1;8,2,489,1" = 0 := by
  change projection (relationPolynomial "13,1,596,1;8,2,489,1") = 0
  exact csv_relation_zero _ relation1394_mem
theorem relation1395_mem : "132,1,163,1;25,1,508,1;7,1,698,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block10[1]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1395_zero : nativeImage "132,1,163,1;25,1,508,1;7,1,698,1" = 0 := by
  change projection (relationPolynomial "132,1,163,1;25,1,508,1;7,1,698,1") = 0
  exact csv_relation_zero _ relation1395_mem
theorem relation1396_mem : "25,1,508,1;3,2,699,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block10[2]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1396_zero : nativeImage "25,1,508,1;3,2,699,1" = 0 := by
  change projection (relationPolynomial "25,1,508,1;3,2,699,1") = 0
  exact csv_relation_zero _ relation1396_mem
theorem relation1397_mem : "3,2,699,1;1,2,18,1,506,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block10[3]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1397_zero : nativeImage "3,2,699,1;1,2,18,1,506,1" = 0 := by
  change projection (relationPolynomial "3,2,699,1;1,2,18,1,506,1") = 0
  exact csv_relation_zero _ relation1397_mem
theorem relation1398_mem : "2,1,847,1;1,1,7,1,676,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block10[24]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1398_zero : nativeImage "2,1,847,1;1,1,7,1,676,1" = 0 := by
  change projection (relationPolynomial "2,1,847,1;1,1,7,1,676,1") = 0
  exact csv_relation_zero _ relation1398_mem
theorem relation1399_mem : "18,1,544,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block11[3]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1399_zero : nativeImage "18,1,544,1" = 0 := by
  change projection (relationPolynomial "18,1,544,1") = 0
  exact csv_relation_zero _ relation1399_mem
theorem relation1400_mem : "43,1,367,1;3,1,789,1;0,1,884,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block11[24]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1400_zero : nativeImage "43,1,367,1;3,1,789,1;0,1,884,1" = 0 := by
  change projection (relationPolynomial "43,1,367,1;3,1,789,1;0,1,884,1") = 0
  exact csv_relation_zero _ relation1400_mem
theorem relation1401_mem : "24,1,504,1;13,2,368,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block12[31]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1401_zero : nativeImage "24,1,504,1;13,2,368,1" = 0 := by
  change projection (relationPolynomial "24,1,504,1;13,2,368,1") = 0
  exact csv_relation_zero _ relation1401_mem
theorem relation1402_mem : "13,2,368,1;3,1,787,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block13[3]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1402_zero : nativeImage "13,2,368,1;3,1,787,1" = 0 := by
  change projection (relationPolynomial "13,2,368,1;3,1,787,1") = 0
  exact csv_relation_zero _ relation1402_mem
theorem relation1403_mem : "2,1,844,1;1,1,868,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block14[5]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1403_zero : nativeImage "2,1,844,1;1,1,868,1" = 0 := by
  change projection (relationPolynomial "2,1,844,1;1,1,868,1") = 0
  exact csv_relation_zero _ relation1403_mem
theorem relation1404_mem : "2,1,840,1;1,1,3,1,764,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block16[24]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1404_zero : nativeImage "2,1,840,1;1,1,3,1,764,1" = 0 := by
  change projection (relationPolynomial "2,1,840,1;1,1,3,1,764,1") = 0
  exact csv_relation_zero _ relation1404_mem
theorem relation1405_mem : "17,1,562,1;16,1,564,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block17[19]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1405_zero : nativeImage "17,1,562,1;16,1,564,1" = 0 := by
  change projection (relationPolynomial "17,1,562,1;16,1,564,1") = 0
  exact csv_relation_zero _ relation1405_mem
theorem relation1406_mem : "16,1,564,1;16,1,563,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block17[20]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1406_zero : nativeImage "16,1,564,1;16,1,563,1" = 0 := by
  change projection (relationPolynomial "16,1,564,1;16,1,563,1") = 0
  exact csv_relation_zero _ relation1406_mem
theorem relation1407_mem : "16,1,563,1;8,1,672,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block17[23]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1407_zero : nativeImage "16,1,563,1;8,1,672,1" = 0 := by
  change projection (relationPolynomial "16,1,563,1;8,1,672,1") = 0
  exact csv_relation_zero _ relation1407_mem
theorem relation1408_mem : "2,1,838,1;1,1,866,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block17[30]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1408_zero : nativeImage "2,1,838,1;1,1,866,1" = 0 := by
  change projection (relationPolynomial "2,1,838,1;1,1,866,1") = 0
  exact csv_relation_zero _ relation1408_mem
theorem relation1409_mem : "8,1,672,1;7,1,692,1;0,2,3,1,764,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block18[0]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1409_zero : nativeImage "8,1,672,1;7,1,692,1;0,2,3,1,764,1" = 0 := by
  change projection (relationPolynomial "8,1,672,1;7,1,692,1;0,2,3,1,764,1") = 0
  exact csv_relation_zero _ relation1409_mem
theorem relation1410_mem : "2,1,835,1;1,1,865,1;1,1,44,1,324,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block19[15]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1410_zero : nativeImage "2,1,835,1;1,1,865,1;1,1,44,1,324,1" = 0 := by
  change projection (relationPolynomial "2,1,835,1;1,1,865,1;1,1,44,1,324,1") = 0
  exact csv_relation_zero _ relation1410_mem
theorem relation1411_mem : "3,2,691,1;1,2,838,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block19[16]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1411_zero : nativeImage "3,2,691,1;1,2,838,1" = 0 := by
  change projection (relationPolynomial "3,2,691,1;1,2,838,1") = 0
  exact csv_relation_zero _ relation1411_mem
theorem relation1412_mem : "39,1,415,1;31,1,445,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block20[11]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1412_zero : nativeImage "39,1,415,1;31,1,445,1" = 0 := by
  change projection (relationPolynomial "39,1,415,1;31,1,445,1") = 0
  exact csv_relation_zero _ relation1412_mem
theorem relation1413_mem : "31,1,445,1;29,1,475,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block20[13]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1413_zero : nativeImage "31,1,445,1;29,1,475,1" = 0 := by
  change projection (relationPolynomial "31,1,445,1;29,1,475,1") = 0
  exact csv_relation_zero _ relation1413_mem
theorem relation1414_mem : "29,1,475,1;22,1,502,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block20[17]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1414_zero : nativeImage "29,1,475,1;22,1,502,1" = 0 := by
  change projection (relationPolynomial "29,1,475,1;22,1,502,1") = 0
  exact csv_relation_zero _ relation1414_mem
theorem relation1415_mem : "22,1,502,1;19,1,534,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block20[22]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1415_zero : nativeImage "22,1,502,1;19,1,534,1" = 0 := by
  change projection (relationPolynomial "22,1,502,1;19,1,534,1") = 0
  exact csv_relation_zero _ relation1415_mem
theorem relation1416_mem : "19,1,534,1;13,1,613,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block20[24]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1416_zero : nativeImage "19,1,534,1;13,1,613,1" = 0 := by
  change projection (relationPolynomial "19,1,534,1;13,1,613,1") = 0
  exact csv_relation_zero _ relation1416_mem
theorem relation1417_mem : "13,1,613,1;8,1,16,1,367,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block20[28]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1417_zero : nativeImage "13,1,613,1;8,1,16,1,367,1" = 0 := by
  change projection (relationPolynomial "13,1,613,1;8,1,16,1,367,1") = 0
  exact csv_relation_zero _ relation1417_mem
theorem relation1418_mem : "8,1,16,1,367,1;2,1,80,1,209,1;0,1,879,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block21[0]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1418_zero : nativeImage "8,1,16,1,367,1;2,1,80,1,209,1;0,1,879,1" = 0 := by
  change projection (relationPolynomial "8,1,16,1,367,1;2,1,80,1,209,1;0,1,879,1") = 0
  exact csv_relation_zero _ relation1418_mem
theorem relation1419_mem : "13,2,359,1;9,1,23,1,286,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block27[4]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1419_zero : nativeImage "13,2,359,1;9,1,23,1,286,1" = 0 := by
  change projection (relationPolynomial "13,2,359,1;9,1,23,1,286,1") = 0
  exact csv_relation_zero _ relation1419_mem
theorem relation1420_mem : "113,1,188,1;10,1,627,1;8,1,667,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block27[5]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1420_zero : nativeImage "113,1,188,1;10,1,627,1;8,1,667,1" = 0 := by
  change projection (relationPolynomial "113,1,188,1;10,1,627,1;8,1,667,1") = 0
  exact csv_relation_zero _ relation1420_mem
theorem relation1421_mem : "10,1,627,1;2,1,832,1;0,1,875,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block27[8]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1421_zero : nativeImage "10,1,627,1;2,1,832,1;0,1,875,1" = 0 := by
  change projection (relationPolynomial "10,1,627,1;2,1,832,1;0,1,875,1") = 0
  exact csv_relation_zero _ relation1421_mem
theorem relation1422_mem : "2,1,832,1;0,1,875,1;0,1,874,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block27[9]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1422_zero : nativeImage "2,1,832,1;0,1,875,1;0,1,874,1" = 0 := by
  change projection (relationPolynomial "2,1,832,1;0,1,875,1;0,1,874,1") = 0
  exact csv_relation_zero _ relation1422_mem
theorem relation1423_mem : "113,1,187,1;112,1,188,1;79,1,226,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block27[22]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1423_zero : nativeImage "113,1,187,1;112,1,188,1;79,1,226,1" = 0 := by
  change projection (relationPolynomial "113,1,187,1;112,1,188,1;79,1,226,1") = 0
  exact csv_relation_zero _ relation1423_mem
theorem relation1424_mem : "112,1,188,1;64,1,255,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block27[29]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1424_zero : nativeImage "112,1,188,1;64,1,255,1" = 0 := by
  change projection (relationPolynomial "112,1,188,1;64,1,255,1") = 0
  exact csv_relation_zero _ relation1424_mem
theorem relation1425_mem : "79,1,226,1;53,1,291,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block28[0]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1425_zero : nativeImage "79,1,226,1;53,1,291,1" = 0 := by
  change projection (relationPolynomial "79,1,226,1;53,1,291,1") = 0
  exact csv_relation_zero _ relation1425_mem
theorem relation1426_mem : "53,1,291,1;16,1,561,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block28[17]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1426_zero : nativeImage "53,1,291,1;16,1,561,1" = 0 := by
  change projection (relationPolynomial "53,1,291,1;16,1,561,1") = 0
  exact csv_relation_zero _ relation1426_mem
theorem relation1427_mem : "16,1,561,1;8,1,666,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block28[20]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1427_zero : nativeImage "16,1,561,1;8,1,666,1" = 0 := by
  change projection (relationPolynomial "16,1,561,1;8,1,666,1") = 0
  exact csv_relation_zero _ relation1427_mem
theorem relation1428_mem : "8,1,666,1;6,1,690,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block28[21]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1428_zero : nativeImage "8,1,666,1;6,1,690,1" = 0 := by
  change projection (relationPolynomial "8,1,666,1;6,1,690,1") = 0
  exact csv_relation_zero _ relation1428_mem
theorem relation1429_mem : "6,1,690,1;0,1,8,1,655,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block28[23]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1429_zero : nativeImage "6,1,690,1;0,1,8,1,655,1" = 0 := by
  change projection (relationPolynomial "6,1,690,1;0,1,8,1,655,1") = 0
  exact csv_relation_zero _ relation1429_mem
theorem relation1430_mem : "17,2,267,1;8,4,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 34 chunkBound rows transcription
    (block31[22]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1430_zero : nativeImage "17,2,267,1;8,4,212,1" = 0 := by
  change projection (relationPolynomial "17,2,267,1;8,4,212,1") = 0
  exact csv_relation_zero _ relation1430_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk034
