module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk032
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[32]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 32 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[32]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block2_mem : block2 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 2) (by decide)
private theorem block2_in_rows (r : List Char) (hr : r ∈ block2) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block2, block2_mem, hr⟩
private theorem block3_mem : block3 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 3) (by decide)
private theorem block3_in_rows (r : List Char) (hr : r ∈ block3) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block3, block3_mem, hr⟩
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
private theorem block22_mem : block22 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 22) (by decide)
private theorem block22_in_rows (r : List Char) (hr : r ∈ block22) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block22, block22_mem, hr⟩
private theorem block23_mem : block23 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 23) (by decide)
private theorem block23_in_rows (r : List Char) (hr : r ∈ block23) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block23, block23_mem, hr⟩
private theorem block26_mem : block26 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 26) (by decide)
private theorem block26_in_rows (r : List Char) (hr : r ∈ block26) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block26, block26_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
private theorem block29_mem : block29 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 29) (by decide)
private theorem block29_in_rows (r : List Char) (hr : r ∈ block29) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block29, block29_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation1325_mem : "20,1,502,1;16,1,534,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block0[1]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1325_zero : nativeImage "20,1,502,1;16,1,534,1" = 0 := by
  change projection (relationPolynomial "20,1,502,1;16,1,534,1") = 0
  exact csv_relation_zero _ relation1325_mem
theorem relation1326_mem : "16,1,534,1;9,1,613,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block0[5]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1326_zero : nativeImage "16,1,534,1;9,1,613,1" = 0 := by
  change projection (relationPolynomial "16,1,534,1;9,1,613,1") = 0
  exact csv_relation_zero _ relation1326_mem
theorem relation1327_mem : "9,1,613,1;8,1,17,1,333,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block0[6]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1327_zero : nativeImage "9,1,613,1;8,1,17,1,333,1" = 0 := by
  change projection (relationPolynomial "9,1,613,1;8,1,17,1,333,1") = 0
  exact csv_relation_zero _ relation1327_mem
theorem relation1328_mem : "23,1,473,1;13,1,581,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block2[20]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1328_zero : nativeImage "23,1,473,1;13,1,581,1" = 0 := by
  change projection (relationPolynomial "23,1,473,1;13,1,581,1") = 0
  exact csv_relation_zero _ relation1328_mem
theorem relation1329_mem : "23,1,472,1;13,2,328,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block3[27]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1329_zero : nativeImage "23,1,472,1;13,2,328,1" = 0 := by
  change projection (relationPolynomial "23,1,472,1;13,2,328,1") = 0
  exact csv_relation_zero _ relation1329_mem
theorem relation1330_mem : "17,1,530,1;8,4,201,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block9[9]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1330_zero : nativeImage "17,1,530,1;8,4,201,1" = 0 := by
  change projection (relationPolynomial "17,1,530,1;8,4,201,1") = 0
  exact csv_relation_zero _ relation1330_mem
theorem relation1331_mem : "17,2,255,1;16,1,530,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block10[11]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1331_zero : nativeImage "17,2,255,1;16,1,530,1" = 0 := by
  change projection (relationPolynomial "17,2,255,1;16,1,530,1") = 0
  exact csv_relation_zero _ relation1331_mem
theorem relation1332_mem : "16,1,530,1;13,1,580,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block10[13]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1332_zero : nativeImage "16,1,530,1;13,1,580,1" = 0 := by
  change projection (relationPolynomial "16,1,530,1;13,1,580,1") = 0
  exact csv_relation_zero _ relation1332_mem
theorem relation1333_mem : "13,1,580,1;8,1,9,1,435,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block10[16]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1333_zero : nativeImage "13,1,580,1;8,1,9,1,435,1" = 0 := by
  change projection (relationPolynomial "13,1,580,1;8,1,9,1,435,1") = 0
  exact csv_relation_zero _ relation1333_mem
theorem relation1334_mem : "138,1,147,1;47,1,292,1;31,1,404,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block12[6]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1334_zero : nativeImage "138,1,147,1;47,1,292,1;31,1,404,1" = 0 := by
  change projection (relationPolynomial "138,1,147,1;47,1,292,1;31,1,404,1") = 0
  exact csv_relation_zero _ relation1334_mem
theorem relation1335_mem : "31,1,404,1;16,1,529,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block12[7]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1335_zero : nativeImage "31,1,404,1;16,1,529,1" = 0 := by
  change projection (relationPolynomial "31,1,404,1;16,1,529,1") = 0
  exact csv_relation_zero _ relation1335_mem
theorem relation1336_mem : "16,1,529,1;8,1,637,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block12[8]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1336_zero : nativeImage "16,1,529,1;8,1,637,1" = 0 := by
  change projection (relationPolynomial "16,1,529,1;8,1,637,1") = 0
  exact csv_relation_zero _ relation1336_mem
theorem relation1337_mem : "47,1,292,1;0,1,17,1,516,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block12[9]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1337_zero : nativeImage "47,1,292,1;0,1,17,1,516,1" = 0 := by
  change projection (relationPolynomial "47,1,292,1;0,1,17,1,516,1") = 0
  exact csv_relation_zero _ relation1337_mem
theorem relation1338_mem : "138,1,146,1;137,1,147,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block12[10]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1338_zero : nativeImage "138,1,146,1;137,1,147,1" = 0 := by
  change projection (relationPolynomial "138,1,146,1;137,1,147,1") = 0
  exact csv_relation_zero _ relation1338_mem
theorem relation1339_mem : "137,1,147,1;72,1,225,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block12[16]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1339_zero : nativeImage "137,1,147,1;72,1,225,1" = 0 := by
  change projection (relationPolynomial "137,1,147,1;72,1,225,1") = 0
  exact csv_relation_zero _ relation1339_mem
theorem relation1340_mem : "72,1,225,1;64,1,238,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block12[17]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1340_zero : nativeImage "72,1,225,1;64,1,238,1" = 0 := by
  change projection (relationPolynomial "72,1,225,1;64,1,238,1") = 0
  exact csv_relation_zero _ relation1340_mem
theorem relation1341_mem : "79,1,210,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block13[31]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1341_zero : nativeImage "79,1,210,1" = 0 := by
  change projection (relationPolynomial "79,1,210,1") = 0
  exact csv_relation_zero _ relation1341_mem
theorem relation1342_mem : "16,1,17,2,138,1;8,1,42,1,224,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block14[8]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1342_zero : nativeImage "16,1,17,2,138,1;8,1,42,1,224,1" = 0 := by
  change projection (relationPolynomial "16,1,17,2,138,1;8,1,42,1,224,1") = 0
  exact csv_relation_zero _ relation1342_mem
theorem relation1343_mem : "0,1,8,2,452,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block15[4]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1343_zero : nativeImage "0,1,8,2,452,1" = 0 := by
  change projection (relationPolynomial "0,1,8,2,452,1") = 0
  exact csv_relation_zero _ relation1343_mem
theorem relation1344_mem : "138,1,145,1;71,1,225,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block15[27]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1344_zero : nativeImage "138,1,145,1;71,1,225,1" = 0 := by
  change projection (relationPolynomial "138,1,145,1;71,1,225,1") = 0
  exact csv_relation_zero _ relation1344_mem
theorem relation1345_mem : "71,1,225,1;31,1,403,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block15[28]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1345_zero : nativeImage "71,1,225,1;31,1,403,1" = 0 := by
  change projection (relationPolynomial "71,1,225,1;31,1,403,1") = 0
  exact csv_relation_zero _ relation1345_mem
theorem relation1346_mem : "31,1,403,1;8,1,636,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block15[29]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1346_zero : nativeImage "31,1,403,1;8,1,636,1" = 0 := by
  change projection (relationPolynomial "31,1,403,1;8,1,636,1") = 0
  exact csv_relation_zero _ relation1346_mem
theorem relation1347_mem : "17,1,528,1;8,4,199,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block16[22]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1347_zero : nativeImage "17,1,528,1;8,4,199,1" = 0 := by
  change projection (relationPolynomial "17,1,528,1;8,4,199,1") = 0
  exact csv_relation_zero _ relation1347_mem
theorem relation1348_mem : "17,2,253,1;9,1,607,1;9,1,606,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block17[15]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1348_zero : nativeImage "17,2,253,1;9,1,607,1;9,1,606,1" = 0 := by
  change projection (relationPolynomial "17,2,253,1;9,1,607,1;9,1,606,1") = 0
  exact csv_relation_zero _ relation1348_mem
theorem relation1349_mem : "9,1,607,1;8,1,634,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block17[16]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1349_zero : nativeImage "9,1,607,1;8,1,634,1" = 0 := by
  change projection (relationPolynomial "9,1,607,1;8,1,634,1") = 0
  exact csv_relation_zero _ relation1349_mem
theorem relation1350_mem : "9,1,606,1;0,3,805,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block17[17]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1350_zero : nativeImage "9,1,606,1;0,3,805,1" = 0 := by
  change projection (relationPolynomial "9,1,606,1;0,3,805,1") = 0
  exact csv_relation_zero _ relation1350_mem
theorem relation1351_mem : "38,1,400,1;18,1,525,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block18[4]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1351_zero : nativeImage "38,1,400,1;18,1,525,1" = 0 := by
  change projection (relationPolynomial "38,1,400,1;18,1,525,1") = 0
  exact csv_relation_zero _ relation1351_mem
theorem relation1352_mem : "1,1,3,1,749,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block18[5]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1352_zero : nativeImage "1,1,3,1,749,1" = 0 := by
  change projection (relationPolynomial "1,1,3,1,749,1") = 0
  exact csv_relation_zero _ relation1352_mem
theorem relation1353_mem : "38,1,399,1;37,1,400,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block18[8]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1353_zero : nativeImage "38,1,399,1;37,1,400,1" = 0 := by
  change projection (relationPolynomial "38,1,399,1;37,1,400,1") = 0
  exact csv_relation_zero _ relation1353_mem
theorem relation1354_mem : "38,1,398,1;18,1,524,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block18[9]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1354_zero : nativeImage "38,1,398,1;18,1,524,1" = 0 := by
  change projection (relationPolynomial "38,1,398,1;18,1,524,1") = 0
  exact csv_relation_zero _ relation1354_mem
theorem relation1355_mem : "37,1,400,1;3,1,776,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block18[10]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1355_zero : nativeImage "37,1,400,1;3,1,776,1" = 0 := by
  change projection (relationPolynomial "37,1,400,1;3,1,776,1") = 0
  exact csv_relation_zero _ relation1355_mem
theorem relation1356_mem : "38,1,397,1;37,1,398,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block18[17]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1356_zero : nativeImage "38,1,397,1;37,1,398,1" = 0 := by
  change projection (relationPolynomial "38,1,397,1;37,1,398,1") = 0
  exact csv_relation_zero _ relation1356_mem
theorem relation1357_mem : "38,1,396,1;18,1,523,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block18[18]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1357_zero : nativeImage "38,1,396,1;18,1,523,1" = 0 := by
  change projection (relationPolynomial "38,1,396,1;18,1,523,1") = 0
  exact csv_relation_zero _ relation1357_mem
theorem relation1358_mem : "37,1,398,1;3,1,774,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block18[22]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1358_zero : nativeImage "37,1,398,1;3,1,774,1" = 0 := by
  change projection (relationPolynomial "37,1,398,1;3,1,774,1") = 0
  exact csv_relation_zero _ relation1358_mem
theorem relation1359_mem : "38,1,392,1;37,1,396,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block19[2]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1359_zero : nativeImage "38,1,392,1;37,1,396,1" = 0 := by
  change projection (relationPolynomial "38,1,392,1;37,1,396,1") = 0
  exact csv_relation_zero _ relation1359_mem
theorem relation1360_mem : "37,1,396,1;3,1,771,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block19[12]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1360_zero : nativeImage "37,1,396,1;3,1,771,1" = 0 := by
  change projection (relationPolynomial "37,1,396,1;3,1,771,1") = 0
  exact csv_relation_zero _ relation1360_mem
theorem relation1361_mem : "107,1,191,1;43,1,336,1;37,1,386,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block22[20]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1361_zero : nativeImage "107,1,191,1;43,1,336,1;37,1,386,1" = 0 := by
  change projection (relationPolynomial "107,1,191,1;43,1,336,1;37,1,386,1") = 0
  exact csv_relation_zero _ relation1361_mem
theorem relation1362_mem : "37,1,386,1;36,1,390,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block22[21]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1362_zero : nativeImage "37,1,386,1;36,1,390,1" = 0 := by
  change projection (relationPolynomial "37,1,386,1;36,1,390,1") = 0
  exact csv_relation_zero _ relation1362_mem
theorem relation1363_mem : "36,1,390,1;3,1,67,1,203,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block23[6]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1363_zero : nativeImage "36,1,390,1;3,1,67,1,203,1" = 0 := by
  change projection (relationPolynomial "36,1,390,1;3,1,67,1,203,1") = 0
  exact csv_relation_zero _ relation1363_mem
theorem relation1364_mem : "3,1,67,1,203,1;2,1,814,1;0,2,845,1;0,2,8,1,16,1,324,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block23[10]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1364_zero : nativeImage "3,1,67,1,203,1;2,1,814,1;0,2,845,1;0,2,8,1,16,1,324,1" = 0 := by
  change projection (relationPolynomial "3,1,67,1,203,1;2,1,814,1;0,2,845,1;0,2,8,1,16,1,324,1") = 0
  exact csv_relation_zero _ relation1364_mem
theorem relation1365_mem : "23,1,485,1;9,1,13,1,373,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block26[2]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1365_zero : nativeImage "23,1,485,1;9,1,13,1,373,1" = 0 := by
  change projection (relationPolynomial "23,1,485,1;9,1,13,1,373,1") = 0
  exact csv_relation_zero _ relation1365_mem
theorem relation1366_mem : "107,1,188,1;9,1,619,1;0,2,838,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block28[20]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1366_zero : nativeImage "107,1,188,1;9,1,619,1;0,2,838,1" = 0 := by
  change projection (relationPolynomial "107,1,188,1;9,1,619,1;0,2,838,1") = 0
  exact csv_relation_zero _ relation1366_mem
theorem relation1367_mem : "32,1,417,1;13,2,335,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block29[28]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1367_zero : nativeImage "32,1,417,1;13,2,335,1" = 0 := by
  change projection (relationPolynomial "32,1,417,1;13,2,335,1") = 0
  exact csv_relation_zero _ relation1367_mem
theorem relation1368_mem : "8,2,483,1;1,1,79,1,209,1;0,1,8,1,17,1,333,1" ∈ LinE2.RawData.relations := by
  exact relation_member 32 chunkBound rows transcription
    (block31[19]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1368_zero : nativeImage "8,2,483,1;1,1,79,1,209,1;0,1,8,1,17,1,333,1" = 0 := by
  change projection (relationPolynomial "8,2,483,1;1,1,79,1,209,1;0,1,8,1,17,1,333,1") = 0
  exact csv_relation_zero _ relation1368_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk032
