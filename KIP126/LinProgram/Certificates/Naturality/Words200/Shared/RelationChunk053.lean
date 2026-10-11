module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk053
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[53]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 53 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[53]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block7_mem : block7 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 7) (by decide)
private theorem block7_in_rows (r : List Char) (hr : r ∈ block7) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block7, block7_mem, hr⟩
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
private theorem block27_mem : block27 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 27) (by decide)
private theorem block27_in_rows (r : List Char) (hr : r ∈ block27) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block27, block27_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
private theorem block29_mem : block29 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 29) (by decide)
private theorem block29_in_rows (r : List Char) (hr : r ∈ block29) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block29, block29_mem, hr⟩
theorem relation1830_mem : "69,1,370,1;67,1,375,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block0[2]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1830_zero : nativeImage "69,1,370,1;67,1,375,1" = 0 := by
  change projection (relationPolynomial "69,1,370,1;67,1,375,1") = 0
  exact csv_relation_zero _ relation1830_mem
theorem relation1831_mem : "67,1,375,1;12,1,819,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block0[17]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1831_zero : nativeImage "67,1,375,1;12,1,819,1" = 0 := by
  change projection (relationPolynomial "67,1,375,1;12,1,819,1") = 0
  exact csv_relation_zero _ relation1831_mem
theorem relation1832_mem : "68,1,373,1;67,1,376,1;2,1,1073,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block0[24]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1832_zero : nativeImage "68,1,373,1;67,1,376,1;2,1,1073,1" = 0 := by
  change projection (relationPolynomial "68,1,373,1;67,1,376,1;2,1,1073,1") = 0
  exact csv_relation_zero _ relation1832_mem
theorem relation1833_mem : "2,1,1073,1;2,2,1008,1;1,1,1098,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block0[26]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1833_zero : nativeImage "2,1,1073,1;2,2,1008,1;1,1,1098,1" = 0 := by
  change projection (relationPolynomial "2,1,1073,1;2,2,1008,1;1,1,1098,1") = 0
  exact csv_relation_zero _ relation1833_mem
theorem relation1834_mem : "2,2,1008,1;1,1,18,1,683,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block0[27]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1834_zero : nativeImage "2,2,1008,1;1,1,18,1,683,1" = 0 := by
  change projection (relationPolynomial "2,2,1008,1;1,1,18,1,683,1") = 0
  exact csv_relation_zero _ relation1834_mem
theorem relation1835_mem : "1,1,1098,1;1,1,18,1,683,1;0,1,1115,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block0[28]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1835_zero : nativeImage "1,1,1098,1;1,1,18,1,683,1;0,1,1115,1" = 0 := by
  change projection (relationPolynomial "1,1,1098,1;1,1,18,1,683,1;0,1,1115,1") = 0
  exact csv_relation_zero _ relation1835_mem
theorem relation1836_mem : "0,1,1115,1;0,2,1099,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block0[31]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1836_zero : nativeImage "0,1,1115,1;0,2,1099,1" = 0 := by
  change projection (relationPolynomial "0,1,1115,1;0,2,1099,1") = 0
  exact csv_relation_zero _ relation1836_mem
theorem relation1837_mem : "2,2,1002,1;1,1,1096,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block7[13]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1837_zero : nativeImage "2,2,1002,1;1,1,1096,1" = 0 := by
  change projection (relationPolynomial "2,2,1002,1;1,1,1096,1") = 0
  exact csv_relation_zero _ relation1837_mem
theorem relation1838_mem : "20,1,692,1;8,1,89,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block15[6]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1838_zero : nativeImage "20,1,692,1;8,1,89,1,209,1" = 0 := by
  change projection (relationPolynomial "20,1,692,1;8,1,89,1,209,1") = 0
  exact csv_relation_zero _ relation1838_mem
theorem relation1839_mem : "17,1,729,1;9,1,834,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block16[26]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1839_zero : nativeImage "17,1,729,1;9,1,834,1" = 0 := by
  change projection (relationPolynomial "17,1,729,1;9,1,834,1") = 0
  exact csv_relation_zero _ relation1839_mem
theorem relation1840_mem : "9,1,834,1;8,1,878,1;1,2,1062,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block17[0]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1840_zero : nativeImage "9,1,834,1;8,1,878,1;1,2,1062,1" = 0 := by
  change projection (relationPolynomial "9,1,834,1;8,1,878,1;1,2,1062,1") = 0
  exact csv_relation_zero _ relation1840_mem
theorem relation1841_mem : "1,2,1062,1;0,1,1104,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block17[1]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1841_zero : nativeImage "1,2,1062,1;0,1,1104,1" = 0 := by
  change projection (relationPolynomial "1,2,1062,1;0,1,1104,1") = 0
  exact csv_relation_zero _ relation1841_mem
theorem relation1842_mem : "160,1,188,1;147,1,209,1;138,1,221,1;107,1,274,1;90,1,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block18[8]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1842_zero : nativeImage "160,1,188,1;147,1,209,1;138,1,221,1;107,1,274,1;90,1,292,1" = 0 := by
  change projection (relationPolynomial "160,1,188,1;147,1,209,1;138,1,221,1;107,1,274,1;90,1,292,1") = 0
  exact csv_relation_zero _ relation1842_mem
theorem relation1843_mem : "138,1,221,1;107,1,274,1;90,1,292,1;89,1,292,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block18[9]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1843_zero : nativeImage "138,1,221,1;107,1,274,1;90,1,292,1;89,1,292,1" = 0 := by
  change projection (relationPolynomial "138,1,221,1;107,1,274,1;90,1,292,1;89,1,292,1") = 0
  exact csv_relation_zero _ relation1843_mem
theorem relation1844_mem : "89,1,292,1;80,1,316,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block18[11]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1844_zero : nativeImage "89,1,292,1;80,1,316,1" = 0 := by
  change projection (relationPolynomial "89,1,292,1;80,1,316,1") = 0
  exact csv_relation_zero _ relation1844_mem
theorem relation1845_mem : "147,1,209,1;90,1,292,1;80,1,317,1;64,1,383,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block18[15]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1845_zero : nativeImage "147,1,209,1;90,1,292,1;80,1,317,1;64,1,383,1" = 0 := by
  change projection (relationPolynomial "147,1,209,1;90,1,292,1;80,1,317,1;64,1,383,1") = 0
  exact csv_relation_zero _ relation1845_mem
theorem relation1846_mem : "29,1,627,1;22,1,655,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block18[31]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1846_zero : nativeImage "29,1,627,1;22,1,655,1" = 0 := by
  change projection (relationPolynomial "29,1,627,1;22,1,655,1") = 0
  exact csv_relation_zero _ relation1846_mem
theorem relation1847_mem : "22,1,655,1;20,1,690,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block19[0]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1847_zero : nativeImage "22,1,655,1;20,1,690,1" = 0 := by
  change projection (relationPolynomial "22,1,655,1;20,1,690,1") = 0
  exact csv_relation_zero _ relation1847_mem
theorem relation1848_mem : "90,1,292,1;80,1,316,1;20,1,690,1;9,1,832,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block19[2]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1848_zero : nativeImage "90,1,292,1;80,1,316,1;20,1,690,1;9,1,832,1" = 0 := by
  change projection (relationPolynomial "90,1,292,1;80,1,316,1;20,1,690,1;9,1,832,1") = 0
  exact csv_relation_zero _ relation1848_mem
theorem relation1849_mem : "80,1,316,1;9,1,832,1;8,1,875,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block19[3]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1849_zero : nativeImage "80,1,316,1;9,1,832,1;8,1,875,1" = 0 := by
  change projection (relationPolynomial "80,1,316,1;9,1,832,1;8,1,875,1") = 0
  exact csv_relation_zero _ relation1849_mem
theorem relation1850_mem : "20,1,690,1;8,1,874,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block19[4]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1850_zero : nativeImage "20,1,690,1;8,1,874,1" = 0 := by
  change projection (relationPolynomial "20,1,690,1;8,1,874,1") = 0
  exact csv_relation_zero _ relation1850_mem
theorem relation1851_mem : "9,1,832,1;8,1,875,1;8,1,874,1;8,2,13,1,423,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block19[5]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1851_zero : nativeImage "9,1,832,1;8,1,875,1;8,1,874,1;8,2,13,1,423,1" = 0 := by
  change projection (relationPolynomial "9,1,832,1;8,1,875,1;8,1,874,1;8,2,13,1,423,1") = 0
  exact csv_relation_zero _ relation1851_mem
theorem relation1852_mem : "8,1,875,1;8,2,13,1,423,1;0,3,1081,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block19[6]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1852_zero : nativeImage "8,1,875,1;8,2,13,1,423,1;0,3,1081,1" = 0 := by
  change projection (relationPolynomial "8,1,875,1;8,2,13,1,423,1;0,3,1081,1") = 0
  exact csv_relation_zero _ relation1852_mem
theorem relation1853_mem : "80,1,317,1;8,1,874,1;8,2,13,1,423,1;0,3,1081,1;0,4,1063,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block19[7]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1853_zero : nativeImage "80,1,317,1;8,1,874,1;8,2,13,1,423,1;0,3,1081,1;0,4,1063,1" = 0 := by
  change projection (relationPolynomial "80,1,317,1;8,1,874,1;8,2,13,1,423,1;0,3,1081,1;0,4,1063,1") = 0
  exact csv_relation_zero _ relation1853_mem
theorem relation1854_mem : "146,1,209,1;72,1,347,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block19[21]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1854_zero : nativeImage "146,1,209,1;72,1,347,1" = 0 := by
  change projection (relationPolynomial "146,1,209,1;72,1,347,1") = 0
  exact csv_relation_zero _ relation1854_mem
theorem relation1855_mem : "72,1,347,1;64,1,382,1;34,1,602,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block20[9]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1855_zero : nativeImage "72,1,347,1;64,1,382,1;34,1,602,1" = 0 := by
  change projection (relationPolynomial "72,1,347,1;64,1,382,1;34,1,602,1") = 0
  exact csv_relation_zero _ relation1855_mem
theorem relation1856_mem : "34,1,600,1;0,3,1079,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block20[23]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1856_zero : nativeImage "34,1,600,1;0,3,1079,1" = 0 := by
  change projection (relationPolynomial "34,1,600,1;0,3,1079,1") = 0
  exact csv_relation_zero _ relation1856_mem
theorem relation1857_mem : "46,1,516,1;31,1,602,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block27[11]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1857_zero : nativeImage "46,1,516,1;31,1,602,1" = 0 := by
  change projection (relationPolynomial "46,1,516,1;31,1,602,1") = 0
  exact csv_relation_zero _ relation1857_mem
theorem relation1858_mem : "17,1,726,1;13,1,796,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block27[18]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1858_zero : nativeImage "17,1,726,1;13,1,796,1" = 0 := by
  change projection (relationPolynomial "17,1,726,1;13,1,796,1") = 0
  exact csv_relation_zero _ relation1858_mem
theorem relation1859_mem : "13,1,796,1;9,1,831,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block27[20]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1859_zero : nativeImage "13,1,796,1;9,1,831,1" = 0 := by
  change projection (relationPolynomial "13,1,796,1;9,1,831,1") = 0
  exact csv_relation_zero _ relation1859_mem
theorem relation1860_mem : "31,1,602,1;8,1,60,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block27[21]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1860_zero : nativeImage "31,1,602,1;8,1,60,1,260,1" = 0 := by
  change projection (relationPolynomial "31,1,602,1;8,1,60,1,260,1") = 0
  exact csv_relation_zero _ relation1860_mem
theorem relation1861_mem : "9,1,831,1;8,2,653,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block27[22]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1861_zero : nativeImage "9,1,831,1;8,2,653,1" = 0 := by
  change projection (relationPolynomial "9,1,831,1;8,2,653,1") = 0
  exact csv_relation_zero _ relation1861_mem
theorem relation1862_mem : "137,1,218,1;112,1,258,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block27[29]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1862_zero : nativeImage "137,1,218,1;112,1,258,1" = 0 := by
  change projection (relationPolynomial "137,1,218,1;112,1,258,1") = 0
  exact csv_relation_zero _ relation1862_mem
theorem relation1863_mem : "112,1,258,1;72,1,344,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block28[2]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1863_zero : nativeImage "112,1,258,1;72,1,344,1" = 0 := by
  change projection (relationPolynomial "112,1,258,1;72,1,344,1") = 0
  exact csv_relation_zero _ relation1863_mem
theorem relation1864_mem : "72,1,344,1;71,1,348,1;56,1,454,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block28[5]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1864_zero : nativeImage "72,1,344,1;71,1,348,1;56,1,454,1" = 0 := by
  change projection (relationPolynomial "72,1,344,1;71,1,348,1;56,1,454,1") = 0
  exact csv_relation_zero _ relation1864_mem
theorem relation1865_mem : "71,1,348,1;55,1,455,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block28[6]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1865_zero : nativeImage "71,1,348,1;55,1,455,1" = 0 := by
  change projection (relationPolynomial "71,1,348,1;55,1,455,1") = 0
  exact csv_relation_zero _ relation1865_mem
theorem relation1866_mem : "55,1,455,1;49,1,492,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block28[7]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1866_zero : nativeImage "55,1,455,1;49,1,492,1" = 0 := by
  change projection (relationPolynomial "55,1,455,1;49,1,492,1") = 0
  exact csv_relation_zero _ relation1866_mem
theorem relation1867_mem : "56,1,454,1;45,1,516,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block28[8]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1867_zero : nativeImage "56,1,454,1;45,1,516,1" = 0 := by
  change projection (relationPolynomial "56,1,454,1;45,1,516,1") = 0
  exact csv_relation_zero _ relation1867_mem
theorem relation1868_mem : "49,1,492,1;39,1,573,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block28[9]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1868_zero : nativeImage "49,1,492,1;39,1,573,1" = 0 := by
  change projection (relationPolynomial "49,1,492,1;39,1,573,1") = 0
  exact csv_relation_zero _ relation1868_mem
theorem relation1869_mem : "39,1,573,1;31,1,599,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block28[10]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1869_zero : nativeImage "39,1,573,1;31,1,599,1" = 0 := by
  change projection (relationPolynomial "39,1,573,1;31,1,599,1") = 0
  exact csv_relation_zero _ relation1869_mem
theorem relation1870_mem : "31,1,599,1;19,1,688,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block28[12]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1870_zero : nativeImage "31,1,599,1;19,1,688,1" = 0 := by
  change projection (relationPolynomial "31,1,599,1;19,1,688,1") = 0
  exact csv_relation_zero _ relation1870_mem
theorem relation1871_mem : "19,1,688,1;16,1,726,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block28[13]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1871_zero : nativeImage "19,1,688,1;16,1,726,1" = 0 := by
  change projection (relationPolynomial "19,1,688,1;16,1,726,1") = 0
  exact csv_relation_zero _ relation1871_mem
theorem relation1872_mem : "16,1,726,1;9,1,830,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block28[14]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1872_zero : nativeImage "16,1,726,1;9,1,830,1" = 0 := by
  change projection (relationPolynomial "16,1,726,1;9,1,830,1") = 0
  exact csv_relation_zero _ relation1872_mem
theorem relation1873_mem : "45,1,516,1;9,1,830,1;8,1,64,1,245,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block28[15]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1873_zero : nativeImage "45,1,516,1;9,1,830,1;8,1,64,1,245,1" = 0 := by
  change projection (relationPolynomial "45,1,516,1;9,1,830,1;8,1,64,1,245,1") = 0
  exact csv_relation_zero _ relation1873_mem
theorem relation1874_mem : "113,1,257,1;55,1,454,1;31,1,598,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block29[4]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1874_zero : nativeImage "113,1,257,1;55,1,454,1;31,1,598,1" = 0 := by
  change projection (relationPolynomial "113,1,257,1;55,1,454,1;31,1,598,1") = 0
  exact csv_relation_zero _ relation1874_mem
theorem relation1875_mem : "55,1,454,1;29,1,623,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block29[5]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1875_zero : nativeImage "55,1,454,1;29,1,623,1" = 0 := by
  change projection (relationPolynomial "55,1,454,1;29,1,623,1") = 0
  exact csv_relation_zero _ relation1875_mem
theorem relation1876_mem : "31,1,598,1;29,1,623,1;8,1,138,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block29[6]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1876_zero : nativeImage "31,1,598,1;29,1,623,1;8,1,138,1,149,1" = 0 := by
  change projection (relationPolynomial "31,1,598,1;29,1,623,1;8,1,138,1,149,1") = 0
  exact csv_relation_zero _ relation1876_mem
theorem relation1877_mem : "29,1,623,1;8,1,16,1,17,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 53 chunkBound rows transcription
    (block29[7]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1877_zero : nativeImage "29,1,623,1;8,1,16,1,17,1,260,1" = 0 := by
  change projection (relationPolynomial "29,1,623,1;8,1,16,1,17,1,260,1") = 0
  exact csv_relation_zero _ relation1877_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk053
