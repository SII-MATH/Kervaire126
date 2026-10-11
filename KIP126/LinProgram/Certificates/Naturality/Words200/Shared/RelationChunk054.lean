module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk054
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[54]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 54 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[54]'(chunkBound) =
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
private theorem block9_mem : block9 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 9) (by decide)
private theorem block9_in_rows (r : List Char) (hr : r ∈ block9) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block9, block9_mem, hr⟩
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
private theorem block20_mem : block20 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 20) (by decide)
private theorem block20_in_rows (r : List Char) (hr : r ∈ block20) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block20, block20_mem, hr⟩
private theorem block21_mem : block21 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 21) (by decide)
private theorem block21_in_rows (r : List Char) (hr : r ∈ block21) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block21, block21_mem, hr⟩
theorem relation1878_mem : "17,1,724,1;8,3,488,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block0[22]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1878_zero : nativeImage "17,1,724,1;8,3,488,1" = 0 := by
  change projection (relationPolynomial "17,1,724,1;8,3,488,1") = 0
  exact csv_relation_zero _ relation1878_mem
theorem relation1879_mem : "17,1,723,1;9,1,829,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block1[12]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1879_zero : nativeImage "17,1,723,1;9,1,829,1" = 0 := by
  change projection (relationPolynomial "17,1,723,1;9,1,829,1") = 0
  exact csv_relation_zero _ relation1879_mem
theorem relation1880_mem : "9,1,829,1;8,1,873,1;0,3,1076,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block1[14]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1880_zero : nativeImage "9,1,829,1;8,1,873,1;0,3,1076,1" = 0 := by
  change projection (relationPolynomial "9,1,829,1;8,1,873,1;0,3,1076,1") = 0
  exact csv_relation_zero _ relation1880_mem
theorem relation1881_mem : "110,1,258,1;71,1,344,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block1[20]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1881_zero : nativeImage "110,1,258,1;71,1,344,1" = 0 := by
  change projection (relationPolynomial "110,1,258,1;71,1,344,1") = 0
  exact csv_relation_zero _ relation1881_mem
theorem relation1882_mem : "71,1,344,1;49,1,489,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block1[21]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1882_zero : nativeImage "71,1,344,1;49,1,489,1" = 0 := by
  change projection (relationPolynomial "71,1,344,1;49,1,489,1") = 0
  exact csv_relation_zero _ relation1882_mem
theorem relation1883_mem : "49,1,489,1;31,1,596,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block1[22]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1883_zero : nativeImage "49,1,489,1;31,1,596,1" = 0 := by
  change projection (relationPolynomial "49,1,489,1;31,1,596,1") = 0
  exact csv_relation_zero _ relation1883_mem
theorem relation1884_mem : "31,1,596,1;19,1,686,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block1[23]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1884_zero : nativeImage "31,1,596,1;19,1,686,1" = 0 := by
  change projection (relationPolynomial "31,1,596,1;19,1,686,1") = 0
  exact csv_relation_zero _ relation1884_mem
theorem relation1885_mem : "19,1,686,1;16,1,723,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block1[24]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1885_zero : nativeImage "19,1,686,1;16,1,723,1" = 0 := by
  change projection (relationPolynomial "19,1,686,1;16,1,723,1") = 0
  exact csv_relation_zero _ relation1885_mem
theorem relation1886_mem : "16,1,723,1;8,1,872,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block1[25]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1886_zero : nativeImage "16,1,723,1;8,1,872,1" = 0 := by
  change projection (relationPolynomial "16,1,723,1;8,1,872,1") = 0
  exact csv_relation_zero _ relation1886_mem
theorem relation1887_mem : "19,1,685,1;8,1,871,1;1,1,59,1,402,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block2[18]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1887_zero : nativeImage "19,1,685,1;8,1,871,1;1,1,59,1,402,1" = 0 := by
  change projection (relationPolynomial "19,1,685,1;8,1,871,1;1,1,59,1,402,1") = 0
  exact csv_relation_zero _ relation1887_mem
theorem relation1888_mem : "74,1,352,1;68,1,394,1;68,1,392,1;67,1,397,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block9[6]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1888_zero : nativeImage "74,1,352,1;68,1,394,1;68,1,392,1;67,1,397,1" = 0 := by
  change projection (relationPolynomial "74,1,352,1;68,1,394,1;68,1,392,1;67,1,397,1") = 0
  exact csv_relation_zero _ relation1888_mem
theorem relation1889_mem : "68,1,392,1;67,1,396,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block9[7]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1889_zero : nativeImage "68,1,392,1;67,1,396,1" = 0 := by
  change projection (relationPolynomial "68,1,392,1;67,1,396,1") = 0
  exact csv_relation_zero _ relation1889_mem
theorem relation1890_mem : "68,1,394,1;2,1,1091,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block9[26]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1890_zero : nativeImage "68,1,394,1;2,1,1091,1" = 0 := by
  change projection (relationPolynomial "68,1,394,1;2,1,1091,1") = 0
  exact csv_relation_zero _ relation1890_mem
theorem relation1891_mem : "67,1,396,1;0,1,1135,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block9[29]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1891_zero : nativeImage "67,1,396,1;0,1,1135,1" = 0 := by
  change projection (relationPolynomial "67,1,396,1;0,1,1135,1") = 0
  exact csv_relation_zero _ relation1891_mem
theorem relation1892_mem : "2,1,1091,1;0,2,1118,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block9[30]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1892_zero : nativeImage "2,1,1091,1;0,2,1118,1" = 0 := by
  change projection (relationPolynomial "2,1,1091,1;0,2,1118,1") = 0
  exact csv_relation_zero _ relation1892_mem
theorem relation1893_mem : "68,1,388,1;61,1,442,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block11[26]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1893_zero : nativeImage "68,1,388,1;61,1,442,1" = 0 := by
  change projection (relationPolynomial "68,1,388,1;61,1,442,1") = 0
  exact csv_relation_zero _ relation1893_mem
theorem relation1894_mem : "61,1,442,1;48,1,513,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block11[30]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1894_zero : nativeImage "61,1,442,1;48,1,513,1" = 0 := by
  change projection (relationPolynomial "61,1,442,1;48,1,513,1") = 0
  exact csv_relation_zero _ relation1894_mem
theorem relation1895_mem : "48,1,513,1;7,1,910,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block12[12]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1895_zero : nativeImage "48,1,513,1;7,1,910,1" = 0 := by
  change projection (relationPolynomial "48,1,513,1;7,1,910,1") = 0
  exact csv_relation_zero _ relation1895_mem
theorem relation1896_mem : "7,1,910,1;5,1,938,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block12[13]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1896_zero : nativeImage "7,1,910,1;5,1,938,1" = 0 := by
  change projection (relationPolynomial "7,1,910,1;5,1,938,1") = 0
  exact csv_relation_zero _ relation1896_mem
theorem relation1897_mem : "5,1,938,1;3,1,1022,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block12[14]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1897_zero : nativeImage "5,1,938,1;3,1,1022,1" = 0 := by
  change projection (relationPolynomial "5,1,938,1;3,1,1022,1") = 0
  exact csv_relation_zero _ relation1897_mem
theorem relation1898_mem : "67,1,391,1;3,1,1020,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block12[16]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1898_zero : nativeImage "67,1,391,1;3,1,1020,1" = 0 := by
  change projection (relationPolynomial "67,1,391,1;3,1,1020,1") = 0
  exact csv_relation_zero _ relation1898_mem
theorem relation1899_mem : "67,1,390,1;18,2,385,1;3,1,1022,1;2,1,1088,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block12[18]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1899_zero : nativeImage "67,1,390,1;18,2,385,1;3,1,1022,1;2,1,1088,1" = 0 := by
  change projection (relationPolynomial "67,1,390,1;18,2,385,1;3,1,1022,1;2,1,1088,1") = 0
  exact csv_relation_zero _ relation1899_mem
theorem relation1900_mem : "3,1,1022,1;1,2,1090,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block12[21]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1900_zero : nativeImage "3,1,1022,1;1,2,1090,1" = 0 := by
  change projection (relationPolynomial "3,1,1022,1;1,2,1090,1") = 0
  exact csv_relation_zero _ relation1900_mem
theorem relation1901_mem : "18,2,385,1;3,1,1021,1;1,2,1090,1;0,1,1131,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block12[22]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1901_zero : nativeImage "18,2,385,1;3,1,1021,1;1,2,1090,1;0,1,1131,1" = 0 := by
  change projection (relationPolynomial "18,2,385,1;3,1,1021,1;1,2,1090,1;0,1,1131,1") = 0
  exact csv_relation_zero _ relation1901_mem
theorem relation1902_mem : "3,1,1021,1;0,1,1131,1;0,2,2,1,1057,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block12[25]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1902_zero : nativeImage "3,1,1021,1;0,1,1131,1;0,2,2,1,1057,1" = 0 := by
  change projection (relationPolynomial "3,1,1021,1;0,1,1131,1;0,2,2,1,1057,1") = 0
  exact csv_relation_zero _ relation1902_mem
theorem relation1903_mem : "68,1,387,1;67,1,388,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block13[16]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1903_zero : nativeImage "68,1,387,1;67,1,388,1" = 0 := by
  change projection (relationPolynomial "68,1,387,1;67,1,388,1") = 0
  exact csv_relation_zero _ relation1903_mem
theorem relation1904_mem : "67,1,388,1;1,1,1112,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block14[21]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1904_zero : nativeImage "67,1,388,1;1,1,1112,1" = 0 := by
  change projection (relationPolynomial "67,1,388,1;1,1,1112,1") = 0
  exact csv_relation_zero _ relation1904_mem
theorem relation1905_mem : "2,1,1087,1;1,2,1088,1;0,6,66,1,324,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block14[27]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1905_zero : nativeImage "2,1,1087,1;1,2,1088,1;0,6,66,1,324,1" = 0 := by
  change projection (relationPolynomial "2,1,1087,1;1,2,1088,1;0,6,66,1,324,1") = 0
  exact csv_relation_zero _ relation1905_mem
theorem relation1906_mem : "68,1,385,1;64,1,413,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block20[28]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1906_zero : nativeImage "68,1,385,1;64,1,413,1" = 0 := by
  change projection (relationPolynomial "68,1,385,1;64,1,413,1") = 0
  exact csv_relation_zero _ relation1906_mem
theorem relation1907_mem : "64,1,413,1;64,1,412,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block20[29]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1907_zero : nativeImage "64,1,413,1;64,1,412,1" = 0 := by
  change projection (relationPolynomial "64,1,413,1;64,1,412,1") = 0
  exact csv_relation_zero _ relation1907_mem
theorem relation1908_mem : "64,1,412,1;61,1,439,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block20[31]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1908_zero : nativeImage "64,1,412,1;61,1,439,1" = 0 := by
  change projection (relationPolynomial "64,1,412,1;61,1,439,1") = 0
  exact csv_relation_zero _ relation1908_mem
theorem relation1909_mem : "61,1,439,1;7,1,905,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block21[22]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1909_zero : nativeImage "61,1,439,1;7,1,905,1" = 0 := by
  change projection (relationPolynomial "61,1,439,1;7,1,905,1") = 0
  exact csv_relation_zero _ relation1909_mem
theorem relation1910_mem : "7,1,905,1;3,1,1012,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block21[25]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1910_zero : nativeImage "7,1,905,1;3,1,1012,1" = 0 := by
  change projection (relationPolynomial "7,1,905,1;3,1,1012,1") = 0
  exact csv_relation_zero _ relation1910_mem
theorem relation1911_mem : "3,1,1012,1;1,2,1086,1" ∈ LinE2.RawData.relations := by
  exact relation_member 54 chunkBound rows transcription
    (block21[28]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1911_zero : nativeImage "3,1,1012,1;1,2,1086,1" = 0 := by
  change projection (relationPolynomial "3,1,1012,1;1,2,1086,1") = 0
  exact csv_relation_zero _ relation1911_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk054
