module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk055
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[55]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 55 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[55]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block1_mem : block1 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 1) (by decide)
private theorem block1_in_rows (r : List Char) (hr : r ∈ block1) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block1, block1_mem, hr⟩
private theorem block3_mem : block3 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 3) (by decide)
private theorem block3_in_rows (r : List Char) (hr : r ∈ block3) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block3, block3_mem, hr⟩
private theorem block5_mem : block5 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 5) (by decide)
private theorem block5_in_rows (r : List Char) (hr : r ∈ block5) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block5, block5_mem, hr⟩
private theorem block17_mem : block17 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 17) (by decide)
private theorem block17_in_rows (r : List Char) (hr : r ∈ block17) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block17, block17_mem, hr⟩
private theorem block18_mem : block18 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 18) (by decide)
private theorem block18_in_rows (r : List Char) (hr : r ∈ block18) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block18, block18_mem, hr⟩
private theorem block21_mem : block21 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 21) (by decide)
private theorem block21_in_rows (r : List Char) (hr : r ∈ block21) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block21, block21_mem, hr⟩
private theorem block22_mem : block22 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 22) (by decide)
private theorem block22_in_rows (r : List Char) (hr : r ∈ block22) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block22, block22_mem, hr⟩
private theorem block23_mem : block23 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 23) (by decide)
private theorem block23_in_rows (r : List Char) (hr : r ∈ block23) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block23, block23_mem, hr⟩
theorem relation1912_mem : "23,1,668,1;9,1,80,1,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block1[7]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1912_zero : nativeImage "23,1,668,1;9,1,80,1,212,1" = 0 := by
  change projection (relationPolynomial "23,1,668,1;9,1,80,1,212,1") = 0
  exact csv_relation_zero _ relation1912_mem
theorem relation1913_mem : "20,1,705,1;8,1,9,1,640,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block3[9]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1913_zero : nativeImage "20,1,705,1;8,1,9,1,640,1" = 0 := by
  change projection (relationPolynomial "20,1,705,1;8,1,9,1,640,1") = 0
  exact csv_relation_zero _ relation1913_mem
theorem relation1914_mem : "17,1,738,1;13,1,813,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block5[18]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1914_zero : nativeImage "17,1,738,1;13,1,813,1" = 0 := by
  change projection (relationPolynomial "17,1,738,1;13,1,813,1") = 0
  exact csv_relation_zero _ relation1914_mem
theorem relation1915_mem : "13,1,813,1;8,2,668,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block5[23]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1915_zero : nativeImage "13,1,813,1;8,2,668,1" = 0 := by
  change projection (relationPolynomial "13,1,813,1;8,2,668,1") = 0
  exact csv_relation_zero _ relation1915_mem
theorem relation1916_mem : "0,1,8,1,138,1,149,1;0,1,8,1,16,1,17,1,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block17[2]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1916_zero : nativeImage "0,1,8,1,138,1,149,1;0,1,8,1,16,1,17,1,260,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,138,1,149,1;0,1,8,1,16,1,17,1,260,1") = 0
  exact csv_relation_zero _ relation1916_mem
theorem relation1917_mem : "0,1,8,1,64,1,244,1;0,1,8,3,491,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block17[21]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1917_zero : nativeImage "0,1,8,1,64,1,244,1;0,1,8,3,491,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,64,1,244,1;0,1,8,3,491,1") = 0
  exact csv_relation_zero _ relation1917_mem
theorem relation1918_mem : "138,1,224,1;137,1,225,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block18[14]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1918_zero : nativeImage "138,1,224,1;137,1,225,1" = 0 := by
  change projection (relationPolynomial "138,1,224,1;137,1,225,1") = 0
  exact csv_relation_zero _ relation1918_mem
theorem relation1919_mem : "137,1,225,1;64,1,403,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block18[20]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1919_zero : nativeImage "137,1,225,1;64,1,403,1" = 0 := by
  change projection (relationPolynomial "137,1,225,1;64,1,403,1") = 0
  exact csv_relation_zero _ relation1919_mem
theorem relation1920_mem : "0,1,8,1,871,1;0,7,1033,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block21[22]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1920_zero : nativeImage "0,1,8,1,871,1;0,7,1033,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,871,1;0,7,1033,1") = 0
  exact csv_relation_zero _ relation1920_mem
theorem relation1921_mem : "17,1,736,1;8,4,295,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block22[28]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1921_zero : nativeImage "17,1,736,1;8,4,295,1" = 0 := by
  change projection (relationPolynomial "17,1,736,1;8,4,295,1") = 0
  exact csv_relation_zero _ relation1921_mem
theorem relation1922_mem : "60,1,431,1;49,1,498,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block23[5]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1922_zero : nativeImage "60,1,431,1;49,1,498,1" = 0 := by
  change projection (relationPolynomial "60,1,431,1;49,1,498,1") = 0
  exact csv_relation_zero _ relation1922_mem
theorem relation1923_mem : "49,1,498,1;42,1,553,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block23[6]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1923_zero : nativeImage "49,1,498,1;42,1,553,1" = 0 := by
  change projection (relationPolynomial "49,1,498,1;42,1,553,1") = 0
  exact csv_relation_zero _ relation1923_mem
theorem relation1924_mem : "42,1,553,1;31,1,607,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block23[7]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1924_zero : nativeImage "42,1,553,1;31,1,607,1" = 0 := by
  change projection (relationPolynomial "42,1,553,1;31,1,607,1") = 0
  exact csv_relation_zero _ relation1924_mem
theorem relation1925_mem : "31,1,607,1;16,1,736,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block23[10]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1925_zero : nativeImage "31,1,607,1;16,1,736,1" = 0 := by
  change projection (relationPolynomial "31,1,607,1;16,1,736,1") = 0
  exact csv_relation_zero _ relation1925_mem
theorem relation1926_mem : "16,1,736,1;8,1,886,1" ∈ LinE2.RawData.relations := by
  exact relation_member 55 chunkBound rows transcription
    (block23[11]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation1926_zero : nativeImage "16,1,736,1;8,1,886,1" = 0 := by
  change projection (relationPolynomial "16,1,736,1;8,1,886,1") = 0
  exact csv_relation_zero _ relation1926_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk055
