module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk013
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[13]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 13 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[13]'(chunkBound) =
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
theorem relation664_mem : "23,1,220,1;13,2,168,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block0[0]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation664_zero : nativeImage "23,1,220,1;13,2,168,1" = 0 := by
  change projection (relationPolynomial "23,1,220,1;13,2,168,1") = 0
  exact csv_relation_zero _ relation664_mem
theorem relation665_mem : "13,1,278,1;9,1,291,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block0[2]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation665_zero : nativeImage "13,1,278,1;9,1,291,1" = 0 := by
  change projection (relationPolynomial "13,1,278,1;9,1,291,1") = 0
  exact csv_relation_zero _ relation665_mem
theorem relation666_mem : "9,1,291,1;8,1,317,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block0[3]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation666_zero : nativeImage "9,1,291,1;8,1,317,1" = 0 := by
  change projection (relationPolynomial "9,1,291,1;8,1,317,1") = 0
  exact csv_relation_zero _ relation666_mem
theorem relation667_mem : "8,1,317,1;8,1,316,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block0[4]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation667_zero : nativeImage "8,1,317,1;8,1,316,1" = 0 := by
  change projection (relationPolynomial "8,1,317,1;8,1,316,1") = 0
  exact csv_relation_zero _ relation667_mem
theorem relation668_mem : "32,1,194,1;23,1,219,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block0[15]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation668_zero : nativeImage "32,1,194,1;23,1,219,1" = 0 := by
  change projection (relationPolynomial "32,1,194,1;23,1,219,1") = 0
  exact csv_relation_zero _ relation668_mem
theorem relation669_mem : "23,1,219,1;13,2,167,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block0[18]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation669_zero : nativeImage "23,1,219,1;13,2,167,1" = 0 := by
  change projection (relationPolynomial "23,1,219,1;13,2,167,1") = 0
  exact csv_relation_zero _ relation669_mem
theorem relation670_mem : "22,1,219,1;8,1,13,1,194,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block1[2]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation670_zero : nativeImage "22,1,219,1;8,1,13,1,194,1" = 0 := by
  change projection (relationPolynomial "22,1,219,1;8,1,13,1,194,1") = 0
  exact csv_relation_zero _ relation670_mem
theorem relation671_mem : "17,1,248,1;8,2,219,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block1[14]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation671_zero : nativeImage "17,1,248,1;8,2,219,1" = 0 := by
  change projection (relationPolynomial "17,1,248,1;8,2,219,1") = 0
  exact csv_relation_zero _ relation671_mem
theorem relation672_mem : "0,2,8,1,64,2" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block1[27]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation672_zero : nativeImage "0,2,8,1,64,2" = 0 := by
  change projection (relationPolynomial "0,2,8,1,64,2") = 0
  exact csv_relation_zero _ relation672_mem
theorem relation673_mem : "17,1,247,1;17,1,246,1;8,3,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block2[21]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation673_zero : nativeImage "17,1,247,1;17,1,246,1;8,3,149,1" = 0 := by
  change projection (relationPolynomial "17,1,247,1;17,1,246,1;8,3,149,1") = 0
  exact csv_relation_zero _ relation673_mem
theorem relation674_mem : "17,1,246,1;0,1,509,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block2[22]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation674_zero : nativeImage "17,1,246,1;0,1,509,1" = 0 := by
  change projection (relationPolynomial "17,1,246,1;0,1,509,1") = 0
  exact csv_relation_zero _ relation674_mem
theorem relation675_mem : "17,1,245,1;8,1,315,1;0,3,491,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block2[29]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation675_zero : nativeImage "17,1,245,1;8,1,315,1;0,3,491,1" = 0 := by
  change projection (relationPolynomial "17,1,245,1;8,1,315,1;0,3,491,1") = 0
  exact csv_relation_zero _ relation675_mem
theorem relation676_mem : "3,2,69,1,76,1;0,3,507,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block5[11]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation676_zero : nativeImage "3,2,69,1,76,1;0,3,507,1" = 0 := by
  change projection (relationPolynomial "3,2,69,1,76,1;0,3,507,1") = 0
  exact csv_relation_zero _ relation676_mem
theorem relation677_mem : "70,1,122,1;1,1,513,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block5[15]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation677_zero : nativeImage "70,1,122,1;1,1,513,1" = 0 := by
  change projection (relationPolynomial "70,1,122,1;1,1,513,1") = 0
  exact csv_relation_zero _ relation677_mem
theorem relation678_mem : "29,1,212,1;9,1,13,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block9[27]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation678_zero : nativeImage "29,1,212,1;9,1,13,1,188,1" = 0 := by
  change projection (relationPolynomial "29,1,212,1;9,1,13,1,188,1") = 0
  exact csv_relation_zero _ relation678_mem
theorem relation679_mem : "10,1,292,1;9,1,300,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block11[0]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation679_zero : nativeImage "10,1,292,1;9,1,300,1" = 0 := by
  change projection (relationPolynomial "10,1,292,1;9,1,300,1") = 0
  exact csv_relation_zero _ relation679_mem
theorem relation680_mem : "9,1,300,1;5,1,369,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block11[2]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation680_zero : nativeImage "9,1,300,1;5,1,369,1" = 0 := by
  change projection (relationPolynomial "9,1,300,1;5,1,369,1") = 0
  exact csv_relation_zero _ relation680_mem
theorem relation681_mem : "5,1,369,1;1,1,510,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block11[5]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation681_zero : nativeImage "5,1,369,1;1,1,510,1" = 0 := by
  change projection (relationPolynomial "5,1,369,1;1,1,510,1") = 0
  exact csv_relation_zero _ relation681_mem
theorem relation682_mem : "17,1,254,1;8,1,327,1;6,1,347,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block12[5]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation682_zero : nativeImage "17,1,254,1;8,1,327,1;6,1,347,1" = 0 := by
  change projection (relationPolynomial "17,1,254,1;8,1,327,1;6,1,347,1") = 0
  exact csv_relation_zero _ relation682_mem
theorem relation683_mem : "6,1,347,1;0,1,517,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block12[7]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation683_zero : nativeImage "6,1,347,1;0,1,517,1" = 0 := by
  change projection (relationPolynomial "6,1,347,1;0,1,517,1") = 0
  exact csv_relation_zero _ relation683_mem
theorem relation684_mem : "0,1,517,1;0,9,440,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block12[9]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation684_zero : nativeImage "0,1,517,1;0,9,440,1" = 0 := by
  change projection (relationPolynomial "0,1,517,1;0,9,440,1") = 0
  exact csv_relation_zero _ relation684_mem
theorem relation685_mem : "17,1,252,1;16,1,253,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block16[31]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation685_zero : nativeImage "17,1,252,1;16,1,253,1" = 0 := by
  change projection (relationPolynomial "17,1,252,1;16,1,253,1") = 0
  exact csv_relation_zero _ relation685_mem
theorem relation686_mem : "16,1,253,1;9,1,296,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block17[0]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation686_zero : nativeImage "16,1,253,1;9,1,296,1" = 0 := by
  change projection (relationPolynomial "16,1,253,1;9,1,296,1") = 0
  exact csv_relation_zero _ relation686_mem
theorem relation687_mem : "9,1,296,1;8,1,326,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block17[1]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation687_zero : nativeImage "9,1,296,1;8,1,326,1" = 0 := by
  change projection (relationPolynomial "9,1,296,1;8,1,326,1") = 0
  exact csv_relation_zero _ relation687_mem
theorem relation688_mem : "9,1,295,1;8,1,325,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block17[10]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation688_zero : nativeImage "9,1,295,1;8,1,325,1" = 0 := by
  change projection (relationPolynomial "9,1,295,1;8,1,325,1") = 0
  exact csv_relation_zero _ relation688_mem
theorem relation689_mem : "69,1,130,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block18[0]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation689_zero : nativeImage "69,1,130,1" = 0 := by
  change projection (relationPolynomial "69,1,130,1") = 0
  exact csv_relation_zero _ relation689_mem
theorem relation690_mem : "69,1,129,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block18[5]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation690_zero : nativeImage "69,1,129,1" = 0 := by
  change projection (relationPolynomial "69,1,129,1") = 0
  exact csv_relation_zero _ relation690_mem
theorem relation691_mem : "3,2,368,1;1,1,525,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block18[9]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation691_zero : nativeImage "3,2,368,1;1,1,525,1" = 0 := by
  change projection (relationPolynomial "3,2,368,1;1,1,525,1") = 0
  exact csv_relation_zero _ relation691_mem
theorem relation692_mem : "3,1,466,1;1,1,524,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block18[14]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation692_zero : nativeImage "3,1,466,1;1,1,524,1" = 0 := by
  change projection (relationPolynomial "3,1,466,1;1,1,524,1") = 0
  exact csv_relation_zero _ relation692_mem
theorem relation693_mem : "2,1,504,1;1,1,523,1;0,1,535,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block18[28]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation693_zero : nativeImage "2,1,504,1;1,1,523,1;0,1,535,1" = 0 := by
  change projection (relationPolynomial "2,1,504,1;1,1,523,1;0,1,535,1") = 0
  exact csv_relation_zero _ relation693_mem
theorem relation694_mem : "0,1,535,1;0,2,524,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block18[30]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation694_zero : nativeImage "0,1,535,1;0,2,524,1" = 0 := by
  change projection (relationPolynomial "0,1,535,1;0,2,524,1") = 0
  exact csv_relation_zero _ relation694_mem
theorem relation695_mem : "38,1,197,1;35,1,203,1;3,1,463,1;3,2,366,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block19[12]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation695_zero : nativeImage "38,1,197,1;35,1,203,1;3,1,463,1;3,2,366,1" = 0 := by
  change projection (relationPolynomial "38,1,197,1;35,1,203,1;3,1,463,1;3,2,366,1") = 0
  exact csv_relation_zero _ relation695_mem
theorem relation696_mem : "35,1,203,1;1,1,521,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block19[14]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation696_zero : nativeImage "35,1,203,1;1,1,521,1" = 0 := by
  change projection (relationPolynomial "35,1,203,1;1,1,521,1") = 0
  exact csv_relation_zero _ relation696_mem
theorem relation697_mem : "3,2,366,1;1,1,521,1;0,1,3,2,352,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block19[16]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation697_zero : nativeImage "3,2,366,1;1,1,521,1;0,1,3,2,352,1" = 0 := by
  change projection (relationPolynomial "3,2,366,1;1,1,521,1;0,1,3,2,352,1") = 0
  exact csv_relation_zero _ relation697_mem
theorem relation698_mem : "9,1,314,1;8,1,338,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block20[14]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation698_zero : nativeImage "9,1,314,1;8,1,338,1" = 0 := by
  change projection (relationPolynomial "9,1,314,1;8,1,338,1") = 0
  exact csv_relation_zero _ relation698_mem
theorem relation699_mem : "69,1,127,1;9,1,312,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block21[17]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation699_zero : nativeImage "69,1,127,1;9,1,312,1" = 0 := by
  change projection (relationPolynomial "69,1,127,1;9,1,312,1") = 0
  exact csv_relation_zero _ relation699_mem
theorem relation700_mem : "9,1,312,1;8,1,337,1" ∈ LinE2.RawData.relations := by
  exact relation_member 13 chunkBound rows transcription
    (block21[18]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation700_zero : nativeImage "9,1,312,1;8,1,337,1" = 0 := by
  change projection (relationPolynomial "9,1,312,1;8,1,337,1") = 0
  exact csv_relation_zero _ relation700_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk013
