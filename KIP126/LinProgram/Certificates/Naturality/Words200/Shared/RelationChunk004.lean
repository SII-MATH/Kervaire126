module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk004
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[4]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 4 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[4]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
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
private theorem block14_mem : block14 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 14) (by decide)
private theorem block14_in_rows (r : List Char) (hr : r ∈ block14) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block14, block14_mem, hr⟩
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
private theorem block23_mem : block23 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 23) (by decide)
private theorem block23_in_rows (r : List Char) (hr : r ∈ block23) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block23, block23_mem, hr⟩
private theorem block24_mem : block24 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 24) (by decide)
private theorem block24_in_rows (r : List Char) (hr : r ∈ block24) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block24, block24_mem, hr⟩
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
private theorem block30_mem : block30 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 30) (by decide)
private theorem block30_in_rows (r : List Char) (hr : r ∈ block30) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block30, block30_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation291_mem : "32,1,80,1;23,1,101,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block3[22]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation291_zero : nativeImage "32,1,80,1;23,1,101,1" = 0 := by
  change projection (relationPolynomial "32,1,80,1;23,1,101,1") = 0
  exact csv_relation_zero _ relation291_mem
theorem relation292_mem : "22,1,101,1;8,1,13,1,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block4[0]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation292_zero : nativeImage "22,1,101,1;8,1,13,1,80,1" = 0 := by
  change projection (relationPolynomial "22,1,101,1;8,1,13,1,80,1") = 0
  exact csv_relation_zero _ relation292_mem
theorem relation293_mem : "17,1,118,1;8,1,154,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block4[17]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation293_zero : nativeImage "17,1,118,1;8,1,154,1" = 0 := by
  change projection (relationPolynomial "17,1,118,1;8,1,154,1") = 0
  exact csv_relation_zero _ relation293_mem
theorem relation294_mem : "20,1,112,1;8,1,17,1,64,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block4[30]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation294_zero : nativeImage "20,1,112,1;8,1,17,1,64,1" = 0 := by
  change projection (relationPolynomial "20,1,112,1;8,1,17,1,64,1") = 0
  exact csv_relation_zero _ relation294_mem
theorem relation295_mem : "13,1,137,1;9,1,146,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block5[9]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation295_zero : nativeImage "13,1,137,1;9,1,146,1" = 0 := by
  change projection (relationPolynomial "13,1,137,1;9,1,146,1") = 0
  exact csv_relation_zero _ relation295_mem
theorem relation296_mem : "9,1,146,1;8,1,16,1,64,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block5[10]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation296_zero : nativeImage "9,1,146,1;8,1,16,1,64,1" = 0 := by
  change projection (relationPolynomial "9,1,146,1;8,1,16,1,64,1") = 0
  exact csv_relation_zero _ relation296_mem
theorem relation297_mem : "17,1,116,1;16,1,117,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block6[9]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation297_zero : nativeImage "17,1,116,1;16,1,117,1" = 0 := by
  change projection (relationPolynomial "17,1,116,1;16,1,117,1") = 0
  exact csv_relation_zero _ relation297_mem
theorem relation298_mem : "16,1,117,1;8,1,153,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block6[10]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation298_zero : nativeImage "16,1,117,1;8,1,153,1" = 0 := by
  change projection (relationPolynomial "16,1,117,1;8,1,153,1") = 0
  exact csv_relation_zero _ relation298_mem
theorem relation299_mem : "9,1,145,1;8,1,152,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block6[16]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation299_zero : nativeImage "9,1,145,1;8,1,152,1" = 0 := by
  change projection (relationPolynomial "9,1,145,1;8,1,152,1") = 0
  exact csv_relation_zero _ relation299_mem
theorem relation300_mem : "43,1,69,1;7,1,163,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block6[29]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation300_zero : nativeImage "43,1,69,1;7,1,163,1" = 0 := by
  change projection (relationPolynomial "43,1,69,1;7,1,163,1") = 0
  exact csv_relation_zero _ relation300_mem
theorem relation301_mem : "2,1,213,1;1,1,3,1,190,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block7[10]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation301_zero : nativeImage "2,1,213,1;1,1,3,1,190,1" = 0 := by
  change projection (relationPolynomial "2,1,213,1;1,1,3,1,190,1") = 0
  exact csv_relation_zero _ relation301_mem
theorem relation302_mem : "0,1,2,1,209,1;0,2,221,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block7[28]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation302_zero : nativeImage "0,1,2,1,209,1;0,2,221,1" = 0 := by
  change projection (relationPolynomial "0,1,2,1,209,1;0,2,221,1") = 0
  exact csv_relation_zero _ relation302_mem
theorem relation303_mem : "23,1,107,1;9,1,13,1,75,1;0,2,3,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block8[28]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation303_zero : nativeImage "23,1,107,1;9,1,13,1,75,1;0,2,3,1,188,1" = 0 := by
  change projection (relationPolynomial "23,1,107,1;9,1,13,1,75,1;0,2,3,1,188,1") = 0
  exact csv_relation_zero _ relation303_mem
theorem relation304_mem : "23,1,105,1;13,2,67,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block9[7]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation304_zero : nativeImage "23,1,105,1;13,2,67,1" = 0 := by
  change projection (relationPolynomial "23,1,105,1;13,2,67,1") = 0
  exact csv_relation_zero _ relation304_mem
theorem relation305_mem : "9,1,149,1;8,1,160,1;5,1,172,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block14[9]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation305_zero : nativeImage "9,1,149,1;8,1,160,1;5,1,172,1" = 0 := by
  change projection (relationPolynomial "9,1,149,1;8,1,160,1;5,1,172,1") = 0
  exact csv_relation_zero _ relation305_mem
theorem relation306_mem : "29,1,101,1;9,1,13,1,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block19[12]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation306_zero : nativeImage "29,1,101,1;9,1,13,1,80,1" = 0 := by
  change projection (relationPolynomial "29,1,101,1;9,1,13,1,80,1") = 0
  exact csv_relation_zero _ relation306_mem
theorem relation307_mem : "17,1,127,1;9,1,154,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block20[12]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation307_zero : nativeImage "17,1,127,1;9,1,154,1" = 0 := by
  change projection (relationPolynomial "17,1,127,1;9,1,154,1") = 0
  exact csv_relation_zero _ relation307_mem
theorem relation308_mem : "9,1,154,1;8,1,162,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block20[13]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation308_zero : nativeImage "9,1,154,1;8,1,162,1" = 0 := by
  change projection (relationPolynomial "9,1,154,1;8,1,162,1") = 0
  exact csv_relation_zero _ relation308_mem
theorem relation309_mem : "22,1,112,1;19,1,118,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block20[27]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation309_zero : nativeImage "22,1,112,1;19,1,118,1" = 0 := by
  change projection (relationPolynomial "22,1,112,1;19,1,118,1") = 0
  exact csv_relation_zero _ relation309_mem
theorem relation310_mem : "19,1,118,1;16,1,127,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block20[28]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation310_zero : nativeImage "19,1,118,1;16,1,127,1" = 0 := by
  change projection (relationPolynomial "19,1,118,1;16,1,127,1") = 0
  exact csv_relation_zero _ relation310_mem
theorem relation311_mem : "16,1,127,1;13,1,147,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block20[30]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation311_zero : nativeImage "16,1,127,1;13,1,147,1" = 0 := by
  change projection (relationPolynomial "16,1,127,1;13,1,147,1") = 0
  exact csv_relation_zero _ relation311_mem
theorem relation312_mem : "13,1,147,1;8,2,113,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block20[31]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation312_zero : nativeImage "13,1,147,1;8,2,113,1" = 0 := by
  change projection (relationPolynomial "13,1,147,1;8,2,113,1") = 0
  exact csv_relation_zero _ relation312_mem
theorem relation313_mem : "0,1,8,1,160,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block21[1]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation313_zero : nativeImage "0,1,8,1,160,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,160,1") = 0
  exact csv_relation_zero _ relation313_mem
theorem relation314_mem : "13,1,146,1;8,2,112,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block21[12]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation314_zero : nativeImage "13,1,146,1;8,2,112,1" = 0 := by
  change projection (relationPolynomial "13,1,146,1;8,2,112,1") = 0
  exact csv_relation_zero _ relation314_mem
theorem relation315_mem : "17,1,125,1;8,4,31,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block21[30]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation315_zero : nativeImage "17,1,125,1;8,4,31,1" = 0 := by
  change projection (relationPolynomial "17,1,125,1;8,4,31,1") = 0
  exact csv_relation_zero _ relation315_mem
theorem relation316_mem : "42,1,71,1;31,1,88,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block22[2]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation316_zero : nativeImage "42,1,71,1;31,1,88,1" = 0 := by
  change projection (relationPolynomial "42,1,71,1;31,1,88,1") = 0
  exact csv_relation_zero _ relation316_mem
theorem relation317_mem : "17,2,50,1;8,1,161,1;0,3,224,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block22[7]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation317_zero : nativeImage "17,2,50,1;8,1,161,1;0,3,224,1" = 0 := by
  change projection (relationPolynomial "17,2,50,1;8,1,161,1;0,3,224,1") = 0
  exact csv_relation_zero _ relation317_mem
theorem relation318_mem : "45,1,69,1;3,1,209,1;0,2,235,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block23[22]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation318_zero : nativeImage "45,1,69,1;3,1,209,1;0,2,235,1" = 0 := by
  change projection (relationPolynomial "45,1,69,1;3,1,209,1;0,2,235,1") = 0
  exact csv_relation_zero _ relation318_mem
theorem relation319_mem : "32,1,95,1;13,2,75,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block24[6]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation319_zero : nativeImage "32,1,95,1;13,2,75,1" = 0 := by
  change projection (relationPolynomial "32,1,95,1;13,2,75,1") = 0
  exact csv_relation_zero _ relation319_mem
theorem relation320_mem : "1,1,241,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block27[22]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation320_zero : nativeImage "1,1,241,1" = 0 := by
  change projection (relationPolynomial "1,1,241,1") = 0
  exact csv_relation_zero _ relation320_mem
theorem relation321_mem : "0,2,241,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block28[1]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation321_zero : nativeImage "0,2,241,1" = 0 := by
  change projection (relationPolynomial "0,2,241,1") = 0
  exact csv_relation_zero _ relation321_mem
theorem relation322_mem : "0,1,243,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block29[4]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation322_zero : nativeImage "0,1,243,1" = 0 := by
  change projection (relationPolynomial "0,1,243,1") = 0
  exact csv_relation_zero _ relation322_mem
theorem relation323_mem : "9,1,160,1;8,1,166,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block30[17]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation323_zero : nativeImage "9,1,160,1;8,1,166,1" = 0 := by
  change projection (relationPolynomial "9,1,160,1;8,1,166,1") = 0
  exact csv_relation_zero _ relation323_mem
theorem relation324_mem : "0,2,8,2,112,1" ∈ LinE2.RawData.relations := by
  exact relation_member 4 chunkBound rows transcription
    (block31[3]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation324_zero : nativeImage "0,2,8,2,112,1" = 0 := by
  change projection (relationPolynomial "0,2,8,2,112,1") = 0
  exact csv_relation_zero _ relation324_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk004
