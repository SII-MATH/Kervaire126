module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.Support

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk015
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[15]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 15 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[15]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
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
private theorem block23_mem : block23 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 23) (by decide)
private theorem block23_in_rows (r : List Char) (hr : r ∈ block23) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block23, block23_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
theorem relation755_mem : "2,1,546,1;1,1,566,1;0,1,18,1,264,1;0,3,9,1,69,2" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block11[23]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation755_zero : nativeImage "2,1,546,1;1,1,566,1;0,1,18,1,264,1;0,3,9,1,69,2" = 0 := by
  change projection (relationPolynomial "2,1,546,1;1,1,566,1;0,1,18,1,264,1;0,3,9,1,69,2") = 0
  exact csv_relation_zero _ relation755_mem
theorem relation756_mem : "7,1,419,1;4,1,480,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block12[13]'(by decide)) (block12_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation756_zero : nativeImage "7,1,419,1;4,1,480,1" = 0 := by
  change projection (relationPolynomial "7,1,419,1;4,1,480,1") = 0
  exact csv_relation_zero _ relation756_mem
theorem relation757_mem : "2,1,541,1;1,1,3,1,485,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block13[26]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation757_zero : nativeImage "2,1,541,1;1,1,3,1,485,1" = 0 := by
  change projection (relationPolynomial "2,1,541,1;1,1,3,1,485,1") = 0
  exact csv_relation_zero _ relation757_mem
theorem relation758_mem : "23,1,251,1;19,1,264,1;18,1,267,1;9,1,351,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block15[10]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation758_zero : nativeImage "23,1,251,1;19,1,264,1;18,1,267,1;9,1,351,1" = 0 := by
  change projection (relationPolynomial "23,1,251,1;19,1,264,1;18,1,267,1;9,1,351,1") = 0
  exact csv_relation_zero _ relation758_mem
theorem relation759_mem : "18,1,267,1;11,1,335,1;8,1,387,1;8,1,386,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block15[12]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation759_zero : nativeImage "18,1,267,1;11,1,335,1;8,1,387,1;8,1,386,1" = 0 := by
  change projection (relationPolynomial "18,1,267,1;11,1,335,1;8,1,387,1;8,1,386,1") = 0
  exact csv_relation_zero _ relation759_mem
theorem relation760_mem : "19,1,264,1;6,1,419,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block15[13]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation760_zero : nativeImage "19,1,264,1;6,1,419,1" = 0 := by
  change projection (relationPolynomial "19,1,264,1;6,1,419,1") = 0
  exact csv_relation_zero _ relation760_mem
theorem relation761_mem : "9,1,351,1;8,1,387,1;8,1,386,1;6,1,419,1;5,1,442,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block15[14]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation761_zero : nativeImage "9,1,351,1;8,1,387,1;8,1,386,1;6,1,419,1;5,1,442,1" = 0 := by
  change projection (relationPolynomial "9,1,351,1;8,1,387,1;8,1,386,1;6,1,419,1;5,1,442,1") = 0
  exact csv_relation_zero _ relation761_mem
theorem relation762_mem : "11,1,335,1;3,2,417,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block15[17]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation762_zero : nativeImage "11,1,335,1;3,2,417,1" = 0 := by
  change projection (relationPolynomial "11,1,335,1;3,2,417,1") = 0
  exact csv_relation_zero _ relation762_mem
theorem relation763_mem : "3,2,417,1;1,1,43,1,189,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block15[18]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation763_zero : nativeImage "3,2,417,1;1,1,43,1,189,1" = 0 := by
  change projection (relationPolynomial "3,2,417,1;1,1,43,1,189,1") = 0
  exact csv_relation_zero _ relation763_mem
theorem relation764_mem : "5,1,442,1;1,1,43,1,189,1;1,2,540,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block15[19]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation764_zero : nativeImage "5,1,442,1;1,1,43,1,189,1;1,2,540,1" = 0 := by
  change projection (relationPolynomial "5,1,442,1;1,1,43,1,189,1;1,2,540,1") = 0
  exact csv_relation_zero _ relation764_mem
theorem relation765_mem : "68,1,141,1;18,1,266,1;12,1,333,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block16[5]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation765_zero : nativeImage "68,1,141,1;18,1,266,1;12,1,333,1" = 0 := by
  change projection (relationPolynomial "68,1,141,1;18,1,266,1;12,1,333,1") = 0
  exact csv_relation_zero _ relation765_mem
theorem relation766_mem : "12,1,333,1;8,1,18,1,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block16[7]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation766_zero : nativeImage "12,1,333,1;8,1,18,1,188,1" = 0 := by
  change projection (relationPolynomial "12,1,333,1;8,1,18,1,188,1") = 0
  exact csv_relation_zero _ relation766_mem
theorem relation767_mem : "18,1,266,1;8,1,18,1,188,1;7,2,267,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block16[8]'(by decide)) (block16_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation767_zero : nativeImage "18,1,266,1;8,1,18,1,188,1;7,2,267,1" = 0 := by
  change projection (relationPolynomial "18,1,266,1;8,1,18,1,188,1;7,2,267,1") = 0
  exact csv_relation_zero _ relation767_mem
theorem relation768_mem : "23,1,250,1;9,1,13,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block17[13]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation768_zero : nativeImage "23,1,250,1;9,1,13,1,209,1" = 0 := by
  change projection (relationPolynomial "23,1,250,1;9,1,13,1,209,1") = 0
  exact csv_relation_zero _ relation768_mem
theorem relation769_mem : "20,1,261,1;9,1,350,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block18[0]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation769_zero : nativeImage "20,1,261,1;9,1,350,1" = 0 := by
  change projection (relationPolynomial "20,1,261,1;9,1,350,1") = 0
  exact csv_relation_zero _ relation769_mem
theorem relation770_mem : "9,1,350,1;8,1,384,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block18[2]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation770_zero : nativeImage "9,1,350,1;8,1,384,1" = 0 := by
  change projection (relationPolynomial "9,1,350,1;8,1,384,1") = 0
  exact csv_relation_zero _ relation770_mem
theorem relation771_mem : "2,1,539,1;1,1,560,1;0,2,561,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block18[8]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation771_zero : nativeImage "2,1,539,1;1,1,560,1;0,2,561,1" = 0 := by
  change projection (relationPolynomial "2,1,539,1;1,1,560,1;0,2,561,1") = 0
  exact csv_relation_zero _ relation771_mem
theorem relation772_mem : "17,1,280,1;13,1,318,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block18[24]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation772_zero : nativeImage "17,1,280,1;13,1,318,1" = 0 := by
  change projection (relationPolynomial "17,1,280,1;13,1,318,1") = 0
  exact csv_relation_zero _ relation772_mem
theorem relation773_mem : "13,1,318,1;9,1,348,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block18[26]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation773_zero : nativeImage "13,1,318,1;9,1,348,1" = 0 := by
  change projection (relationPolynomial "13,1,318,1;9,1,348,1") = 0
  exact csv_relation_zero _ relation773_mem
theorem relation774_mem : "9,1,348,1;8,2,250,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block18[27]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation774_zero : nativeImage "9,1,348,1;8,2,250,1" = 0 := by
  change projection (relationPolynomial "9,1,348,1;8,2,250,1") = 0
  exact csv_relation_zero _ relation774_mem
theorem relation775_mem : "17,1,279,1;16,1,280,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block19[12]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation775_zero : nativeImage "17,1,279,1;16,1,280,1" = 0 := by
  change projection (relationPolynomial "17,1,279,1;16,1,280,1") = 0
  exact csv_relation_zero _ relation775_mem
theorem relation776_mem : "16,1,280,1;8,1,383,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block19[15]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation776_zero : nativeImage "16,1,280,1;8,1,383,1" = 0 := by
  change projection (relationPolynomial "16,1,280,1;8,1,383,1") = 0
  exact csv_relation_zero _ relation776_mem
theorem relation777_mem : "39,1,209,1;27,1,239,1;16,1,279,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block20[0]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation777_zero : nativeImage "39,1,209,1;27,1,239,1;16,1,279,1" = 0 := by
  change projection (relationPolynomial "39,1,209,1;27,1,239,1;16,1,279,1") = 0
  exact csv_relation_zero _ relation777_mem
theorem relation778_mem : "13,1,316,1;9,1,346,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block20[7]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation778_zero : nativeImage "13,1,316,1;9,1,346,1" = 0 := by
  change projection (relationPolynomial "13,1,316,1;9,1,346,1") = 0
  exact csv_relation_zero _ relation778_mem
theorem relation779_mem : "9,1,347,1;8,1,382,1;5,1,436,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block20[9]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation779_zero : nativeImage "9,1,347,1;8,1,382,1;5,1,436,1" = 0 := by
  change projection (relationPolynomial "9,1,347,1;8,1,382,1;5,1,436,1") = 0
  exact csv_relation_zero _ relation779_mem
theorem relation780_mem : "23,1,248,1;13,2,194,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block21[1]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation780_zero : nativeImage "23,1,248,1;13,2,194,1" = 0 := by
  change projection (relationPolynomial "23,1,248,1;13,2,194,1") = 0
  exact csv_relation_zero _ relation780_mem
theorem relation781_mem : "22,1,248,1;8,1,13,1,219,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block21[21]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation781_zero : nativeImage "22,1,248,1;8,1,13,1,219,1" = 0 := by
  change projection (relationPolynomial "22,1,248,1;8,1,13,1,219,1") = 0
  exact csv_relation_zero _ relation781_mem
theorem relation782_mem : "17,1,277,1;13,1,315,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block23[12]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation782_zero : nativeImage "17,1,277,1;13,1,315,1" = 0 := by
  change projection (relationPolynomial "17,1,277,1;13,1,315,1") = 0
  exact csv_relation_zero _ relation782_mem
theorem relation783_mem : "13,1,315,1;9,1,345,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block23[13]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation783_zero : nativeImage "13,1,315,1;9,1,345,1" = 0 := by
  change projection (relationPolynomial "13,1,315,1;9,1,345,1") = 0
  exact csv_relation_zero _ relation783_mem
theorem relation784_mem : "9,1,345,1;8,2,247,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block23[14]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation784_zero : nativeImage "9,1,345,1;8,2,247,1" = 0 := by
  change projection (relationPolynomial "9,1,345,1;8,2,247,1") = 0
  exact csv_relation_zero _ relation784_mem
theorem relation785_mem : "17,2,149,1;8,2,245,1;0,2,64,1,137,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block23[26]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation785_zero : nativeImage "17,2,149,1;8,2,245,1;0,2,64,1,137,1" = 0 := by
  change projection (relationPolynomial "17,2,149,1;8,2,245,1;0,2,64,1,137,1") = 0
  exact csv_relation_zero _ relation785_mem
theorem relation786_mem : "9,1,367,1;8,1,415,1;0,1,2,1,544,1;0,2,7,1,414,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block28[9]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation786_zero : nativeImage "9,1,367,1;8,1,415,1;0,1,2,1,544,1;0,2,7,1,414,1" = 0 := by
  change projection (relationPolynomial "9,1,367,1;8,1,415,1;0,1,2,1,544,1;0,2,7,1,414,1") = 0
  exact csv_relation_zero _ relation786_mem
theorem relation787_mem : "13,1,333,1;9,1,366,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block28[17]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation787_zero : nativeImage "13,1,333,1;9,1,366,1" = 0 := by
  change projection (relationPolynomial "13,1,333,1;9,1,366,1") = 0
  exact csv_relation_zero _ relation787_mem
theorem relation788_mem : "9,1,366,1;8,1,414,1" ∈ LinE2.RawData.relations := by
  exact relation_member 15 chunkBound rows transcription
    (block28[18]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation788_zero : nativeImage "9,1,366,1;8,1,414,1" = 0 := by
  change projection (relationPolynomial "9,1,366,1;8,1,414,1") = 0
  exact csv_relation_zero _ relation788_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk015
