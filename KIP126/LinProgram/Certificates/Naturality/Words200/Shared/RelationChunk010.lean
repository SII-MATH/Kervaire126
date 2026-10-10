import KIP126.LinProgram.Certificates.Naturality.Words200.Support

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk010
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[10]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 10 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[10]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block0_mem : block0 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 0) (by decide)
private theorem block0_in_rows (r : List Char) (hr : r ∈ block0) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block0, block0_mem, hr⟩
private theorem block1_mem : block1 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 1) (by decide)
private theorem block1_in_rows (r : List Char) (hr : r ∈ block1) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block1, block1_mem, hr⟩
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
private theorem block8_mem : block8 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 8) (by decide)
private theorem block8_in_rows (r : List Char) (hr : r ∈ block8) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block8, block8_mem, hr⟩
private theorem block14_mem : block14 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 14) (by decide)
private theorem block14_in_rows (r : List Char) (hr : r ∈ block14) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block14, block14_mem, hr⟩
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
private theorem block24_mem : block24 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 24) (by decide)
private theorem block24_in_rows (r : List Char) (hr : r ∈ block24) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block24, block24_mem, hr⟩
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block28_mem : block28 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 28) (by decide)
private theorem block28_in_rows (r : List Char) (hr : r ∈ block28) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block28, block28_mem, hr⟩
private theorem block29_mem : block29 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 29) (by decide)
private theorem block29_in_rows (r : List Char) (hr : r ∈ block29) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block29, block29_mem, hr⟩
theorem relation522_mem : "80,2;23,1,187,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block0[1]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation522_zero : nativeImage "80,2;23,1,187,1" = 0 := by
  change projection (relationPolynomial "80,2;23,1,187,1") = 0
  exact csv_relation_zero _ relation522_mem
theorem relation523_mem : "23,1,187,1;22,1,188,1;0,1,421,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block0[6]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation523_zero : nativeImage "23,1,187,1;22,1,188,1;0,1,421,1" = 0 := by
  change projection (relationPolynomial "23,1,187,1;22,1,188,1;0,1,421,1") = 0
  exact csv_relation_zero _ relation523_mem
theorem relation524_mem : "0,1,421,1;0,1,17,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block0[7]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation524_zero : nativeImage "0,1,421,1;0,1,17,1,209,1" = 0 := by
  change projection (relationPolynomial "0,1,421,1;0,1,17,1,209,1") = 0
  exact csv_relation_zero _ relation524_mem
theorem relation525_mem : "17,1,212,1;12,1,243,1;9,1,255,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block0[18]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation525_zero : nativeImage "17,1,212,1;12,1,243,1;9,1,255,1" = 0 := by
  change projection (relationPolynomial "17,1,212,1;12,1,243,1;9,1,255,1") = 0
  exact csv_relation_zero _ relation525_mem
theorem relation526_mem : "9,1,255,1;8,2,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block0[19]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation526_zero : nativeImage "9,1,255,1;8,2,188,1" = 0 := by
  change projection (relationPolynomial "9,1,255,1;8,2,188,1") = 0
  exact csv_relation_zero _ relation526_mem
theorem relation527_mem : "12,1,243,1;6,1,279,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block0[21]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation527_zero : nativeImage "12,1,243,1;6,1,279,1" = 0 := by
  change projection (relationPolynomial "12,1,243,1;6,1,279,1") = 0
  exact csv_relation_zero _ relation527_mem
theorem relation528_mem : "6,1,279,1;3,1,334,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block0[22]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation528_zero : nativeImage "6,1,279,1;3,1,334,1" = 0 := by
  change projection (relationPolynomial "6,1,279,1;3,1,334,1") = 0
  exact csv_relation_zero _ relation528_mem
theorem relation529_mem : "3,1,334,1;2,1,382,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block0[23]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation529_zero : nativeImage "3,1,334,1;2,1,382,1" = 0 := by
  change projection (relationPolynomial "3,1,334,1;2,1,382,1") = 0
  exact csv_relation_zero _ relation529_mem
theorem relation530_mem : "2,1,382,1;1,2,383,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block0[24]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation530_zero : nativeImage "2,1,382,1;1,2,383,1" = 0 := by
  change projection (relationPolynomial "2,1,382,1;1,2,383,1") = 0
  exact csv_relation_zero _ relation530_mem
theorem relation531_mem : "1,2,383,1;0,1,16,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block0[25]'(by decide)) (block0_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation531_zero : nativeImage "1,2,383,1;0,1,16,1,209,1" = 0 := by
  change projection (relationPolynomial "1,2,383,1;0,1,16,1,209,1") = 0
  exact csv_relation_zero _ relation531_mem
theorem relation532_mem : "23,1,186,1;9,1,13,2,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block1[24]'(by decide)) (block1_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation532_zero : nativeImage "23,1,186,1;9,1,13,2,80,1" = 0 := by
  change projection (relationPolynomial "23,1,186,1;9,1,13,2,80,1") = 0
  exact csv_relation_zero _ relation532_mem
theorem relation533_mem : "0,1,8,1,257,1;0,12,300,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block4[29]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation533_zero : nativeImage "0,1,8,1,257,1;0,12,300,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,257,1;0,12,300,1") = 0
  exact csv_relation_zero _ relation533_mem
theorem relation534_mem : "13,1,237,1;8,2,184,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block5[8]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation534_zero : nativeImage "13,1,237,1;8,2,184,1" = 0 := by
  change projection (relationPolynomial "13,1,237,1;8,2,184,1") = 0
  exact csv_relation_zero _ relation534_mem
theorem relation535_mem : "17,1,211,1;17,1,210,1;8,4,71,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block5[28]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation535_zero : nativeImage "17,1,211,1;17,1,210,1;8,4,71,1" = 0 := by
  change projection (relationPolynomial "17,1,211,1;17,1,210,1;8,4,71,1") = 0
  exact csv_relation_zero _ relation535_mem
theorem relation536_mem : "17,1,210,1;0,3,403,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block5[29]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation536_zero : nativeImage "17,1,210,1;0,3,403,1" = 0 := by
  change projection (relationPolynomial "17,1,210,1;0,3,403,1") = 0
  exact csv_relation_zero _ relation536_mem
theorem relation537_mem : "17,2,111,1;8,1,265,1;0,3,402,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block6[8]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation537_zero : nativeImage "17,2,111,1;8,1,265,1;0,3,402,1" = 0 := by
  change projection (relationPolynomial "17,2,111,1;8,1,265,1;0,3,402,1") = 0
  exact csv_relation_zero _ relation537_mem
theorem relation538_mem : "69,1,101,1;18,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block8[6]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation538_zero : nativeImage "69,1,101,1;18,1,209,1" = 0 := by
  change projection (relationPolynomial "69,1,101,1;18,1,209,1") = 0
  exact csv_relation_zero _ relation538_mem
theorem relation539_mem : "7,2,209,1;4,1,322,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block8[20]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation539_zero : nativeImage "7,2,209,1;4,1,322,1" = 0 := by
  change projection (relationPolynomial "7,2,209,1;4,1,322,1") = 0
  exact csv_relation_zero _ relation539_mem
theorem relation540_mem : "4,1,322,1;3,1,351,1;2,1,409,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block8[24]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation540_zero : nativeImage "4,1,322,1;3,1,351,1;2,1,409,1" = 0 := by
  change projection (relationPolynomial "4,1,322,1;3,1,351,1;2,1,409,1") = 0
  exact csv_relation_zero _ relation540_mem
theorem relation541_mem : "3,1,351,1;2,1,409,1;1,1,427,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block8[25]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation541_zero : nativeImage "3,1,351,1;2,1,409,1;1,1,427,1" = 0 := by
  change projection (relationPolynomial "3,1,351,1;2,1,409,1;1,1,427,1") = 0
  exact csv_relation_zero _ relation541_mem
theorem relation542_mem : "0,1,435,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block14[1]'(by decide)) (block14_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation542_zero : nativeImage "0,1,435,1" = 0 := by
  change projection (relationPolynomial "0,1,435,1") = 0
  exact csv_relation_zero _ relation542_mem
theorem relation543_mem : "75,1,95,1;18,1,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block18[12]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation543_zero : nativeImage "75,1,95,1;18,1,212,1" = 0 := by
  change projection (relationPolynomial "75,1,95,1;18,1,212,1") = 0
  exact csv_relation_zero _ relation543_mem
theorem relation544_mem : "18,1,212,1;13,1,251,1;0,3,428,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block18[17]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation544_zero : nativeImage "18,1,212,1;13,1,251,1;0,3,428,1" = 0 := by
  change projection (relationPolynomial "18,1,212,1;13,1,251,1;0,3,428,1") = 0
  exact csv_relation_zero _ relation544_mem
theorem relation545_mem : "2,1,417,1;1,1,3,1,335,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block19[5]'(by decide)) (block19_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation545_zero : nativeImage "2,1,417,1;1,1,3,1,335,1" = 0 := by
  change projection (relationPolynomial "2,1,417,1;1,1,3,1,335,1") = 0
  exact csv_relation_zero _ relation545_mem
theorem relation546_mem : "20,1,209,1;17,1,221,1;8,1,280,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block20[30]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation546_zero : nativeImage "20,1,209,1;17,1,221,1;8,1,280,1" = 0 := by
  change projection (relationPolynomial "20,1,209,1;17,1,221,1;8,1,280,1") = 0
  exact csv_relation_zero _ relation546_mem
theorem relation547_mem : "17,1,221,1;1,1,437,1;0,2,438,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block21[1]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation547_zero : nativeImage "17,1,221,1;1,1,437,1;0,2,438,1" = 0 := by
  change projection (relationPolynomial "17,1,221,1;1,1,437,1;0,2,438,1") = 0
  exact csv_relation_zero _ relation547_mem
theorem relation548_mem : "1,1,437,1;0,2,438,1;0,4,418,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block21[2]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation548_zero : nativeImage "1,1,437,1;0,2,438,1;0,4,418,1" = 0 := by
  change projection (relationPolynomial "1,1,437,1;0,2,438,1;0,4,418,1") = 0
  exact csv_relation_zero _ relation548_mem
theorem relation549_mem : "24,1,194,1;13,2,150,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block23[3]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation549_zero : nativeImage "24,1,194,1;13,2,150,1" = 0 := by
  change projection (relationPolynomial "24,1,194,1;13,2,150,1") = 0
  exact csv_relation_zero _ relation549_mem
theorem relation550_mem : "32,1,167,1;23,1,194,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block23[13]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation550_zero : nativeImage "32,1,167,1;23,1,194,1" = 0 := by
  change projection (relationPolynomial "32,1,167,1;23,1,194,1") = 0
  exact csv_relation_zero _ relation550_mem
theorem relation551_mem : "23,1,194,1;13,1,248,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block23[14]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation551_zero : nativeImage "23,1,194,1;13,1,248,1" = 0 := by
  change projection (relationPolynomial "23,1,194,1;13,1,248,1") = 0
  exact csv_relation_zero _ relation551_mem
theorem relation552_mem : "9,1,260,1;8,1,278,1;5,1,300,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block23[17]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation552_zero : nativeImage "9,1,260,1;8,1,278,1;5,1,300,1" = 0 := by
  change projection (relationPolynomial "9,1,260,1;8,1,278,1;5,1,300,1") = 0
  exact csv_relation_zero _ relation552_mem
theorem relation553_mem : "22,1,194,1;8,1,13,1,167,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block23[30]'(by decide)) (block23_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation553_zero : nativeImage "22,1,194,1;8,1,13,1,167,1" = 0 := by
  change projection (relationPolynomial "22,1,194,1;8,1,13,1,167,1") = 0
  exact csv_relation_zero _ relation553_mem
theorem relation554_mem : "17,1,219,1;8,2,194,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block24[8]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation554_zero : nativeImage "17,1,219,1;8,2,194,1" = 0 := by
  change projection (relationPolynomial "17,1,219,1;8,2,194,1") = 0
  exact csv_relation_zero _ relation554_mem
theorem relation555_mem : "17,1,218,1;16,1,219,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block24[17]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation555_zero : nativeImage "17,1,218,1;16,1,219,1" = 0 := by
  change projection (relationPolynomial "17,1,218,1;16,1,219,1") = 0
  exact csv_relation_zero _ relation555_mem
theorem relation556_mem : "16,1,219,1;13,1,247,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block24[18]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation556_zero : nativeImage "16,1,219,1;13,1,247,1" = 0 := by
  change projection (relationPolynomial "16,1,219,1;13,1,247,1") = 0
  exact csv_relation_zero _ relation556_mem
theorem relation557_mem : "13,1,247,1;9,1,259,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block24[20]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation557_zero : nativeImage "13,1,247,1;9,1,259,1" = 0 := by
  change projection (relationPolynomial "13,1,247,1;9,1,259,1") = 0
  exact csv_relation_zero _ relation557_mem
theorem relation558_mem : "9,1,259,1;8,2,193,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block24[21]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation558_zero : nativeImage "9,1,259,1;8,2,193,1" = 0 := by
  change projection (relationPolynomial "9,1,259,1;8,2,193,1") = 0
  exact csv_relation_zero _ relation558_mem
theorem relation559_mem : "16,1,218,1;13,1,245,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block24[26]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation559_zero : nativeImage "16,1,218,1;13,1,245,1" = 0 := by
  change projection (relationPolynomial "16,1,218,1;13,1,245,1") = 0
  exact csv_relation_zero _ relation559_mem
theorem relation560_mem : "13,1,245,1;9,1,258,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block24[27]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation560_zero : nativeImage "13,1,245,1;9,1,258,1" = 0 := by
  change projection (relationPolynomial "13,1,245,1;9,1,258,1") = 0
  exact csv_relation_zero _ relation560_mem
theorem relation561_mem : "9,1,258,1;8,1,277,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block24[28]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation561_zero : nativeImage "9,1,258,1;8,1,277,1" = 0 := by
  change projection (relationPolynomial "9,1,258,1;8,1,277,1") = 0
  exact csv_relation_zero _ relation561_mem
theorem relation562_mem : "39,1,160,1;31,1,166,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block25[9]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation562_zero : nativeImage "39,1,160,1;31,1,166,1" = 0 := by
  change projection (relationPolynomial "39,1,160,1;31,1,166,1") = 0
  exact csv_relation_zero _ relation562_mem
theorem relation563_mem : "31,1,166,1;19,1,206,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block25[12]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation563_zero : nativeImage "31,1,166,1;19,1,206,1" = 0 := by
  change projection (relationPolynomial "31,1,166,1;19,1,206,1") = 0
  exact csv_relation_zero _ relation563_mem
theorem relation564_mem : "19,1,206,1;13,1,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block25[13]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation564_zero : nativeImage "19,1,206,1;13,1,244,1" = 0 := by
  change projection (relationPolynomial "19,1,206,1;13,1,244,1") = 0
  exact csv_relation_zero _ relation564_mem
theorem relation565_mem : "13,1,244,1;9,1,257,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block25[14]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation565_zero : nativeImage "13,1,244,1;9,1,257,1" = 0 := by
  change projection (relationPolynomial "13,1,244,1;9,1,257,1") = 0
  exact csv_relation_zero _ relation565_mem
theorem relation566_mem : "9,1,257,1;8,1,16,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block25[15]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation566_zero : nativeImage "9,1,257,1;8,1,16,1,149,1" = 0 := by
  change projection (relationPolynomial "9,1,257,1;8,1,16,1,149,1") = 0
  exact csv_relation_zero _ relation566_mem
theorem relation567_mem : "69,1,109,1;3,1,377,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block28[7]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation567_zero : nativeImage "69,1,109,1;3,1,377,1" = 0 := by
  change projection (relationPolynomial "69,1,109,1;3,1,377,1") = 0
  exact csv_relation_zero _ relation567_mem
theorem relation568_mem : "1,1,451,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block28[17]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation568_zero : nativeImage "1,1,451,1" = 0 := by
  change projection (relationPolynomial "1,1,451,1") = 0
  exact csv_relation_zero _ relation568_mem
theorem relation569_mem : "0,1,69,1,107,1;0,1,3,1,367,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block28[29]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation569_zero : nativeImage "0,1,69,1,107,1;0,1,3,1,367,1" = 0 := by
  change projection (relationPolynomial "0,1,69,1,107,1;0,1,3,1,367,1") = 0
  exact csv_relation_zero _ relation569_mem
theorem relation570_mem : "0,1,3,1,367,1;0,2,451,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block28[30]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation570_zero : nativeImage "0,1,3,1,367,1;0,2,451,1" = 0 := by
  change projection (relationPolynomial "0,1,3,1,367,1;0,2,451,1") = 0
  exact csv_relation_zero _ relation570_mem
theorem relation571_mem : "2,2,373,1;1,1,450,1" ∈ LinE2.RawData.relations := by
  exact relation_member 10 chunkBound rows transcription
    (block29[6]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation571_zero : nativeImage "2,2,373,1;1,1,450,1" = 0 := by
  change projection (relationPolynomial "2,2,373,1;1,1,450,1") = 0
  exact csv_relation_zero _ relation571_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk010
