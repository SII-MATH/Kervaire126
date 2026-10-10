import KIP126.LinProgram.Certificates.Naturality.Words200.Support

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk006
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[6]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 6 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[6]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
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
private theorem block10_mem : block10 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 10) (by decide)
private theorem block10_in_rows (r : List Char) (hr : r ∈ block10) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block10, block10_mem, hr⟩
private theorem block11_mem : block11 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 11) (by decide)
private theorem block11_in_rows (r : List Char) (hr : r ∈ block11) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block11, block11_mem, hr⟩
private theorem block13_mem : block13 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 13) (by decide)
private theorem block13_in_rows (r : List Char) (hr : r ∈ block13) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block13, block13_mem, hr⟩
private theorem block18_mem : block18 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 18) (by decide)
private theorem block18_in_rows (r : List Char) (hr : r ∈ block18) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block18, block18_mem, hr⟩
private theorem block20_mem : block20 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 20) (by decide)
private theorem block20_in_rows (r : List Char) (hr : r ∈ block20) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block20, block20_mem, hr⟩
private theorem block21_mem : block21 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 21) (by decide)
private theorem block21_in_rows (r : List Char) (hr : r ∈ block21) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block21, block21_mem, hr⟩
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block26_mem : block26 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 26) (by decide)
private theorem block26_in_rows (r : List Char) (hr : r ∈ block26) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block26, block26_mem, hr⟩
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
theorem relation363_mem : "0,1,280,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block5[11]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation363_zero : nativeImage "0,1,280,1" = 0 := by
  change projection (relationPolynomial "0,1,280,1") = 0
  exact csv_relation_zero _ relation363_mem
theorem relation364_mem : "0,1,279,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block5[22]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation364_zero : nativeImage "0,1,279,1" = 0 := by
  change projection (relationPolynomial "0,1,279,1") = 0
  exact csv_relation_zero _ relation364_mem
theorem relation365_mem : "9,1,187,1;8,1,201,1;1,1,5,1,209,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block5[28]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation365_zero : nativeImage "9,1,187,1;8,1,201,1;1,1,5,1,209,1" = 0 := by
  change projection (relationPolynomial "9,1,187,1;8,1,201,1;1,1,5,1,209,1") = 0
  exact csv_relation_zero _ relation365_mem
theorem relation366_mem : "51,1,80,1;13,2,101,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block6[4]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation366_zero : nativeImage "51,1,80,1;13,2,101,1" = 0 := by
  change projection (relationPolynomial "51,1,80,1;13,2,101,1") = 0
  exact csv_relation_zero _ relation366_mem
theorem relation367_mem : "42,1,101,1;13,1,173,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block6[15]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation367_zero : nativeImage "42,1,101,1;13,1,173,1" = 0 := by
  change projection (relationPolynomial "42,1,101,1;13,1,173,1") = 0
  exact csv_relation_zero _ relation367_mem
theorem relation368_mem : "13,1,173,1;9,1,186,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block6[19]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation368_zero : nativeImage "13,1,173,1;9,1,186,1" = 0 := by
  change projection (relationPolynomial "13,1,173,1;9,1,186,1") = 0
  exact csv_relation_zero _ relation368_mem
theorem relation369_mem : "9,1,186,1;8,1,23,1,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block6[20]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation369_zero : nativeImage "9,1,186,1;8,1,23,1,80,1" = 0 := by
  change projection (relationPolynomial "9,1,186,1;8,1,23,1,80,1") = 0
  exact csv_relation_zero _ relation369_mem
theorem relation370_mem : "17,2,64,1;16,1,154,1;0,1,17,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block7[31]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation370_zero : nativeImage "17,2,64,1;16,1,154,1;0,1,17,1,149,1" = 0 := by
  change projection (relationPolynomial "17,2,64,1;16,1,154,1;0,1,17,1,149,1") = 0
  exact csv_relation_zero _ relation370_mem
theorem relation371_mem : "16,1,17,1,64,1;15,1,160,1;9,1,185,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block8[15]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation371_zero : nativeImage "16,1,17,1,64,1;15,1,160,1;9,1,185,1" = 0 := by
  change projection (relationPolynomial "16,1,17,1,64,1;15,1,160,1;9,1,185,1") = 0
  exact csv_relation_zero _ relation371_mem
theorem relation372_mem : "9,1,185,1;8,2,138,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block8[16]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation372_zero : nativeImage "9,1,185,1;8,2,138,1" = 0 := by
  change projection (relationPolynomial "9,1,185,1;8,2,138,1") = 0
  exact csv_relation_zero _ relation372_mem
theorem relation373_mem : "15,1,160,1;6,1,206,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block8[17]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation373_zero : nativeImage "15,1,160,1;6,1,206,1" = 0 := by
  change projection (relationPolynomial "15,1,160,1;6,1,206,1") = 0
  exact csv_relation_zero _ relation373_mem
theorem relation374_mem : "6,1,206,1;2,1,257,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block8[18]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation374_zero : nativeImage "6,1,206,1;2,1,257,1" = 0 := by
  change projection (relationPolynomial "6,1,206,1;2,1,257,1") = 0
  exact csv_relation_zero _ relation374_mem
theorem relation375_mem : "2,1,257,1;0,1,16,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block8[19]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation375_zero : nativeImage "2,1,257,1;0,1,16,1,149,1" = 0 := by
  change projection (relationPolynomial "2,1,257,1;0,1,16,1,149,1") = 0
  exact csv_relation_zero _ relation375_mem
theorem relation376_mem : "0,7,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block9[18]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation376_zero : nativeImage "0,7,244,1" = 0 := by
  change projection (relationPolynomial "0,7,244,1") = 0
  exact csv_relation_zero _ relation376_mem
theorem relation377_mem : "17,1,152,1;16,1,153,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block9[29]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation377_zero : nativeImage "17,1,152,1;16,1,153,1" = 0 := by
  change projection (relationPolynomial "17,1,152,1;16,1,153,1") = 0
  exact csv_relation_zero _ relation377_mem
theorem relation378_mem : "16,1,153,1;9,1,183,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block9[30]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation378_zero : nativeImage "16,1,153,1;9,1,183,1" = 0 := by
  change projection (relationPolynomial "16,1,153,1;9,1,183,1") = 0
  exact csv_relation_zero _ relation378_mem
theorem relation379_mem : "9,1,183,1;8,1,200,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block9[31]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation379_zero : nativeImage "9,1,183,1;8,1,200,1" = 0 := by
  change projection (relationPolynomial "9,1,183,1;8,1,200,1") = 0
  exact csv_relation_zero _ relation379_mem
theorem relation380_mem : "9,1,182,1;8,1,199,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block10[6]'(by decide)) (block10_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation380_zero : nativeImage "9,1,182,1;8,1,199,1" = 0 := by
  change projection (relationPolynomial "9,1,182,1;8,1,199,1") = 0
  exact csv_relation_zero _ relation380_mem
theorem relation381_mem : "2,1,271,1;1,1,282,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block11[5]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation381_zero : nativeImage "2,1,271,1;1,1,282,1" = 0 := by
  change projection (relationPolynomial "2,1,271,1;1,1,282,1") = 0
  exact csv_relation_zero _ relation381_mem
theorem relation382_mem : "2,2,251,1;1,1,281,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block11[18]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation382_zero : nativeImage "2,2,251,1;1,1,281,1" = 0 := by
  change projection (relationPolynomial "2,2,251,1;1,1,281,1") = 0
  exact csv_relation_zero _ relation382_mem
theorem relation383_mem : "3,2,213,1;1,2,270,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block11[19]'(by decide)) (block11_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation383_zero : nativeImage "3,2,213,1;1,2,270,1" = 0 := by
  change projection (relationPolynomial "3,2,213,1;1,2,270,1") = 0
  exact csv_relation_zero _ relation383_mem
theorem relation384_mem : "60,1,69,1;59,1,69,1;1,1,280,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block13[0]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation384_zero : nativeImage "60,1,69,1;59,1,69,1;1,1,280,1" = 0 := by
  change projection (relationPolynomial "60,1,69,1;59,1,69,1;1,1,280,1") = 0
  exact csv_relation_zero _ relation384_mem
theorem relation385_mem : "0,1,287,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block13[1]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation385_zero : nativeImage "0,1,287,1" = 0 := by
  change projection (relationPolynomial "0,1,287,1") = 0
  exact csv_relation_zero _ relation385_mem
theorem relation386_mem : "2,1,267,1;1,1,279,1;0,1,286,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block13[16]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation386_zero : nativeImage "2,1,267,1;1,1,279,1;0,1,286,1" = 0 := by
  change projection (relationPolynomial "2,1,267,1;1,1,279,1;0,1,286,1") = 0
  exact csv_relation_zero _ relation386_mem
theorem relation387_mem : "3,2,216,1;1,1,289,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block18[21]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation387_zero : nativeImage "3,2,216,1;1,1,289,1" = 0 := by
  change projection (relationPolynomial "3,2,216,1;1,1,289,1") = 0
  exact csv_relation_zero _ relation387_mem
theorem relation388_mem : "0,2,286,1;0,2,285,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block20[1]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation388_zero : nativeImage "0,2,286,1;0,2,285,1" = 0 := by
  change projection (relationPolynomial "0,2,286,1;0,2,285,1") = 0
  exact csv_relation_zero _ relation388_mem
theorem relation389_mem : "19,1,149,1;16,1,160,1;14,1,172,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block21[13]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation389_zero : nativeImage "19,1,149,1;16,1,160,1;14,1,172,1" = 0 := by
  change projection (relationPolynomial "19,1,149,1;16,1,160,1;14,1,172,1") = 0
  exact csv_relation_zero _ relation389_mem
theorem relation390_mem : "16,1,160,1;8,1,206,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block21[14]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation390_zero : nativeImage "16,1,160,1;8,1,206,1" = 0 := by
  change projection (relationPolynomial "16,1,160,1;8,1,206,1") = 0
  exact csv_relation_zero _ relation390_mem
theorem relation391_mem : "0,1,294,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block25[18]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation391_zero : nativeImage "0,1,294,1" = 0 := by
  change projection (relationPolynomial "0,1,294,1") = 0
  exact csv_relation_zero _ relation391_mem
theorem relation392_mem : "13,1,187,1;9,1,201,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block26[6]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation392_zero : nativeImage "13,1,187,1;9,1,201,1" = 0 := by
  change projection (relationPolynomial "13,1,187,1;9,1,201,1") = 0
  exact csv_relation_zero _ relation392_mem
theorem relation393_mem : "9,1,201,1;8,1,212,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block26[7]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation393_zero : nativeImage "9,1,201,1;8,1,212,1" = 0 := by
  change projection (relationPolynomial "9,1,201,1;8,1,212,1") = 0
  exact csv_relation_zero _ relation393_mem
theorem relation394_mem : "0,3,285,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block26[20]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation394_zero : nativeImage "0,3,285,1" = 0 := by
  change projection (relationPolynomial "0,3,285,1") = 0
  exact csv_relation_zero _ relation394_mem
theorem relation395_mem : "46,1,101,1;13,1,186,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block27[8]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation395_zero : nativeImage "46,1,101,1;13,1,186,1" = 0 := by
  change projection (relationPolynomial "46,1,101,1;13,1,186,1") = 0
  exact csv_relation_zero _ relation395_mem
theorem relation396_mem : "13,1,186,1;9,1,23,1,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block27[10]'(by decide)) (block27_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation396_zero : nativeImage "13,1,186,1;9,1,23,1,80,1" = 0 := by
  change projection (relationPolynomial "13,1,186,1;9,1,23,1,80,1") = 0
  exact csv_relation_zero _ relation396_mem
theorem relation397_mem : "42,1,113,1;8,3,89,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block28[8]'(by decide)) (block28_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation397_zero : nativeImage "42,1,113,1;8,3,89,1" = 0 := by
  change projection (relationPolynomial "42,1,113,1;8,3,89,1") = 0
  exact csv_relation_zero _ relation397_mem
theorem relation398_mem : "0,1,8,1,206,1;0,7,260,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block29[21]'(by decide)) (block29_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation398_zero : nativeImage "0,1,8,1,206,1;0,7,260,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,206,1;0,7,260,1") = 0
  exact csv_relation_zero _ relation398_mem
theorem relation399_mem : "13,1,184,1;8,2,146,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block30[0]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation399_zero : nativeImage "13,1,184,1;8,2,146,1" = 0 := by
  change projection (relationPolynomial "13,1,184,1;8,2,146,1") = 0
  exact csv_relation_zero _ relation399_mem
theorem relation400_mem : "17,1,161,1;8,4,49,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block30[18]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation400_zero : nativeImage "17,1,161,1;8,4,49,1" = 0 := by
  change projection (relationPolynomial "17,1,161,1;8,4,49,1") = 0
  exact csv_relation_zero _ relation400_mem
theorem relation401_mem : "60,1,71,1;49,1,88,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block30[20]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation401_zero : nativeImage "60,1,71,1;49,1,88,1" = 0 := by
  change projection (relationPolynomial "60,1,71,1;49,1,88,1") = 0
  exact csv_relation_zero _ relation401_mem
theorem relation402_mem : "49,1,88,1;42,1,110,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block30[21]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation402_zero : nativeImage "49,1,88,1;42,1,110,1" = 0 := by
  change projection (relationPolynomial "49,1,88,1;42,1,110,1") = 0
  exact csv_relation_zero _ relation402_mem
theorem relation403_mem : "42,1,110,1;31,1,125,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block30[22]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation403_zero : nativeImage "42,1,110,1;31,1,125,1" = 0 := by
  change projection (relationPolynomial "42,1,110,1;31,1,125,1") = 0
  exact csv_relation_zero _ relation403_mem
theorem relation404_mem : "31,1,125,1;16,1,161,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block30[24]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation404_zero : nativeImage "31,1,125,1;16,1,161,1" = 0 := by
  change projection (relationPolynomial "31,1,125,1;16,1,161,1") = 0
  exact csv_relation_zero _ relation404_mem
theorem relation405_mem : "16,1,161,1;8,1,211,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block30[25]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation405_zero : nativeImage "16,1,161,1;8,1,211,1" = 0 := by
  change projection (relationPolynomial "16,1,161,1;8,1,211,1") = 0
  exact csv_relation_zero _ relation405_mem
theorem relation406_mem : "8,1,210,1" ∈ LinE2.RawData.relations := by
  exact relation_member 6 chunkBound rows transcription
    (block30[26]'(by decide)) (block30_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation406_zero : nativeImage "8,1,210,1" = 0 := by
  change projection (relationPolynomial "8,1,210,1") = 0
  exact csv_relation_zero _ relation406_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk006
