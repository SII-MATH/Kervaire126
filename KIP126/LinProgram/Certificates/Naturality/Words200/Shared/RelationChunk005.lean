import KIP126.LinProgram.Certificates.Naturality.Words200.Support

/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.RelationChunk005
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
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 0 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block1 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 32 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block2 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 64 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block3 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 96 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block4 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 128 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block5 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 160 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block6 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 192 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block7 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 224 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block8 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 256 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block9 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 288 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block10 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 320 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block11 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 352 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block12 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 384 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block13 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 416 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block14 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 448 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block15 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 480 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block16 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 512 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block17 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 544 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block18 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 576 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block19 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 608 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block20 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 640 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block21 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 672 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block22 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 704 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block23 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 736 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block24 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 768 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block25 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 800 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block26 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 832 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block27 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 864 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block28 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 896 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block29 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 928 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block30 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 960 |>.take 32 |>.map String.toList))
    replaceMainGoal []
open Lean Elab Tactic in
private def block31 : List (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.relationChunks[5]!).splitOn "\n" |>.drop 992 |>.take 32 |>.map String.toList))
    replaceMainGoal []
private def blocks : List (List (List Char)) := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31]
private def rows : List (List Char) := blocks.flatten
private theorem chunkBound : 5 < LinE2.RawData.relationChunks.size := by decide
private theorem transcription : LinE2.RawData.relationChunks[5]'(chunkBound) =
    String.ofList (joinRows rows) := by rfl
private theorem block2_mem : block2 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 2) (by decide)
private theorem block2_in_rows (r : List Char) (hr : r ∈ block2) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block2, block2_mem, hr⟩
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
private theorem block13_mem : block13 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 13) (by decide)
private theorem block13_in_rows (r : List Char) (hr : r ∈ block13) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block13, block13_mem, hr⟩
private theorem block15_mem : block15 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 15) (by decide)
private theorem block15_in_rows (r : List Char) (hr : r ∈ block15) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block15, block15_mem, hr⟩
private theorem block17_mem : block17 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 17) (by decide)
private theorem block17_in_rows (r : List Char) (hr : r ∈ block17) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block17, block17_mem, hr⟩
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
private theorem block22_mem : block22 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 22) (by decide)
private theorem block22_in_rows (r : List Char) (hr : r ∈ block22) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block22, block22_mem, hr⟩
private theorem block24_mem : block24 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 24) (by decide)
private theorem block24_in_rows (r : List Char) (hr : r ∈ block24) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block24, block24_mem, hr⟩
private theorem block25_mem : block25 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 25) (by decide)
private theorem block25_in_rows (r : List Char) (hr : r ∈ block25) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block25, block25_mem, hr⟩
private theorem block26_mem : block26 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 26) (by decide)
private theorem block26_in_rows (r : List Char) (hr : r ∈ block26) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block26, block26_mem, hr⟩
private theorem block31_mem : block31 ∈ blocks := by
  exact List.getElem_mem (l := blocks) (n := 31) (by decide)
private theorem block31_in_rows (r : List Char) (hr : r ∈ block31) : r ∈ rows :=
  List.mem_flatten.mpr ⟨block31, block31_mem, hr⟩
theorem relation325_mem : "32,1,101,1;13,2,80,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block2[23]'(by decide)) (block2_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation325_zero : nativeImage "32,1,101,1;13,2,80,1" = 0 := by
  change projection (relationPolynomial "32,1,101,1;13,2,80,1") = 0
  exact csv_relation_zero _ relation325_mem
theorem relation326_mem : "42,1,80,1;8,1,13,1,101,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block3[1]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation326_zero : nativeImage "42,1,80,1;8,1,13,1,101,1" = 0 := by
  change projection (relationPolynomial "42,1,80,1;8,1,13,1,101,1") = 0
  exact csv_relation_zero _ relation326_mem
theorem relation327_mem : "23,1,118,1;8,1,173,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block3[8]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation327_zero : nativeImage "23,1,118,1;8,1,173,1" = 0 := by
  change projection (relationPolynomial "23,1,118,1;8,1,173,1") = 0
  exact csv_relation_zero _ relation327_mem
theorem relation328_mem : "8,1,172,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block3[9]'(by decide)) (block3_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation328_zero : nativeImage "8,1,172,1" = 0 := by
  change projection (relationPolynomial "8,1,172,1") = 0
  exact csv_relation_zero _ relation328_mem
theorem relation329_mem : "0,1,8,1,166,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block4[4]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation329_zero : nativeImage "0,1,8,1,166,1" = 0 := by
  change projection (relationPolynomial "0,1,8,1,166,1") = 0
  exact csv_relation_zero _ relation329_mem
theorem relation330_mem : "17,1,137,1;16,1,138,1;0,1,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block4[28]'(by decide)) (block4_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation330_zero : nativeImage "17,1,137,1;16,1,138,1;0,1,244,1" = 0 := by
  change projection (relationPolynomial "17,1,137,1;16,1,138,1;0,1,244,1") = 0
  exact csv_relation_zero _ relation330_mem
theorem relation331_mem : "17,1,136,1;8,4,39,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block5[9]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation331_zero : nativeImage "17,1,136,1;8,4,39,1" = 0 := by
  change projection (relationPolynomial "17,1,136,1;8,4,39,1") = 0
  exact csv_relation_zero _ relation331_mem
theorem relation332_mem : "17,2,56,1;9,1,161,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block5[21]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation332_zero : nativeImage "17,2,56,1;9,1,161,1" = 0 := by
  change projection (relationPolynomial "17,2,56,1;9,1,161,1") = 0
  exact csv_relation_zero _ relation332_mem
theorem relation333_mem : "9,1,161,1;8,1,171,1;0,3,237,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block5[23]'(by decide)) (block5_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation333_zero : nativeImage "9,1,161,1;8,1,171,1;0,3,237,1" = 0 := by
  change projection (relationPolynomial "9,1,161,1;8,1,171,1;0,3,237,1") = 0
  exact csv_relation_zero _ relation333_mem
theorem relation334_mem : "7,1,191,1;3,1,222,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block6[9]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation334_zero : nativeImage "7,1,191,1;3,1,222,1" = 0 := by
  change projection (relationPolynomial "7,1,191,1;3,1,222,1") = 0
  exact csv_relation_zero _ relation334_mem
theorem relation335_mem : "52,1,69,1;7,1,190,1;3,2,191,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block6[11]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation335_zero : nativeImage "52,1,69,1;7,1,190,1;3,2,191,1" = 0 := by
  change projection (relationPolynomial "52,1,69,1;7,1,190,1;3,2,191,1") = 0
  exact csv_relation_zero _ relation335_mem
theorem relation336_mem : "2,1,239,1;1,1,251,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block6[17]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation336_zero : nativeImage "2,1,239,1;1,1,251,1" = 0 := by
  change projection (relationPolynomial "2,1,239,1;1,1,251,1") = 0
  exact csv_relation_zero _ relation336_mem
theorem relation337_mem : "8,1,23,1,69,1;3,1,221,1;1,2,239,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block6[28]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation337_zero : nativeImage "8,1,23,1,69,1;3,1,221,1;1,2,239,1" = 0 := by
  change projection (relationPolynomial "8,1,23,1,69,1;3,1,221,1;1,2,239,1") = 0
  exact csv_relation_zero _ relation337_mem
theorem relation338_mem : "3,1,221,1;0,2,251,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block6[29]'(by decide)) (block6_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation338_zero : nativeImage "3,1,221,1;0,2,251,1" = 0 := by
  change projection (relationPolynomial "3,1,221,1;0,2,251,1") = 0
  exact csv_relation_zero _ relation338_mem
theorem relation339_mem : "8,1,22,1,69,1;7,1,188,1;3,2,189,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block7[7]'(by decide)) (block7_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation339_zero : nativeImage "8,1,22,1,69,1;7,1,188,1;3,2,189,1" = 0 := by
  change projection (relationPolynomial "8,1,22,1,69,1;7,1,188,1;3,2,189,1") = 0
  exact csv_relation_zero _ relation339_mem
theorem relation340_mem : "0,2,250,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block8[1]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation340_zero : nativeImage "0,2,250,1" = 0 := by
  change projection (relationPolynomial "0,2,250,1") = 0
  exact csv_relation_zero _ relation340_mem
theorem relation341_mem : "32,1,107,1;9,1,13,1,95,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block8[16]'(by decide)) (block8_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation341_zero : nativeImage "32,1,107,1;9,1,13,1,95,1" = 0 := by
  change projection (relationPolynomial "32,1,107,1;9,1,13,1,95,1") = 0
  exact csv_relation_zero _ relation341_mem
theorem relation342_mem : "32,1,105,1;13,2,83,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block9[1]'(by decide)) (block9_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation342_zero : nativeImage "32,1,105,1;13,2,83,1" = 0 := by
  change projection (relationPolynomial "32,1,105,1;13,2,83,1") = 0
  exact csv_relation_zero _ relation342_mem
theorem relation343_mem : "53,1,67,1;0,1,3,2,188,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block13[13]'(by decide)) (block13_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation343_zero : nativeImage "53,1,67,1;0,1,3,2,188,1" = 0 := by
  change projection (relationPolynomial "53,1,67,1;0,1,3,2,188,1") = 0
  exact csv_relation_zero _ relation343_mem
theorem relation344_mem : "0,2,8,3,64,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block15[12]'(by decide)) (block15_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation344_zero : nativeImage "0,2,8,3,64,1" = 0 := by
  change projection (relationPolynomial "0,2,8,3,64,1") = 0
  exact csv_relation_zero _ relation344_mem
theorem relation345_mem : "43,1,94,1;7,1,198,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block17[1]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation345_zero : nativeImage "43,1,94,1;7,1,198,1" = 0 := by
  change projection (relationPolynomial "43,1,94,1;7,1,198,1") = 0
  exact csv_relation_zero _ relation345_mem
theorem relation346_mem : "7,1,198,1;3,1,230,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block17[2]'(by decide)) (block17_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation346_zero : nativeImage "7,1,198,1;3,1,230,1" = 0 := by
  change projection (relationPolynomial "7,1,198,1;3,1,230,1") = 0
  exact csv_relation_zero _ relation346_mem
theorem relation347_mem : "0,1,261,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block18[30]'(by decide)) (block18_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation347_zero : nativeImage "0,1,261,1" = 0 := by
  change projection (relationPolynomial "0,1,261,1") = 0
  exact csv_relation_zero _ relation347_mem
theorem relation348_mem : "46,1,80,1;9,1,13,1,101,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block20[21]'(by decide)) (block20_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation348_zero : nativeImage "46,1,80,1;9,1,13,1,101,1" = 0 := by
  change projection (relationPolynomial "46,1,80,1;9,1,13,1,101,1") = 0
  exact csv_relation_zero _ relation348_mem
theorem relation349_mem : "42,1,89,1;23,1,127,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block21[6]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation349_zero : nativeImage "42,1,89,1;23,1,127,1" = 0 := by
  change projection (relationPolynomial "42,1,89,1;23,1,127,1") = 0
  exact csv_relation_zero _ relation349_mem
theorem relation350_mem : "23,1,127,1;9,1,173,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block21[12]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation350_zero : nativeImage "23,1,127,1;9,1,173,1" = 0 := by
  change projection (relationPolynomial "23,1,127,1;9,1,173,1") = 0
  exact csv_relation_zero _ relation350_mem
theorem relation351_mem : "9,1,173,1;8,1,186,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block21[14]'(by decide)) (block21_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation351_zero : nativeImage "9,1,173,1;8,1,186,1" = 0 := by
  change projection (relationPolynomial "9,1,173,1;8,1,186,1") = 0
  exact csv_relation_zero _ relation351_mem
theorem relation352_mem : "17,1,146,1;16,1,147,1;15,1,149,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block22[25]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation352_zero : nativeImage "17,1,146,1;16,1,147,1;15,1,149,1" = 0 := by
  change projection (relationPolynomial "17,1,146,1;16,1,147,1;15,1,149,1") = 0
  exact csv_relation_zero _ relation352_mem
theorem relation353_mem : "16,1,147,1;8,1,185,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block22[26]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation353_zero : nativeImage "16,1,147,1;8,1,185,1" = 0 := by
  change projection (relationPolynomial "16,1,147,1;8,1,185,1") = 0
  exact csv_relation_zero _ relation353_mem
theorem relation354_mem : "15,1,149,1;2,1,244,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block22[27]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation354_zero : nativeImage "15,1,149,1;2,1,244,1" = 0 := by
  change projection (relationPolynomial "15,1,149,1;2,1,244,1") = 0
  exact csv_relation_zero _ relation354_mem
theorem relation355_mem : "2,1,244,1;0,1,257,1;0,4,246,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block22[28]'(by decide)) (block22_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation355_zero : nativeImage "2,1,244,1;0,1,257,1;0,4,246,1" = 0 := by
  change projection (relationPolynomial "2,1,244,1;0,1,257,1;0,4,246,1") = 0
  exact csv_relation_zero _ relation355_mem
theorem relation356_mem : "17,1,145,1;8,1,183,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block24[12]'(by decide)) (block24_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation356_zero : nativeImage "17,1,145,1;8,1,183,1" = 0 := by
  change projection (relationPolynomial "17,1,145,1;8,1,183,1") = 0
  exact csv_relation_zero _ relation356_mem
theorem relation357_mem : "0,1,269,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block25[17]'(by decide)) (block25_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation357_zero : nativeImage "0,1,269,1" = 0 := by
  change projection (relationPolynomial "0,1,269,1") = 0
  exact csv_relation_zero _ relation357_mem
theorem relation358_mem : "8,2,9,1,69,1;7,1,201,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block26[2]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation358_zero : nativeImage "8,2,9,1,69,1;7,1,201,1" = 0 := by
  change projection (relationPolynomial "8,2,9,1,69,1;7,1,201,1") = 0
  exact csv_relation_zero _ relation358_mem
theorem relation359_mem : "7,1,201,1;1,1,261,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block26[4]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation359_zero : nativeImage "7,1,201,1;1,1,261,1" = 0 := by
  change projection (relationPolynomial "7,1,201,1;1,1,261,1") = 0
  exact csv_relation_zero _ relation359_mem
theorem relation360_mem : "23,1,134,1;13,1,164,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block26[13]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation360_zero : nativeImage "23,1,134,1;13,1,164,1" = 0 := by
  change projection (relationPolynomial "23,1,134,1;13,1,164,1") = 0
  exact csv_relation_zero _ relation360_mem
theorem relation361_mem : "23,1,133,1;13,2,95,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block26[26]'(by decide)) (block26_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation361_zero : nativeImage "23,1,133,1;13,2,95,1" = 0 := by
  change projection (relationPolynomial "23,1,133,1;13,2,95,1") = 0
  exact csv_relation_zero _ relation361_mem
theorem relation362_mem : "3,1,239,1;1,1,270,1" ∈ LinE2.RawData.relations := by
  exact relation_member 5 chunkBound rows transcription
    (block31[7]'(by decide)) (block31_in_rows _ (List.getElem_mem _)) (by decide +kernel)
theorem relation362_zero : nativeImage "3,1,239,1;1,1,270,1" = 0 := by
  change projection (relationPolynomial "3,1,239,1;1,1,270,1") = 0
  exact csv_relation_zero _ relation362_mem
end KIP126.LinModule.NaturalityWords200.Shared.RelationChunk005
