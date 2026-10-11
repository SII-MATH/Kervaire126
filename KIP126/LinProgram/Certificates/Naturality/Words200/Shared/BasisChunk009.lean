module

import all Init.Data.List.SplitOn.Basic
public import KIP126.LinProgram.Certificates.Naturality.Words200.CatalogueSupport

@[expose] public section


/-! Generated finite kernel certificates. Reproduce with
`python3 KIP126/LinProgram/Translate/generate-naturality-word-proofs.py`.
These are native quotient equations and original target catalogue memberships,
not actual-map comparisons or mathematical basis certification. -/
namespace KIP126.LinModule.NaturalityWords200.Shared.BasisChunk009
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
private def rows : Array (List Char) := by
  run_tac
    (← getMainGoal).assign (toExpr ((LinE2.RawData.basisChunks[9]!).splitOn "\n" |>.map String.toList |>.toArray))
    replaceMainGoal []
private theorem chunkBound : 9 < LinE2.RawData.basisChunks.size := by decide
private theorem transcription : LinE2.RawData.basisChunks[9]'chunkBound =
    String.ofList (joinRows rows.toList) := by rfl
private def bindings0 : List (Nat × BasisRow) := [(0, ⟨23, 197, 0, "9,1,80,1,209,1"⟩),
  (1, ⟨23, 197, 1, "0,1,68,1,359,1"⟩),
  (2, ⟨23, 197, 2, "0,9,59,1,324,1"⟩),
  (3, ⟨22, 197, 0, "0,1,18,1,690,1"⟩),
  (4, ⟨22, 197, 1, "0,1,3,1,982,1"⟩),
  (5, ⟨21, 197, 0, "1124,1"⟩),
  (7, ⟨21, 197, 2, "0,1,1108,1"⟩),
  (8, ⟨21, 197, 3, "0,1,3,1,984,1"⟩),
  (9, ⟨20, 197, 0, "1125,1"⟩),
  (10, ⟨20, 197, 1, "78,1,324,1"⟩),
  (11, ⟨20, 197, 2, "0,1,67,1,363,1"⟩),
  (13, ⟨19, 197, 1, "1,1,1096,1"⟩),
  (14, ⟨19, 197, 2, "0,5,1055,1"⟩),
  (16, ⟨18, 197, 1, "75,1,335,1"⟩),
  (17, ⟨18, 197, 2, "2,2,1004,1"⟩),
  (18, ⟨18, 197, 3, "0,3,1088,1"⟩),
  (19, ⟨18, 197, 4, "0,5,1057,1"⟩),
  (24, ⟨17, 197, 4, "0,1,1113,1"⟩),
  (25, ⟨17, 197, 5, "0,6,64,1,324,1"⟩),
  (27, ⟨16, 197, 1, "67,1,373,1"⟩),
  (28, ⟨16, 197, 2, "8,2,20,1,324,1"⟩),
  (29, ⟨16, 197, 3, "0,1,43,1,543,1"⟩),
  (30, ⟨16, 197, 4, "0,2,1098,1"⟩),
  (31, ⟨16, 197, 5, "0,5,66,1,324,1"⟩),
  (34, ⟨15, 197, 2, "67,1,376,1"⟩),
  (35, ⟨15, 197, 3, "8,1,45,1,324,1"⟩),
  (36, ⟨15, 197, 4, "0,1,43,1,544,1"⟩),
  (37, ⟨15, 197, 5, "0,1,2,1,1057,1"⟩),
  (38, ⟨15, 197, 6, "0,2,1099,1"⟩),
  (39, ⟨14, 197, 0, "1134,1"⟩),
  (40, ⟨14, 197, 1, "1133,1"⟩),
  (41, ⟨14, 197, 2, "1132,1"⟩)]
private def bindings1 : List (Nat × BasisRow) := [(42, ⟨14, 197, 3, "8,1,46,1,324,1"⟩),
  (43, ⟨14, 197, 4, "1,1,1100,1"⟩),
  (44, ⟨14, 197, 5, "0,3,72,1,324,1"⟩),
  (45, ⟨13, 197, 0, "1135,1"⟩),
  (46, ⟨13, 197, 1, "9,1,13,2,324,1"⟩),
  (47, ⟨13, 197, 2, "0,1,1118,1"⟩),
  (48, ⟨12, 197, 0, "1136,1"⟩),
  (49, ⟨12, 197, 1, "0,1,1120,1"⟩),
  (50, ⟨11, 197, 0, "1138,1"⟩),
  (52, ⟨11, 197, 2, "79,1,324,1"⟩),
  (53, ⟨10, 197, 0, "80,1,324,1"⟩),
  (54, ⟨10, 197, 1, "1,1,18,1,684,1"⟩),
  (55, ⟨10, 197, 2, "0,2,73,1,324,1"⟩),
  (56, ⟨9, 197, 0, "0,2,74,1,324,1"⟩),
  (57, ⟨9, 197, 1, "0,5,1058,1"⟩),
  (59, ⟨8, 197, 1, "0,5,18,2,324,1"⟩),
  (60, ⟨7, 197, 0, "2,1,18,1,660,1"⟩),
  (61, ⟨7, 197, 1, "1,1,76,1,324,1"⟩),
  (62, ⟨6, 197, 0, "2,1,70,1,324,1"⟩),
  (63, ⟨6, 197, 1, "0,1,2,1,1058,1"⟩),
  (64, ⟨5, 197, 0, "0,1,2,1,18,2,324,1"⟩),
  (65, ⟨198, 198, 0, "0,198"⟩),
  (66, ⟨67, 198, 0, "0,2,1101,1"⟩),
  (68, ⟨63, 198, 0, "1140,1"⟩),
  (70, ⟨59, 198, 0, "8,1,16,1,554,1"⟩),
  (71, ⟨58, 198, 0, "8,1,17,1,554,1"⟩),
  (72, ⟨57, 198, 0, "8,1,886,1"⟩),
  (73, ⟨56, 198, 0, "8,4,295,1"⟩),
  (74, ⟨55, 198, 0, "8,4,296,1"⟩),
  (76, ⟨54, 198, 1, "8,2,16,1,17,1,183,1"⟩),
  (77, ⟨53, 198, 0, "1142,1"⟩),
  (78, ⟨53, 198, 1, "8,3,498,1"⟩)]
private def bindings2 : List (Nat × BasisRow) := [(79, ⟨52, 198, 0, "8,6,145,1"⟩),
  (80, ⟨51, 198, 0, "8,5,16,1,111,1"⟩),
  (81, ⟨51, 198, 1, "0,4,17,1,685,1"⟩),
  (83, ⟨50, 198, 1, "8,5,17,1,111,1"⟩),
  (84, ⟨50, 198, 2, "0,3,17,2,403,1"⟩),
  (85, ⟨49, 198, 0, "8,2,663,1"⟩),
  (86, ⟨49, 198, 1, "8,5,211,1"⟩),
  (87, ⟨49, 198, 2, "0,7,1033,1"⟩),
  (88, ⟨48, 198, 0, "8,1,17,1,556,1"⟩),
  (89, ⟨48, 198, 1, "8,8,49,1"⟩),
  (90, ⟨48, 198, 2, "0,5,1059,1"⟩),
  (91, ⟨47, 198, 0, "17,2,433,1"⟩),
  (92, ⟨47, 198, 1, "8,8,50,1"⟩),
  (93, ⟨46, 198, 0, "8,4,297,1"⟩),
  (94, ⟨46, 198, 1, "8,6,16,1,17,2"⟩),
  (95, ⟨45, 198, 0, "8,4,298,1"⟩),
  (96, ⟨45, 198, 1, "8,7,88,1"⟩),
  (98, ⟨44, 198, 1, "8,3,17,1,238,1"⟩),
  (99, ⟨44, 198, 2, "8,11"⟩),
  (100, ⟨43, 198, 0, "64,1,403,1"⟩),
  (101, ⟨43, 198, 1, "8,2,17,2,185,1"⟩),
  (102, ⟨43, 198, 2, "8,9,22,1"⟩),
  (103, ⟨43, 198, 3, "0,1,16,1,725,1"⟩),
  (104, ⟨42, 198, 0, "138,1,225,1"⟩),
  (105, ⟨42, 198, 1, "8,6,146,1"⟩),
  (106, ⟨42, 198, 2, "8,9,23,1"⟩),
  (107, ⟨42, 198, 3, "0,1,17,1,725,1"⟩),
  (108, ⟨41, 198, 0, "1144,1"⟩),
  (110, ⟨41, 198, 2, "8,6,147,1"⟩),
  (111, ⟨41, 198, 3, "8,8,51,1"⟩),
  (112, ⟨40, 198, 0, "8,1,16,1,64,1,137,1"⟩),
  (113, ⟨40, 198, 1, "8,5,17,1,113,1"⟩)]
private def bindings3 : List (Nat × BasisRow) := [(114, ⟨40, 198, 2, "8,7,13,3"⟩),
  (115, ⟨39, 198, 0, "8,1,16,1,64,1,138,1"⟩),
  (116, ⟨39, 198, 1, "8,4,17,1,162,1"⟩),
  (117, ⟨39, 198, 2, "8,6,13,2,32,1"⟩),
  (118, ⟨39, 198, 3, "0,1,8,3,491,1"⟩),
  (119, ⟨38, 198, 0, "8,2,664,1"⟩),
  (120, ⟨38, 198, 1, "8,5,13,3,23,1"⟩),
  (121, ⟨38, 198, 2, "8,7,89,1"⟩),
  (122, ⟨38, 198, 3, "0,1,8,1,16,1,17,1,260,1"⟩),
  (123, ⟨37, 198, 0, "8,2,665,1"⟩),
  (124, ⟨37, 198, 1, "8,4,13,3,51,1"⟩),
  (125, ⟨37, 198, 2, "8,6,9,1,80,1"⟩),
  (127, ⟨36, 198, 0, "8,3,13,6"⟩),
  (128, ⟨36, 198, 1, "8,4,64,2"⟩),
  (129, ⟨36, 198, 2, "8,5,23,1,89,1"⟩),
  (130, ⟨35, 198, 0, "8,2,13,5,32,1"⟩),
  (131, ⟨35, 198, 1, "8,4,299,1"⟩),
  (132, ⟨35, 198, 2, "8,4,9,1,23,1,80,1"⟩),
  (133, ⟨34, 198, 0, "8,1,13,6,23,1"⟩),
  (134, ⟨34, 198, 1, "8,3,499,1"⟩),
  (135, ⟨34, 198, 2, "8,3,9,1,13,2,101,1"⟩),
  (137, ⟨33, 198, 0, "13,6,51,1"⟩),
  (138, ⟨33, 198, 1, "8,2,13,1,435,1"⟩),
  (139, ⟨33, 198, 2, "8,2,9,1,13,3,80,1"⟩),
  (140, ⟨33, 198, 3, "0,1,64,1,380,1"⟩),
  (142, ⟨32, 198, 1, "13,6,52,1"⟩),
  (143, ⟨32, 198, 2, "8,1,9,1,13,2,23,1,101,1"⟩),
  (144, ⟨32, 198, 3, "8,5,212,1"⟩),
  (145, ⟨32, 198, 4, "0,1,113,1,260,1"⟩),
  (146, ⟨32, 198, 5, "0,4,64,1,347,1"⟩),
  (147, ⟨31, 198, 0, "1145,1"⟩),
  (148, ⟨31, 198, 1, "9,1,13,3,23,1,80,1"⟩)]
private def bindings4 : List (Nat × BasisRow) := [(149, ⟨31, 198, 2, "8,4,13,1,188,1"⟩),
  (150, ⟨31, 198, 3, "0,2,1103,1"⟩),
  (151, ⟨31, 198, 4, "0,4,138,1,209,1"⟩),
  (152, ⟨30, 198, 0, "8,1,64,1,254,1"⟩),
  (153, ⟨30, 198, 1, "8,3,13,1,267,1"⟩),
  (155, ⟨30, 198, 3, "0,4,23,1,627,1"⟩),
  (156, ⟨29, 198, 0, "8,1,64,1,255,1"⟩),
  (157, ⟨29, 198, 1, "8,2,13,1,23,1,188,1"⟩),
  (158, ⟨29, 198, 2, "0,1,8,2,655,1"⟩),
  (159, ⟨29, 198, 3, "0,4,1079,1"⟩),
  (160, ⟨29, 198, 4, "0,4,64,1,349,1"⟩),
  (161, ⟨28, 198, 0, "13,3,303,1"⟩),
  (162, ⟨28, 198, 1, "8,1,13,3,212,1"⟩),
  (163, ⟨28, 198, 2, "8,2,667,1"⟩),
  (164, ⟨28, 198, 3, "0,1,8,1,874,1"⟩),
  (165, ⟨28, 198, 4, "0,4,1081,1"⟩),
  (166, ⟨28, 198, 5, "0,5,1063,1"⟩),
  (167, ⟨27, 198, 0, "13,4,188,1"⟩),
  (168, ⟨27, 198, 1, "9,1,13,2,328,1"⟩),
  (169, ⟨27, 198, 2, "8,2,668,1"⟩),
  (170, ⟨27, 198, 3, "0,1,23,1,655,1"⟩),
  (171, ⟨27, 198, 4, "0,2,3,1,978,1"⟩),
  (172, ⟨27, 198, 5, "0,6,1051,1"⟩),
  (173, ⟨26, 198, 0, "13,4,189,1"⟩),
  (174, ⟨26, 198, 1, "8,1,9,1,640,1"⟩),
  (175, ⟨26, 198, 2, "0,1,1122,1"⟩),
  (176, ⟨26, 198, 3, "0,4,1084,1"⟩),
  (177, ⟨25, 198, 0, "9,1,80,1,212,1"⟩),
  (178, ⟨25, 198, 1, "0,2,1105,1"⟩),
  (179, ⟨25, 198, 2, "0,2,67,1,359,1"⟩),
  (180, ⟨24, 198, 0, "13,4,190,1"⟩),
  (182, ⟨24, 198, 2, "0,2,68,1,359,1"⟩)]
private def bindings5 : List (Nat × BasisRow) := [(183, ⟨24, 198, 3, "0,10,59,1,324,1"⟩),
  (185, ⟨23, 198, 1, "9,1,13,2,331,1"⟩),
  (186, ⟨23, 198, 2, "2,1,1083,1"⟩),
  (188, ⟨22, 198, 0, "1147,1"⟩),
  (189, ⟨22, 198, 1, "0,1,77,1,324,1"⟩),
  (190, ⟨22, 198, 2, "0,2,1108,1"⟩),
  (191, ⟨21, 198, 0, "1149,1"⟩),
  (192, ⟨21, 198, 1, "1148,1"⟩),
  (193, ⟨21, 198, 2, "1,1,1107,1"⟩),
  (194, ⟨21, 198, 3, "0,1,78,1,324,1"⟩),
  (195, ⟨20, 198, 0, "1151,1"⟩),
  (197, ⟨20, 198, 2, "3,1,1011,1"⟩),
  (198, ⟨20, 198, 3, "1,2,1086,1"⟩),
  (204, ⟨18, 198, 2, "3,1,1016,1"⟩),
  (205, ⟨18, 198, 3, "3,1,1015,1"⟩),
  (206, ⟨18, 198, 4, "0,7,64,1,324,1"⟩),
  (208, ⟨17, 198, 1, "3,1,1017,1"⟩),
  (209, ⟨17, 198, 2, "1,1,1112,1"⟩),
  (210, ⟨17, 198, 3, "1,2,1088,1"⟩),
  (211, ⟨17, 198, 4, "0,1,1129,1"⟩),
  (212, ⟨17, 198, 5, "0,6,66,1,324,1"⟩),
  (213, ⟨16, 198, 0, "1157,1"⟩),
  (214, ⟨16, 198, 1, "3,1,1020,1"⟩),
  (215, ⟨16, 198, 2, "2,1,1088,1"⟩),
  (216, ⟨16, 198, 3, "1,2,1090,1"⟩),
  (217, ⟨16, 198, 4, "0,1,1131,1"⟩),
  (218, ⟨16, 198, 5, "0,2,2,1,1057,1"⟩),
  (220, ⟨15, 198, 1, "67,1,392,1"⟩),
  (221, ⟨15, 198, 2, "0,1,1133,1"⟩),
  (222, ⟨15, 198, 3, "0,1,1132,1"⟩),
  (224, ⟨14, 198, 1, "67,1,397,1"⟩),
  (225, ⟨14, 198, 2, "0,1,1135,1"⟩)]
private def bindings6 : List (Nat × BasisRow) := [(226, ⟨14, 198, 3, "0,2,1118,1"⟩),
  (227, ⟨13, 198, 0, "1160,1"⟩),
  (229, ⟨13, 198, 2, "0,1,1136,1"⟩),
  (230, ⟨13, 198, 3, "0,2,1120,1"⟩),
  (231, ⟨12, 198, 0, "1161,1"⟩),
  (232, ⟨12, 198, 1, "0,1,1138,1"⟩),
  (233, ⟨12, 198, 2, "0,1,79,1,324,1"⟩),
  (236, ⟨11, 198, 2, "0,1,80,1,324,1"⟩),
  (237, ⟨10, 198, 0, "1164,1"⟩),
  (239, ⟨10, 198, 2, "0,6,1058,1"⟩),
  (241, ⟨9, 198, 1, "83,1,324,1"⟩),
  (243, ⟨9, 198, 3, "0,6,18,2,324,1"⟩),
  (244, ⟨8, 198, 0, "1166,1"⟩),
  (247, ⟨8, 198, 3, "0,1,2,1,18,1,660,1"⟩),
  (248, ⟨7, 198, 0, "86,1,324,1"⟩),
  (249, ⟨7, 198, 1, "2,1,18,2,341,1"⟩),
  (250, ⟨7, 198, 2, "0,2,2,1,1058,1"⟩),
  (251, ⟨6, 198, 0, "0,2,2,1,18,2,324,1"⟩)]
private def bindingBlocks : List (List (Nat × BasisRow)) := [bindings0, bindings1, bindings2, bindings3, bindings4, bindings5, bindings6]
private def bindings : List (Nat × BasisRow) := bindingBlocks.flatten
private theorem checked : bindings.all (basisBindingCheck rows) = true := by cbv
private theorem bindings0_mem : bindings0 ∈ bindingBlocks :=
  List.getElem_mem (l := bindingBlocks) (n := 0) (by decide)
private theorem bindings0_subset (b : Nat × BasisRow) (hb : b ∈ bindings0) : b ∈ bindings :=
  List.mem_flatten.mpr ⟨bindings0, bindings0_mem, hb⟩
private theorem bindings1_mem : bindings1 ∈ bindingBlocks :=
  List.getElem_mem (l := bindingBlocks) (n := 1) (by decide)
private theorem bindings1_subset (b : Nat × BasisRow) (hb : b ∈ bindings1) : b ∈ bindings :=
  List.mem_flatten.mpr ⟨bindings1, bindings1_mem, hb⟩
private theorem bindings2_mem : bindings2 ∈ bindingBlocks :=
  List.getElem_mem (l := bindingBlocks) (n := 2) (by decide)
private theorem bindings2_subset (b : Nat × BasisRow) (hb : b ∈ bindings2) : b ∈ bindings :=
  List.mem_flatten.mpr ⟨bindings2, bindings2_mem, hb⟩
private theorem bindings3_mem : bindings3 ∈ bindingBlocks :=
  List.getElem_mem (l := bindingBlocks) (n := 3) (by decide)
private theorem bindings3_subset (b : Nat × BasisRow) (hb : b ∈ bindings3) : b ∈ bindings :=
  List.mem_flatten.mpr ⟨bindings3, bindings3_mem, hb⟩
private theorem bindings4_mem : bindings4 ∈ bindingBlocks :=
  List.getElem_mem (l := bindingBlocks) (n := 4) (by decide)
private theorem bindings4_subset (b : Nat × BasisRow) (hb : b ∈ bindings4) : b ∈ bindings :=
  List.mem_flatten.mpr ⟨bindings4, bindings4_mem, hb⟩
private theorem bindings5_mem : bindings5 ∈ bindingBlocks :=
  List.getElem_mem (l := bindingBlocks) (n := 5) (by decide)
private theorem bindings5_subset (b : Nat × BasisRow) (hb : b ∈ bindings5) : b ∈ bindings :=
  List.mem_flatten.mpr ⟨bindings5, bindings5_mem, hb⟩
private theorem bindings6_mem : bindings6 ∈ bindingBlocks :=
  List.getElem_mem (l := bindingBlocks) (n := 6) (by decide)
private theorem bindings6_subset (b : Nat × BasisRow) (hb : b ∈ bindings6) : b ∈ bindings :=
  List.mem_flatten.mpr ⟨bindings6, bindings6_mem, hb⟩
theorem row9216_mem : (⟨23, 197, 0, "9,1,80,1,209,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[0]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9217_mem : (⟨23, 197, 1, "0,1,68,1,359,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[1]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9218_mem : (⟨23, 197, 2, "0,9,59,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[2]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9219_mem : (⟨22, 197, 0, "0,1,18,1,690,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[3]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9220_mem : (⟨22, 197, 1, "0,1,3,1,982,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[4]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9221_mem : (⟨21, 197, 0, "1124,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[5]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9223_mem : (⟨21, 197, 2, "0,1,1108,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[6]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9224_mem : (⟨21, 197, 3, "0,1,3,1,984,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[7]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9225_mem : (⟨20, 197, 0, "1125,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[8]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9226_mem : (⟨20, 197, 1, "78,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[9]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9227_mem : (⟨20, 197, 2, "0,1,67,1,363,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[10]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9229_mem : (⟨19, 197, 1, "1,1,1096,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[11]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9230_mem : (⟨19, 197, 2, "0,5,1055,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[12]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9232_mem : (⟨18, 197, 1, "75,1,335,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[13]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9233_mem : (⟨18, 197, 2, "2,2,1004,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[14]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9234_mem : (⟨18, 197, 3, "0,3,1088,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[15]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9235_mem : (⟨18, 197, 4, "0,5,1057,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[16]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9240_mem : (⟨17, 197, 4, "0,1,1113,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[17]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9241_mem : (⟨17, 197, 5, "0,6,64,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[18]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9243_mem : (⟨16, 197, 1, "67,1,373,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[19]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9244_mem : (⟨16, 197, 2, "8,2,20,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[20]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9245_mem : (⟨16, 197, 3, "0,1,43,1,543,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[21]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9246_mem : (⟨16, 197, 4, "0,2,1098,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[22]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9247_mem : (⟨16, 197, 5, "0,5,66,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[23]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9250_mem : (⟨15, 197, 2, "67,1,376,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[24]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9251_mem : (⟨15, 197, 3, "8,1,45,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[25]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9252_mem : (⟨15, 197, 4, "0,1,43,1,544,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[26]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9253_mem : (⟨15, 197, 5, "0,1,2,1,1057,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[27]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9254_mem : (⟨15, 197, 6, "0,2,1099,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[28]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9255_mem : (⟨14, 197, 0, "1134,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[29]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9256_mem : (⟨14, 197, 1, "1133,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[30]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9257_mem : (⟨14, 197, 2, "1132,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings0[31]'(by decide)) (bindings0_subset _ (List.getElem_mem _))
theorem row9258_mem : (⟨14, 197, 3, "8,1,46,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[0]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9259_mem : (⟨14, 197, 4, "1,1,1100,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[1]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9260_mem : (⟨14, 197, 5, "0,3,72,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[2]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9261_mem : (⟨13, 197, 0, "1135,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[3]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9262_mem : (⟨13, 197, 1, "9,1,13,2,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[4]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9263_mem : (⟨13, 197, 2, "0,1,1118,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[5]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9264_mem : (⟨12, 197, 0, "1136,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[6]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9265_mem : (⟨12, 197, 1, "0,1,1120,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[7]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9266_mem : (⟨11, 197, 0, "1138,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[8]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9268_mem : (⟨11, 197, 2, "79,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[9]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9269_mem : (⟨10, 197, 0, "80,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[10]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9270_mem : (⟨10, 197, 1, "1,1,18,1,684,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[11]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9271_mem : (⟨10, 197, 2, "0,2,73,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[12]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9272_mem : (⟨9, 197, 0, "0,2,74,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[13]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9273_mem : (⟨9, 197, 1, "0,5,1058,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[14]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9275_mem : (⟨8, 197, 1, "0,5,18,2,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[15]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9276_mem : (⟨7, 197, 0, "2,1,18,1,660,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[16]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9277_mem : (⟨7, 197, 1, "1,1,76,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[17]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9278_mem : (⟨6, 197, 0, "2,1,70,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[18]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9279_mem : (⟨6, 197, 1, "0,1,2,1,1058,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[19]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9280_mem : (⟨5, 197, 0, "0,1,2,1,18,2,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[20]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9281_mem : (⟨198, 198, 0, "0,198"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[21]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9282_mem : (⟨67, 198, 0, "0,2,1101,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[22]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9284_mem : (⟨63, 198, 0, "1140,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[23]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9286_mem : (⟨59, 198, 0, "8,1,16,1,554,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[24]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9287_mem : (⟨58, 198, 0, "8,1,17,1,554,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[25]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9288_mem : (⟨57, 198, 0, "8,1,886,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[26]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9289_mem : (⟨56, 198, 0, "8,4,295,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[27]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9290_mem : (⟨55, 198, 0, "8,4,296,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[28]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9292_mem : (⟨54, 198, 1, "8,2,16,1,17,1,183,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[29]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9293_mem : (⟨53, 198, 0, "1142,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[30]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9294_mem : (⟨53, 198, 1, "8,3,498,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings1[31]'(by decide)) (bindings1_subset _ (List.getElem_mem _))
theorem row9295_mem : (⟨52, 198, 0, "8,6,145,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[0]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9296_mem : (⟨51, 198, 0, "8,5,16,1,111,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[1]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9297_mem : (⟨51, 198, 1, "0,4,17,1,685,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[2]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9299_mem : (⟨50, 198, 1, "8,5,17,1,111,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[3]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9300_mem : (⟨50, 198, 2, "0,3,17,2,403,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[4]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9301_mem : (⟨49, 198, 0, "8,2,663,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[5]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9302_mem : (⟨49, 198, 1, "8,5,211,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[6]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9303_mem : (⟨49, 198, 2, "0,7,1033,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[7]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9304_mem : (⟨48, 198, 0, "8,1,17,1,556,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[8]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9305_mem : (⟨48, 198, 1, "8,8,49,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[9]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9306_mem : (⟨48, 198, 2, "0,5,1059,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[10]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9307_mem : (⟨47, 198, 0, "17,2,433,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[11]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9308_mem : (⟨47, 198, 1, "8,8,50,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[12]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9309_mem : (⟨46, 198, 0, "8,4,297,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[13]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9310_mem : (⟨46, 198, 1, "8,6,16,1,17,2"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[14]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9311_mem : (⟨45, 198, 0, "8,4,298,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[15]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9312_mem : (⟨45, 198, 1, "8,7,88,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[16]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9314_mem : (⟨44, 198, 1, "8,3,17,1,238,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[17]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9315_mem : (⟨44, 198, 2, "8,11"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[18]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9316_mem : (⟨43, 198, 0, "64,1,403,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[19]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9317_mem : (⟨43, 198, 1, "8,2,17,2,185,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[20]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9318_mem : (⟨43, 198, 2, "8,9,22,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[21]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9319_mem : (⟨43, 198, 3, "0,1,16,1,725,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[22]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9320_mem : (⟨42, 198, 0, "138,1,225,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[23]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9321_mem : (⟨42, 198, 1, "8,6,146,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[24]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9322_mem : (⟨42, 198, 2, "8,9,23,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[25]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9323_mem : (⟨42, 198, 3, "0,1,17,1,725,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[26]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9324_mem : (⟨41, 198, 0, "1144,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[27]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9326_mem : (⟨41, 198, 2, "8,6,147,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[28]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9327_mem : (⟨41, 198, 3, "8,8,51,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[29]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9328_mem : (⟨40, 198, 0, "8,1,16,1,64,1,137,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[30]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9329_mem : (⟨40, 198, 1, "8,5,17,1,113,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings2[31]'(by decide)) (bindings2_subset _ (List.getElem_mem _))
theorem row9330_mem : (⟨40, 198, 2, "8,7,13,3"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[0]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9331_mem : (⟨39, 198, 0, "8,1,16,1,64,1,138,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[1]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9332_mem : (⟨39, 198, 1, "8,4,17,1,162,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[2]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9333_mem : (⟨39, 198, 2, "8,6,13,2,32,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[3]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9334_mem : (⟨39, 198, 3, "0,1,8,3,491,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[4]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9335_mem : (⟨38, 198, 0, "8,2,664,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[5]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9336_mem : (⟨38, 198, 1, "8,5,13,3,23,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[6]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9337_mem : (⟨38, 198, 2, "8,7,89,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[7]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9338_mem : (⟨38, 198, 3, "0,1,8,1,16,1,17,1,260,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[8]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9339_mem : (⟨37, 198, 0, "8,2,665,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[9]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9340_mem : (⟨37, 198, 1, "8,4,13,3,51,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[10]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9341_mem : (⟨37, 198, 2, "8,6,9,1,80,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[11]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9343_mem : (⟨36, 198, 0, "8,3,13,6"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[12]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9344_mem : (⟨36, 198, 1, "8,4,64,2"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[13]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9345_mem : (⟨36, 198, 2, "8,5,23,1,89,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[14]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9346_mem : (⟨35, 198, 0, "8,2,13,5,32,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[15]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9347_mem : (⟨35, 198, 1, "8,4,299,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[16]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9348_mem : (⟨35, 198, 2, "8,4,9,1,23,1,80,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[17]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9349_mem : (⟨34, 198, 0, "8,1,13,6,23,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[18]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9350_mem : (⟨34, 198, 1, "8,3,499,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[19]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9351_mem : (⟨34, 198, 2, "8,3,9,1,13,2,101,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[20]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9353_mem : (⟨33, 198, 0, "13,6,51,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[21]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9354_mem : (⟨33, 198, 1, "8,2,13,1,435,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[22]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9355_mem : (⟨33, 198, 2, "8,2,9,1,13,3,80,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[23]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9356_mem : (⟨33, 198, 3, "0,1,64,1,380,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[24]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9358_mem : (⟨32, 198, 1, "13,6,52,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[25]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9359_mem : (⟨32, 198, 2, "8,1,9,1,13,2,23,1,101,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[26]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9360_mem : (⟨32, 198, 3, "8,5,212,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[27]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9361_mem : (⟨32, 198, 4, "0,1,113,1,260,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[28]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9362_mem : (⟨32, 198, 5, "0,4,64,1,347,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[29]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9363_mem : (⟨31, 198, 0, "1145,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[30]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9364_mem : (⟨31, 198, 1, "9,1,13,3,23,1,80,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings3[31]'(by decide)) (bindings3_subset _ (List.getElem_mem _))
theorem row9365_mem : (⟨31, 198, 2, "8,4,13,1,188,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[0]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9366_mem : (⟨31, 198, 3, "0,2,1103,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[1]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9367_mem : (⟨31, 198, 4, "0,4,138,1,209,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[2]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9368_mem : (⟨30, 198, 0, "8,1,64,1,254,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[3]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9369_mem : (⟨30, 198, 1, "8,3,13,1,267,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[4]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9371_mem : (⟨30, 198, 3, "0,4,23,1,627,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[5]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9372_mem : (⟨29, 198, 0, "8,1,64,1,255,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[6]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9373_mem : (⟨29, 198, 1, "8,2,13,1,23,1,188,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[7]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9374_mem : (⟨29, 198, 2, "0,1,8,2,655,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[8]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9375_mem : (⟨29, 198, 3, "0,4,1079,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[9]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9376_mem : (⟨29, 198, 4, "0,4,64,1,349,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[10]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9377_mem : (⟨28, 198, 0, "13,3,303,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[11]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9378_mem : (⟨28, 198, 1, "8,1,13,3,212,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[12]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9379_mem : (⟨28, 198, 2, "8,2,667,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[13]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9380_mem : (⟨28, 198, 3, "0,1,8,1,874,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[14]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9381_mem : (⟨28, 198, 4, "0,4,1081,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[15]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9382_mem : (⟨28, 198, 5, "0,5,1063,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[16]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9383_mem : (⟨27, 198, 0, "13,4,188,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[17]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9384_mem : (⟨27, 198, 1, "9,1,13,2,328,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[18]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9385_mem : (⟨27, 198, 2, "8,2,668,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[19]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9386_mem : (⟨27, 198, 3, "0,1,23,1,655,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[20]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9387_mem : (⟨27, 198, 4, "0,2,3,1,978,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[21]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9388_mem : (⟨27, 198, 5, "0,6,1051,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[22]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9389_mem : (⟨26, 198, 0, "13,4,189,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[23]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9390_mem : (⟨26, 198, 1, "8,1,9,1,640,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[24]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9391_mem : (⟨26, 198, 2, "0,1,1122,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[25]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9392_mem : (⟨26, 198, 3, "0,4,1084,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[26]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9393_mem : (⟨25, 198, 0, "9,1,80,1,212,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[27]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9394_mem : (⟨25, 198, 1, "0,2,1105,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[28]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9395_mem : (⟨25, 198, 2, "0,2,67,1,359,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[29]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9396_mem : (⟨24, 198, 0, "13,4,190,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[30]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9398_mem : (⟨24, 198, 2, "0,2,68,1,359,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings4[31]'(by decide)) (bindings4_subset _ (List.getElem_mem _))
theorem row9399_mem : (⟨24, 198, 3, "0,10,59,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[0]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9401_mem : (⟨23, 198, 1, "9,1,13,2,331,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[1]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9402_mem : (⟨23, 198, 2, "2,1,1083,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[2]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9404_mem : (⟨22, 198, 0, "1147,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[3]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9405_mem : (⟨22, 198, 1, "0,1,77,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[4]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9406_mem : (⟨22, 198, 2, "0,2,1108,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[5]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9407_mem : (⟨21, 198, 0, "1149,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[6]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9408_mem : (⟨21, 198, 1, "1148,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[7]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9409_mem : (⟨21, 198, 2, "1,1,1107,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[8]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9410_mem : (⟨21, 198, 3, "0,1,78,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[9]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9411_mem : (⟨20, 198, 0, "1151,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[10]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9413_mem : (⟨20, 198, 2, "3,1,1011,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[11]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9414_mem : (⟨20, 198, 3, "1,2,1086,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[12]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9420_mem : (⟨18, 198, 2, "3,1,1016,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[13]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9421_mem : (⟨18, 198, 3, "3,1,1015,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[14]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9422_mem : (⟨18, 198, 4, "0,7,64,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[15]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9424_mem : (⟨17, 198, 1, "3,1,1017,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[16]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9425_mem : (⟨17, 198, 2, "1,1,1112,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[17]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9426_mem : (⟨17, 198, 3, "1,2,1088,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[18]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9427_mem : (⟨17, 198, 4, "0,1,1129,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[19]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9428_mem : (⟨17, 198, 5, "0,6,66,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[20]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9429_mem : (⟨16, 198, 0, "1157,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[21]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9430_mem : (⟨16, 198, 1, "3,1,1020,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[22]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9431_mem : (⟨16, 198, 2, "2,1,1088,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[23]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9432_mem : (⟨16, 198, 3, "1,2,1090,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[24]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9433_mem : (⟨16, 198, 4, "0,1,1131,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[25]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9434_mem : (⟨16, 198, 5, "0,2,2,1,1057,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[26]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9436_mem : (⟨15, 198, 1, "67,1,392,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[27]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9437_mem : (⟨15, 198, 2, "0,1,1133,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[28]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9438_mem : (⟨15, 198, 3, "0,1,1132,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[29]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9440_mem : (⟨14, 198, 1, "67,1,397,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[30]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9441_mem : (⟨14, 198, 2, "0,1,1135,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings5[31]'(by decide)) (bindings5_subset _ (List.getElem_mem _))
theorem row9442_mem : (⟨14, 198, 3, "0,2,1118,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[0]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9443_mem : (⟨13, 198, 0, "1160,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[1]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9445_mem : (⟨13, 198, 2, "0,1,1136,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[2]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9446_mem : (⟨13, 198, 3, "0,2,1120,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[3]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9447_mem : (⟨12, 198, 0, "1161,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[4]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9448_mem : (⟨12, 198, 1, "0,1,1138,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[5]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9449_mem : (⟨12, 198, 2, "0,1,79,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[6]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9452_mem : (⟨11, 198, 2, "0,1,80,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[7]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9453_mem : (⟨10, 198, 0, "1164,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[8]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9455_mem : (⟨10, 198, 2, "0,6,1058,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[9]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9457_mem : (⟨9, 198, 1, "83,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[10]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9459_mem : (⟨9, 198, 3, "0,6,18,2,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[11]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9460_mem : (⟨8, 198, 0, "1166,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[12]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9463_mem : (⟨8, 198, 3, "0,1,2,1,18,1,660,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[13]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9464_mem : (⟨7, 198, 0, "86,1,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[14]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9465_mem : (⟨7, 198, 1, "2,1,18,2,341,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[15]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9466_mem : (⟨7, 198, 2, "0,2,2,1,1058,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[16]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
theorem row9467_mem : (⟨6, 198, 0, "0,2,2,1,18,2,324,1"⟩ : BasisRow) ∈ basisRows :=
  basisBindings_mem 9 chunkBound rows transcription bindings checked
    (bindings6[17]'(by decide)) (bindings6_subset _ (List.getElem_mem _))
end KIP126.LinModule.NaturalityWords200.Shared.BasisChunk009
