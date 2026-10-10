import KIP126.Interface.Challenge.Challenge2

/-! GENERATED named projections from explicit C(M) hypotheses. These theorems
do NOT prove the database computations or add mathematical assumptions. -/
namespace KIP126.Computation.Route
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  {D : Model H M Syn} {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}
set_option maxRecDepth 10000

/-- Cnu_AdamsE2_ss row 3872; equation. Coordinates are degree-local. -/
def record_d3_cnu_bottom_x_126_8 : Raw.Claim := ⟨.nuCofiber, .equation, 3, 8, 134, [4], 11, 136, [1], "Cnu_AdamsE2_ss", 3872⟩
theorem Inputs.d3_cnu_bottom_x_126_8 (I : Inputs D L G) : Statement I.realization record_d3_cnu_bottom_x_126_8 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 33) (by decide))

/-- Cnu_AdamsE2_ss row 3873; equation. Coordinates are degree-local. -/
def record_d3_cnu_bottom_x_126_8_2 : Raw.Claim := ⟨.nuCofiber, .equation, 3, 8, 134, [3], 11, 136, [2], "Cnu_AdamsE2_ss", 3873⟩
theorem Inputs.d3_cnu_bottom_x_126_8_2 (I : Inputs D L G) : Statement I.realization record_d3_cnu_bottom_x_126_8_2 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 34) (by decide))

/-- S0_AdamsE2_ss row 2433; reaches. Coordinates are degree-local. -/
def record_X_reaches_e6 : Raw.Claim := ⟨.sphere, .reaches, 6, 8, 130, [0], 8, 130, [], "S0_AdamsE2_ss", 2433⟩
theorem Inputs.X_reaches_e6 (I : Inputs D L G) : Statement I.realization record_X_reaches_e6 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 197) (by decide))

/-- S0_AdamsE2_ss row 2702; reaches. Coordinates are degree-local. -/
def record_W_reaches_e6 : Raw.Claim := ⟨.sphere, .reaches, 6, 8, 134, [0, 3], 8, 134, [], "S0_AdamsE2_ss", 2702⟩
theorem Inputs.W_reaches_e6 (I : Inputs D L G) : Statement I.realization record_W_reaches_e6 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 204) (by decide))

/-- S0_AdamsE2_ss row 2569; reaches. Coordinates are degree-local. -/
def record_V_reaches_e12 : Raw.Claim := ⟨.sphere, .reaches, 12, 9, 132, [0, 1], 9, 132, [], "S0_AdamsE2_ss", 2569⟩
theorem Inputs.V_reaches_e12 (I : Inputs D L G) : Statement I.realization record_V_reaches_e12 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 219) (by decide))

/-- S0_AdamsE2_ss row 2852; reaches. Coordinates are degree-local. -/
def record_Y_reaches_e5 : Raw.Claim := ⟨.sphere, .reaches, 5, 11, 136, [3], 11, 136, [], "S0_AdamsE2_ss", 2852⟩
theorem Inputs.Y_reaches_e5 (I : Inputs D L G) : Statement I.realization record_Y_reaches_e5 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 281) (by decide))

/-- S0_AdamsE2_ss row 3080; reaches. Coordinates are degree-local. -/
def record_T_reaches_e1000 : Raw.Claim := ⟨.sphere, .reaches, 1000, 14, 139, [1], 14, 139, [], "S0_AdamsE2_ss", 3080⟩
theorem Inputs.T_reaches_e1000 (I : Inputs D L G) : Statement I.realization record_T_reaches_e1000 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 342) (by decide))

/-- proofs.db/log row 5541; equation. Coordinates are degree-local. -/
def record_d2_h6 : Raw.Claim := ⟨.sphere, .equation, 2, 1, 64, [0], 3, 65, [0], "proofs.db/log", 5541⟩
theorem Inputs.d2_h6 (I : Inputs D L G) : Statement I.realization record_d2_h6 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 651) (by decide))

/-- proofs.db/log row 5990; equation. Coordinates are degree-local. -/
def record_d2_x_125_8 : Raw.Claim := ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "proofs.db/log", 5990⟩
theorem Inputs.d2_x_125_8 (I : Inputs D L G) : Statement I.realization record_d2_x_125_8 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 652) (by decide))

/-- proofs.db/log row 153768; equation. Coordinates are degree-local. -/
def record_d3_h4_x_109_12 : Raw.Claim := ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "proofs.db/log", 153768⟩
theorem Inputs.d3_h4_x_109_12 (I : Inputs D L G) : Statement I.realization record_d3_h4_x_109_12 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 653) (by decide))

/-- proofs.db/log row 462481; equation. Coordinates are degree-local. -/
def record_d3_h0Sq_x_123_13_2 : Raw.Claim := ⟨.sphere, .equation, 3, 15, 138, [2], 18, 140, [2], "proofs.db/log", 462481⟩
theorem Inputs.d3_h0Sq_x_123_13_2 (I : Inputs D L G) : Statement I.realization record_d3_h0Sq_x_123_13_2 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 654) (by decide))

/-- proofs.db/log row 929469; equation. Coordinates are degree-local. -/
def record_d3_x_126_4 : Raw.Claim := ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "proofs.db/log", 929469⟩
theorem Inputs.d3_x_126_4 (I : Inputs D L G) : Statement I.realization record_d3_x_126_4 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 655) (by decide))

/-- proofs.db/log row 2671068; equation. Coordinates are degree-local. -/
def record_d7_x_123_combination : Raw.Claim := ⟨.sphere, .equation, 7, 11, 134, [0, 1, 3], 18, 140, [1], "proofs.db/log", 2671068⟩
theorem Inputs.d7_x_123_combination (I : Inputs D L G) : Statement I.realization record_d7_x_123_combination :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 656) (by decide))

/-- proofs.db/log row 212838; equation. Coordinates are degree-local. -/
def record_d3_cnu_top : Raw.Claim := ⟨.nuCofiber, .equation, 3, 8, 134, [0], 11, 136, [1, 2, 3], "proofs.db/log", 212838⟩
theorem Inputs.d3_cnu_top (I : Inputs D L G) : Statement I.realization record_d3_cnu_top :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 657) (by decide))

/-- proofs.db/log row 2047477; refutation. Coordinates are degree-local. -/
def record_refutation_2047477 : Raw.Claim := ⟨.sphere, .refutation, 3, 6, 132, [0], 9, 134, [], "proofs.db/log", 2047477⟩
theorem Inputs.refutation_2047477 (I : Inputs D L G) : Statement I.realization record_refutation_2047477 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 659) (by decide))

/-- proofs.db/log row 2047478; refutation. Coordinates are degree-local. -/
def record_refutation_2047478 : Raw.Claim := ⟨.sphere, .refutation, 3, 6, 132, [0], 9, 134, [2], "proofs.db/log", 2047478⟩
theorem Inputs.refutation_2047478 (I : Inputs D L G) : Statement I.realization record_refutation_2047478 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 660) (by decide))

/-- proofs.db/log row 154532; refutation. Coordinates are degree-local. -/
def record_refutation_154532 : Raw.Claim := ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [], "proofs.db/log", 154532⟩
theorem Inputs.refutation_154532 (I : Inputs D L G) : Statement I.realization record_refutation_154532 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 661) (by decide))

/-- proofs.db/log row 154533; refutation. Coordinates are degree-local. -/
def record_refutation_154533 : Raw.Claim := ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [3], "proofs.db/log", 154533⟩
theorem Inputs.refutation_154533 (I : Inputs D L G) : Statement I.realization record_refutation_154533 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 662) (by decide))

/-- proofs.db/log row 154534; refutation. Coordinates are degree-local. -/
def record_refutation_154534 : Raw.Claim := ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [2], "proofs.db/log", 154534⟩
theorem Inputs.refutation_154534 (I : Inputs D L G) : Statement I.realization record_refutation_154534 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 663) (by decide))

/-- proofs.db/log row 154535; refutation. Coordinates are degree-local. -/
def record_refutation_154535 : Raw.Claim := ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [2, 3], "proofs.db/log", 154535⟩
theorem Inputs.refutation_154535 (I : Inputs D L G) : Statement I.realization record_refutation_154535 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 664) (by decide))

/-- proofs.db/log row 154536; refutation. Coordinates are degree-local. -/
def record_refutation_154536 : Raw.Claim := ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [0, 1], "proofs.db/log", 154536⟩
theorem Inputs.refutation_154536 (I : Inputs D L G) : Statement I.realization record_refutation_154536 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 665) (by decide))

/-- proofs.db/log row 154537; refutation. Coordinates are degree-local. -/
def record_refutation_154537 : Raw.Claim := ⟨.sphere, .refutation, 4, 21, 147, [0], 25, 150, [0, 1, 3], "proofs.db/log", 154537⟩
theorem Inputs.refutation_154537 (I : Inputs D L G) : Statement I.realization record_refutation_154537 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 666) (by decide))

/-- S0_AdamsE2_basis/d2 row 513; equation. Coordinates are degree-local. -/
def record_d2_h0Six_h6 : Raw.Claim := ⟨.sphere, .equation, 2, 7, 70, [2], 9, 71, [0], "S0_AdamsE2_basis/d2", 513⟩
theorem Inputs.d2_h0Six_h6 (I : Inputs D L G) : Statement I.realization record_d2_h0Six_h6 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 667) (by decide))

/-- S0_AdamsE2_basis/d2 row 2855; equation. Coordinates are degree-local. -/
def record_d2_for_P_h2 : Raw.Claim := ⟨.sphere, .equation, 2, 10, 136, [0], 12, 137, [2], "S0_AdamsE2_basis/d2", 2855⟩
theorem Inputs.d2_for_P_h2 (I : Inputs D L G) : Statement I.realization record_d2_for_P_h2 :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 668) (by decide))

/-- S0_AdamsE2_basis/d2 row 2923; equation. Coordinates are degree-local. -/
def record_d2_for_Q_h2_first : Raw.Claim := ⟨.sphere, .equation, 2, 11, 137, [0], 13, 138, [3], "S0_AdamsE2_basis/d2", 2923⟩
theorem Inputs.d2_for_Q_h2_first (I : Inputs D L G) : Statement I.realization record_d2_for_Q_h2_first :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 669) (by decide))

/-- S0_AdamsE2_basis/d2 row 2926; equation. Coordinates are degree-local. -/
def record_d2_for_Q_h2_second : Raw.Claim := ⟨.sphere, .equation, 2, 11, 137, [3], 13, 138, [4], "S0_AdamsE2_basis/d2", 2926⟩
theorem Inputs.d2_for_Q_h2_second (I : Inputs D L G) : Statement I.realization record_d2_for_Q_h2_second :=
  I.results _ (by exact List.getElem_mem (l := Raw.claims) (n := 670) (by decide))

end KIP126.Computation.Route
