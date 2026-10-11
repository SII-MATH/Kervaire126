module

public import KIP126.Main.Solution.Computation.Route.Bounds
public import KIP126.Main.Solution.Computation.Route.NamedSurvival
public import KIP126.Main.Solution.Computation.Route.Candidates
public import KIP126.Main.Solution.Computation.Route.High125
public import KIP126.Main.Solution.Computation.Route.Stem125Vanishing
public import KIP126.Main.Solution.Computation.Route.Stem125Differentials
public import KIP126.Main.Solution.Computation.Route.CofiberAndFiltration
import all KIP126.Main.Solution.Computation.Route.SphereSurvival
import all KIP126.Main.Solution.Computation.Route.SphereDifferentials
import all KIP126.Main.Solution.Computation.Route.SphereIncoming
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

/-!
# Proof obligations deriving Section 7 facts from the finite C interface

The statements in this file are internal proof tasks.  `sorry` marks an
unfinished proof, not an accepted program result or literature axiom.  The
original `Inputs.results` retains its finite strength.  There is one D, one
realization `I.realization`, and the same route/tmf labels throughout.

The range proof is independent of the pinned computations and of the paper's
new generalized Leibniz/Mahowald rules.  No theorem below is used as a premise
of a certification rule for the same input records.
-/

@[expose] public section

namespace KIP126.Computation.Route
open CategoryTheory.Limits KIP126.Core.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.LinE2.RelationCertificates
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Core.SpectralSequence KIP126.Synthetic.Context KIP126.Kervaire.Route
open KIP126.LinE2 KIP126.Computation.Near126
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

variable {D : Model H M Syn} {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}

section SphereFactsProof
open CategoryTheory.Limits KIP126.Core.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

open private sphere_basic_survival sphere_low_page_vanishing y_survives_five vx_empty_page
  from KIP126.Main.Solution.Computation.Route.SphereSurvival
open private sphere_named_differentials sphere_product_obstructions
  from KIP126.Main.Solution.Computation.Route.SphereDifferentials
open private sphere_t_incoming_and_survival
  t_incoming_t_incoming8_source_four t_incoming_t_incoming10_source_four
  t_incoming_t_incoming9_zero_h164 t_incoming_t_incoming11_zero_h151
  from KIP126.Main.Solution.Computation.Route.SphereIncoming

/-- The four delivered d₂ directions have zero coordinate along the named
E₃ target. Controlling the remaining column therefore excludes every incoming
d₂ boundary, and the delivered d₃ equation is nonzero. -/
private theorem h4_d3_nonzero_of_remaining_span (I : Inputs D L G)
    (hcol : (sequence D .sphere).d 2 (14,138)
      (I.realization.basis .sphere 14 138 2) ∈
      Submodule.span ℤ {I.realization.basis .sphere 16 139 1,
        I.realization.basis .sphere 16 139 2}) :
    Derived.Differential I.realization 3 (mulAt (atom .h4) (atom .x_109_12))
      (mulAt dataH1 (atom .x_122_15_2)) := by
  classical
  let E := sequence D .sphere
  have next_projection_zero_iff_incoming
      (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
      (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
      (z : (Subobject.underlying.obj ((E.ssData (p+E.diffDeg r)).Z
        ↑((r-E.r₀).toNat+1)) : ModuleCat.{v} ℤ)) :
      (E.ssData (p+E.diffDeg r)).pageπ ↑((r-E.r₀).toNat+1) z = 0 ↔
        (Subobject.ofLE _ _ ((E.ssData (p+E.diffDeg r)).Z_anti
          (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
            (E.ssData (p+E.diffDeg r)).pageπ ↑(r-E.r₀).toNat) z ∈
          LinearMap.range (E.d r p).hom := by
    let D := E.ssData (p+E.diffDeg r)
    let n := (r-E.r₀).toNat
    have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
    let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hnm)
    let j := Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑n)
      ((D.B_le_Z _).trans (D.Z_anti hnm))
    rw [← subobjectModule_image, E.B_succ r p hr, subobjectModule_image]
    change D.pageπ ↑(n+1) z = 0 ↔ (i ≫ D.pageπ ↑n) z ∈ LinearMap.range (j ≫ D.pageπ ↑n).hom
    constructor
    · intro hz
      obtain ⟨v, hv⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _)) z).mp hz
      refine ⟨v, ?_⟩
      rw [← hv]
      change (j ≫ D.pageπ ↑n) v =
        ((Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _)) ≫ i ≫ D.pageπ ↑n) v
      congr 2
      dsimp only [i,j]
      rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
    · rintro ⟨v, hv⟩
      apply (subobject_cokernel_π_eq_zero_iff (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _) z).mpr
      have hz : D.pageπ ↑n (i z-j v) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr hv.symm
      have hb := (subobject_cokernel_π_eq_zero_iff (D.B ↑n) (D.Z ↑n) (D.B_le_Z _) _).mp hz
      have hb' := (ModuleCat.subobjectModule D.V).monotone (D.B_mono hnm) hb
      have hv' : (D.Z ↑n).arrow (j v) ∈ (ModuleCat.subobjectModule D.V) (D.B ↑(n+1)) := by
        change (j ≫ (D.Z ↑n).arrow) v ∈ _
        dsimp only [j]
        rw [Subobject.ofLE_arrow]
        exact ⟨v, rfl⟩
      have hh := ((ModuleCat.subobjectModule D.V) (D.B ↑(n+1))).add_mem hb' hv'
      rw [map_sub, sub_add_cancel] at hh
      change (i ≫ (D.Z ↑n).arrow) z ∈ _ at hh
      dsimp only [i] at hh
      rwa [Subobject.ofLE_arrow] at hh
  have h308 : HasDifferential E 2 (12,137) (14,138)
      (I.realization.basis .sphere 12 137 1) (I.realization.basis .sphere 14 138 4) := by
    have hr := I.results ⟨.sphere,.equation,2,12,137,[1],14,138,[4],"S0_AdamsE2_ss",2921⟩
      (by exact List.getElem_mem (l := Raw.claims) (n := 308) (by decide))
    dsimp only [Statement] at hr
    obtain ⟨a,ha,b,hb,hd⟩ := hr
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [4] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    exact hd
  have h309 : HasDifferential E 2 (12,137) (14,138)
      (I.realization.basis .sphere 12 137 0) (I.realization.basis .sphere 14 138 3) := by
    have hr := I.results ⟨.sphere,.equation,2,12,137,[0],14,138,[3],"S0_AdamsE2_ss",2922⟩
      (by exact List.getElem_mem (l := Raw.claims) (n := 309) (by decide))
    dsimp only [Statement] at hr
    obtain ⟨a,ha,b,hb,hd⟩ := hr
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [3] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    exact hd
  have h324 : HasDifferential E 3 (13,137) (16,139)
      (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := by
    have hr := I.results ⟨.sphere,.equation,3,13,137,[2],16,139,[0],"S0_AdamsE2_ss",2917⟩
      (by exact List.getElem_mem (l := Raw.claims) (n := 324) (by decide))
    dsimp only [Statement] at hr
    obtain ⟨a,ha,b,hb,hd⟩ := hr
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    exact hd
  have h366 : HasDifferential E 2 (14,138) (16,139)
      (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := by
    have hr := I.results ⟨.sphere,.equation,2,14,138,[1],16,139,[1, 2],"S0_AdamsE2_ss",3072⟩
      (by exact List.getElem_mem (l := Raw.claims) (n := 366) (by decide))
    dsimp only [Statement] at hr
    obtain ⟨a,ha,b,hb,hd⟩ := hr
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    exact hd
  have h367 : HasDifferential E 2 (14,138) (16,139)
      (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := by
    have hr := I.results ⟨.sphere,.equation,2,14,138,[0, 1],16,139,[2],"S0_AdamsE2_ss",3073⟩
      (by exact List.getElem_mem (l := Raw.claims) (n := 367) (by decide))
    dsimp only [Statement] at hr
    obtain ⟨a,ha,b,hb,hd⟩ := hr
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hd
    exact hd
  obtain ⟨e,he⟩ := I.basis ⟨.sphere, 14, 138, ["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩
    (by exact List.getElem_mem (l := Raw.degrees) (n := 216) (by decide))
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) =
    I.realization.basis .sphere 14 138 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩
    (by exact List.getElem_mem (l := Raw.degrees) (n := 230) (by decide))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) =
    I.realization.basis .sphere 16 139 i.val at hf
  have hf0 : f.symm (Finsupp.single (0 : Fin 3) 1) = I.realization.basis .sphere 16 139 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1 : Fin 3) 1) = I.realization.basis .sphere 16 139 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2 : Fin 3) 1) = I.realization.basis .sphere 16 139 2 := hf 2
  have d1 : E.d 2 (14,138) (I.realization.basis .sphere 14 138 1) =
      I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2 :=
    h366.eq_on_page_two.2
  have d01 : E.d 2 (14,138)
      (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) =
      I.realization.basis .sphere 16 139 2 := h367.eq_on_page_two.2
  have d3 : E.d 2 (14,138) (I.realization.basis .sphere 14 138 3) = 0 := by
    have hd := h309.eq_on_page_two.2
    change E.d 2 (12,137) _ = _ at hd
    rw [←hd]
    exact congrArg (fun f => f (I.realization.basis .sphere 12 137 0)) (E.d_comp_d 2 (12,137))
  have d4 : E.d 2 (14,138) (I.realization.basis .sphere 14 138 4) = 0 := by
    have hd := h308.eq_on_page_two.2
    change E.d 2 (12,137) _ = _ at hd
    rw [←hd]
    exact congrArg (fun f => f (I.realization.basis .sphere 12 137 1)) (E.d_comp_d 2 (12,137))
  have coord1 : f (E.d 2 (14,138) (I.realization.basis .sphere 14 138 1)) 0 = 0 := by
    rw [d1, ←hf1, ←hf2, map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    norm_num [Finsupp.single_apply, Fin.ext_iff]
  have coord0 : f (E.d 2 (14,138) (I.realization.basis .sphere 14 138 0)) 0 = 0 := by
    have hh := congrArg (fun z => f z 0) d01
    simp only [map_add, Finsupp.add_apply, coord1, add_zero] at hh
    rw [hh, ←hf2, LinearEquiv.apply_symm_apply]
    norm_num [Finsupp.single_apply, Fin.ext_iff]
  have coord2 : f (E.d 2 (14,138) (I.realization.basis .sphere 14 138 2)) 0 = 0 := by
    let coord : E.Page 2 (16,139) →ₗ[ℤ] F2 :=
      (Finsupp.lapply (0 : Fin 3)).comp f.toLinearMap
    have hspan : Submodule.span ℤ {I.realization.basis .sphere 16 139 1,
        I.realization.basis .sphere 16 139 2} ≤ coord.ker := by
      apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · change f (I.realization.basis .sphere 16 139 1) 0 = 0
        rw [← hf1, LinearEquiv.apply_symm_apply]
        norm_num [Finsupp.single_apply, Fin.ext_iff]
      · have hz' := Set.mem_singleton_iff.mp hz
        subst z
        change f (I.realization.basis .sphere 16 139 2) 0 = 0
        rw [← hf2, LinearEquiv.apply_symm_apply]
        norm_num [Finsupp.single_apply, Fin.ext_iff]
    exact hspan hcol
  have one (i : Fin 5) : f (E.d 2 (14,138) (e.symm (Finsupp.single i 1))) 0 = 0 := by
    rw [he]
    fin_cases i
    · exact coord0
    · exact coord1
    · exact coord2
    · simp only [d3, map_zero, Finsupp.zero_apply]
    · simp only [d4, map_zero, Finsupp.zero_apply]
  have all (c : Fin 5 →₀ F2) : f (E.d 2 (14,138) (e.symm c)) 0 = 0 := by
    induction c using Finsupp.induction with
    | zero => simp
    | @single_add i a c hi ha ih =>
      rw [map_add, map_add, map_add, Finsupp.add_apply, ih, add_zero]
      fin_cases a
      · simp
      · exact one i
  have image_zero (a : E.Page 2 (14,138)) : f (E.d 2 (14,138) a) 0 = 0 := by
    simpa only [LinearEquiv.symm_apply_apply] using all (e a)
  obtain ⟨hdeg,x3,y3,hx3,hy3,hd3⟩ := h324
  have yn : y3 ≠ 0 := by
    intro hy0
    obtain ⟨_,z,hz,hzy⟩ := hy3
    have hm := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega)
      (14,138) z).mp (hzy.trans hy0)
    change (Subobject.ofLE _ _ _ ≫ (E.ssData (16,139)).pageπ 0) z ∈
      LinearMap.range (E.d 2 (14,138)).hom at hm
    change (Subobject.ofLE _ _ _ ≫ (E.ssData (16,139)).pageπ 0) z =
      I.realization.basis .sphere 16 139 0 at hz
    rw [hz] at hm
    obtain ⟨a,ha⟩ := hm
    have hzero := image_zero a
    rw [ha, ←hf0, LinearEquiv.apply_symm_apply] at hzero
    norm_num at hzero
  have hd : HasNonzeroDifferential E 3 (13,137) (16,139)
      (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) :=
    ⟨hdeg,x3,y3,hx3,hy3,hd3,yn⟩
  have source_label : I.realization.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12)) =
      I.realization.basis .sphere 13 137 2 := by
    have hc := I.csv ⟨.sphere, 13, 137, ["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩
      (by exact List.getElem_mem (l := Raw.degrees) (n := 208) (by decide)) rfl
    obtain ⟨z,hz,he⟩ := hc (2 : Fin 4)
    have heq : (mulAt (atom .h4) (atom .x_109_12)) = z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨7,by decide⟩ * generator ⟨275,by decide⟩ = projection (monomialOfString "7,1,275,1")
      have hs : "7,1,275,1" ≠ "" := by decide
      have hp : (("7,1,275,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [7, 1, 275, 1] := by
        have split : "7,1,275,1".splitOn "," = ["7", "1", "275", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
    rw [heq]
    exact he
  have target_label : I.realization.sphere 16 139 (mulAt dataH1 (atom .x_122_15_2)) =
      I.realization.basis .sphere 16 139 0 := by
    have hc := I.csv ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩
      (by exact List.getElem_mem (l := Raw.degrees) (n := 230) (by decide)) rfl
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 3)
    have heq : (mulAt dataH1 (atom .x_122_15_2)) = z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨1,by decide⟩ * generator ⟨424,by decide⟩ = projection (monomialOfString "1,1,424,1")
      have hs : "1,1,424,1" ≠ "" := by decide
      have hp : (("1,1,424,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1, 1, 424, 1] := by
        have split : "1,1,424,1".splitOn "," = ["1", "1", "424", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
    rw [heq]
    exact he
  change HasNonzeroDifferential E 3 (13,137) (16,139)
    (I.realization.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12)))
    (I.realization.sphere 16 139 (mulAt dataH1 (atom .x_122_15_2)))
  rw [source_label, target_label]
  exact hd

/-- A zero remaining column is a sufficient special case of the coordinate condition. -/
private theorem h4_d3_nonzero_of_remaining_column (I : Inputs D L G)
    (hcol : (sequence D .sphere).d 2 (14,138)
      (I.realization.basis .sphere 14 138 2) = 0) :
    Derived.Differential I.realization 3 (mulAt (atom .h4) (atom .x_109_12))
      (mulAt dataH1 (atom .x_122_15_2)) := by
  apply h4_d3_nonzero_of_remaining_span I
  rw [hcol]
  exact Submodule.zero_mem _

/-- The complete local sphere interface now has an explicit derivation goal
on the same interpretation.  No historical global comparison is substituted. -/
theorem sphere_facts (I : Inputs D L G) (V : SphereVanishingLine H) :
    Derived.SphereFacts I.realization := by
  classical
  obtain ⟨hd2h6, hd2x, hVX, hY⟩ := sphere_basic_survival I
  obtain ⟨hMiddle125, hAF11, hAF12, hxH2, stem125_e2_low⟩ := sphere_low_page_vanishing I
  obtain ⟨hD3sq, hD3x1264, hD7source⟩ := sphere_named_differentials I
  obtain ⟨hD2H0six, hH5B, hH1Correction, p_h2_boundary, q_h2_boundary, hTnotH0, hTnotH2⟩ := sphere_product_obstructions I
  obtain ⟨t_permanent_cycle, w_to_e6, w_d6_targets, t_only_incoming⟩ := sphere_t_incoming_and_survival I V
  obtain ⟨hU,hCorrection,hP,hQ⟩ := named_survive1000 I
  refine {
    d2_x_125_8 := hd2x
    d2_h6 := hd2h6
    d2_h0Six_h6 := hD2H0six
    d3_h4_x_109_12 := by
      have remaining_column : (sequence D .sphere).d 2 (14,138)
          (I.realization.basis .sphere 14 138 2) ∈
          Submodule.span ℤ {I.realization.basis .sphere 16 139 1,
            I.realization.basis .sphere 16 139 2} := by
        -- Remaining subgoal of sphere_facts.d3_h4_x_109_12: the last
        -- unconstrained d2 column has zero coordinate along target basis 0.
        -- The other four columns already lie in this span; the helper then
        -- excludes every incoming boundary of the named d3 target on E3.
        -- The full delivery's staircase row 3005 would make this column zero,
        -- but these generic Inputs retain only selected claims. Continue by
        -- deriving this weaker span condition from the same interpretation.
        sorry
      exact h4_d3_nonzero_of_remaining_span I remaining_column
    d3_h0Sq_x_123_13_2 := hD3sq
    d3_x_126_4 := hD3x1264
    d7_source := hD7source
    d3_x_126_6_candidates := d3_x_126_6_candidates I
    w_to_e6 := w_to_e6
    t_permanent_cycle := t_permanent_cycle
    t_only_incoming := t_only_incoming
    w_d6_targets := w_d6_targets
    u_permanent := nonzero_permanent_of_survives1000 V 10 134 (by norm_num) (by norm_num) (by norm_num) _ hU
    correction_permanent := nonzero_permanent_of_survives1000 V 13 137 (by norm_num) (by norm_num) (by norm_num) _ hCorrection
    p_permanent := nonzero_permanent_of_survives1000 V 11 133 (by norm_num) (by norm_num) (by norm_num) _ hP
    q_permanent := nonzero_permanent_of_survives1000 V 12 134 (by norm_num) (by norm_num) (by norm_num) _ hQ
    v_to_e12 := hVX.1
    v_not_hit := hVX.2.1
    y_to_e5 := hY.1
    y_not_hit := by
      have source_six_zero (I : Inputs D L G) :
          Subsingleton ((sequence D .sphere).Page 6 (5,131)) := by
        classical
        let E := sequence D .sphere
        obtain ⟨e, he⟩ := I.basis ⟨.sphere,5,131,["0,3,69,2"]⟩ (by
          exact List.mem_of_getElem? (i := 127) (by rfl))
        change E.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
        change ∀ i : Fin 1, e.symm (Finsupp.single i 1) =
          I.realization.basis .sphere 5 131 i.val at he
        have hz : RepresentsOnPage E 6 (5,131) (I.realization.basis .sphere 5 131 0) 0 :=
          differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide)
            (t_incoming_t_incoming9_zero_h164 I)
        have hall (a : E.Page 6 (5,131)) : a = 0 := by
          obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤6)
            e (fun _ => 0) (by
              intro i
              rw [he i]
              fin_cases i
              exact hz) a
          simpa using hc
        exact ⟨fun a b => (hall a).trans (hall b).symm⟩

      have source_eight_zero (I : Inputs D L G) :
          Subsingleton ((sequence D .sphere).Page 8 (3,129)) := by
        classical
        let E := sequence D .sphere
        obtain ⟨e, he⟩ := I.basis ⟨.sphere,3,129,["0,1,69,2"]⟩ (by
          exact List.mem_of_getElem? (i := 108) (by rfl))
        change E.Page 2 (3,129) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
        change ∀ i : Fin 1, e.symm (Finsupp.single i 1) =
          I.realization.basis .sphere 3 129 i.val at he
        have hz : RepresentsOnPage E 8 (3,129) (I.realization.basis .sphere 3 129 0) 0 :=
          differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide)
            (t_incoming_t_incoming11_zero_h151 I)
        have hall (a : E.Page 8 (3,129)) : a = 0 := by
          obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤8)
            e (fun _ => 0) (by
              intro i
              rw [he i]
              fin_cases i
              exact hz) a
          simpa using hc
        exact ⟨fun a b => (hall a).trans (hall b).symm⟩

      have y_incoming_source_zero_except_nine (I : Inputs D L G) (r : ℤ)
          (hr : 5 ≤ r) (hr9 : r ≠ 9) :
          Subsingleton ((sequence D .sphere).Page r
            ((11,136) - (sequence D .sphere).diffDeg r)) := by
        by_cases hlate : 12 ≤ r
        · change Subsingleton ((sequence D .sphere).Page r (11-r,136-(r-1)))
          exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
            r (11-r) (136-(r-1)) (by omega)
        have hrhi : r ≤ 11 := by omega
        interval_cases r
        · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum
            4 5 6 132 (by decide) (by decide) (t_incoming_t_incoming8_source_four I)
        · exact source_six_zero I
        · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum
            4 7 4 130 (by decide) (by decide) (t_incoming_t_incoming10_source_four I)
        · exact source_eight_zero I
        · exact (hr9 rfl).elim
        · exact vx_empty_page I 1 127 (by
            exact List.mem_of_getElem? (i := 90) (by rfl)) 10 (by decide)
        · exact vx_empty_page I 0 126 (by
            exact List.mem_of_getElem? (i := 77) (by rfl)) 11 (by decide)

      have y_not_hit_except_nine (I : Inputs D L G) (r : ℤ) (hr : 2 ≤ r)
          (hr9 : r ≠ 9) :
          ¬ HitOnPage (sequence D .sphere) r (11,136)
            (I.realization.sphere 11 136 Y) := by
        let E := sequence D .sphere
        rintro ⟨q,h,z,y,hy,hyn,hd⟩
        by_cases hlow : r < 5
        · obtain ⟨x,hx⟩ := page_has_representative hr z
          have hdiff : HasDifferential E r q (11,136) x
              (I.realization.sphere 11 136 Y) := ⟨h,z,y,hx,hy,hd⟩
          have hzero := differential_target_later_zero
            (by change (2:ℤ)≤r; exact hr) hlow hdiff
          obtain ⟨y5,hy5,hyn5⟩ := y_survives_five I
          exact hyn5 (represents_unique hy5 hzero)
        · have hq : q = (11,136) - E.diffDeg r := eq_sub_iff_add_eq.mpr h
          subst q
          haveI := y_incoming_source_zero_except_nine I r (by omega) hr9
          have hz : z = 0 := Subsingleton.elim _ _
          rw [hz, map_zero] at hd
          exact hyn hd.symm
      intro r hr q h y hy hyn z hd
      by_cases hr9 : r = 9
      · subst r
        have hq : q = (2,128) := eq_sub_iff_add_eq.mpr h
        subst q
        change (sequence D .sphere).d 9 (2,128) z = y at hd
        -- The original unresolved case: the actual d9 cannot hit this
        -- nonzero E9 representative of Y. All other lengths are excluded.
        sorry
      · exact y_not_hit_except_nine I r hr hr9 ⟨q,h,z,y,hy,hyn,hd⟩
    x_to_e6 := hVX.2.2.1
    x_not_hit := hVX.2.2.2
    high_e5 := high125_component I
    h5Sq_B_zero := hH5B
    t_not_h0_multiple := hTnotH0
    t_not_h2_multiple := hTnotH2
    x_h2_zero := hxH2
    y_not_h2_multiple := hY.2
    h1_correction_zero := hH1Correction
    p_h2_boundary := p_h2_boundary
    q_h2_boundary := q_h2_boundary
    e2_stem125_low := stem125_e2_low
    e5_stem124_af11 := hAF11
    e4_stem124_af12 := hAF12
    e4_stem125_af12 := hMiddle125.1
    e5_stem125_af13 := hMiddle125.2
  }


end SphereFactsProof


end
end KIP126.Computation.Route
end
