import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
import KIP126.Main.Solution.StageInput
import KIP126.Main.Solution.Computation.Lambda
import KIP126.Main.Solution.DifferentialReduction.Conclusion
import KIP126.Main.Solution.Route.Predicates
import KIP126.Main.Solution.Route.AlphaOne
import KIP126.Main.Solution.Route.Section7

/-! Section 7 on the selected stage witnesses. No new model, A or C is chosen.
The two paper propositions are still proof obligations in Main, never fields
of a model or stage input. Their unfinished proofs remain here in Solution. -/
namespace KIP126.Main.Solution.Route
open KIP126.Core.SpectralSequence.FinitePageCalculus
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Classical.Adams.PageRepresentatives
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route KIP126.Algebra
open KIP126.LinE2 KIP126.Computation.Near126 KIP126.Computation.Route
noncomputable section
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
  {L : Labels H} {G : TmfLabels H} {η : BiHom 1 2 (S_0_0:Syn)}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem stem124_finite_pages_low124_d2_10 (I : KIP126.Computation.Route.Inputs D L G) : (sequence D .sphere).d 2 (10,134) = 0 := by
  classical
  let E := sequence D .sphere
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have h171 : HasDifferential E 4 (6,131) (10,134)
      (I.realization.basis .sphere 6 131 0) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 3) := by
    have hrow := I.results ⟨.sphere,.equation,4,6,131,[0],10,134,[0, 3],"S0_AdamsE2_ss",2492⟩ (by
      exact List.mem_of_getElem? (i := 171) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h172 : HasDifferential E 4 (6,131) (10,134)
      (I.realization.basis .sphere 6 131 1) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 1 + I.realization.basis .sphere 10 134 3 + I.realization.basis .sphere 10 134 4) := by
    have hrow := I.results ⟨.sphere,.equation,4,6,131,[1],10,134,[0, 1, 3, 4],"S0_AdamsE2_ss",2493⟩ (by
      exact List.mem_of_getElem? (i := 172) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h201 : HasDifferential E 2 (8,133) (10,134)
      (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := by
    have hrow := I.results ⟨.sphere,.equation,2,8,133,[1],10,134,[2, 4],"S0_AdamsE2_ss",2630⟩ (by
      exact List.mem_of_getElem? (i := 201) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (8,133) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h250 : HasDifferential E 5 (10,134) (15,138)
      (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := by
    have hrow := I.results ⟨.sphere,.equation,5,10,134,[3],15,138,[1],"S0_AdamsE2_ss",2694⟩ (by
      exact List.mem_of_getElem? (i := 250) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (10,134) (15,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h249 : ReachesPage E 1000 (10,134) (I.realization.basis .sphere 10 134 4) := by
    have hrow := I.results ⟨.sphere,.reaches,1000,10,134,[4],10,134,[],"S0_AdamsE2_ss",2693⟩ (by
      exact List.mem_of_getElem? (i := 249) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [4] = true := rfl
    simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
    rw [← ha] at h
    exact h
  have d03 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
    (hrep2 _) (show ReachesPage E 4 (10,134) _ from ⟨h171.choose_spec.choose_spec.choose, h171.choose_spec.choose_spec.choose_spec.2.1⟩)
  have d0134 : E.d 2 (10,134) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 1 + I.realization.basis .sphere 10 134 3 + I.realization.basis .sphere 10 134 4) = 0 := by
    obtain ⟨_,xr,yr,hxr,hyr,_⟩ := h172
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨yr,hyr⟩
  have d24 : E.d 2 (10,134) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) = 0 := by
    obtain ⟨_,hd⟩ := h201.eq_on_page_two
    change E.d 2 (8,133) (I.realization.basis .sphere 8 133 1) = _ at hd
    rw [← hd]
    exact congrArg (fun f => f (I.realization.basis .sphere 8 133 1)) (E.d_comp_d 2 (8,133))
  have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000) (hrep2 _) h249
  have d3 : E.d 2 (10,134) (I.realization.basis .sphere 10 134 3) = 0 := by
    obtain ⟨_,xr,yr,hxr,hyr,_⟩ := h250
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) (hrep2 _) ⟨xr,hxr⟩
  have d0 : E.d 2 (10,134) (I.realization.basis .sphere 10 134 0) = 0 := by simpa only [map_add,d3,add_zero] using d03
  have d1 : E.d 2 (10,134) (I.realization.basis .sphere 10 134 1) = 0 := by simpa only [map_add,d0,d3,d4,zero_add,add_zero] using d0134
  have d2 : E.d 2 (10,134) (I.realization.basis .sphere 10 134 2) = 0 := by simpa only [map_add,d4,add_zero] using d24
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,134,["389,1","388,1","1,1,366,1","0,1,373,1","0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Core.Algebra.F2) at e
  change ∀i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 134 i.val at he
  have hone (i : Fin 5) : E.d 2 (10,134) (e.symm (Finsupp.single i 1)) = 0 := by
    rw [he]
    fin_cases i
    · exact d0
    · exact d1
    · exact d2
    · exact d3
    · exact d4
  have hall (f : Fin 5 →₀ KIP126.Core.Algebra.F2) : E.d 2 (10,134) (e.symm f) = 0 := by
    induction f using Finsupp.induction with
    | zero => simp
    | @single_add i a f hi ha ih =>
      rw [map_add,map_add,ih,add_zero]
      fin_cases a
      · simp
      · exact hone i
  ext x
  simpa only [LinearEquiv.symm_apply_apply,ModuleCat.hom_zero,LinearMap.zero_apply] using hall (e x)


private theorem stem124_finite_pages_f2_three (f : Fin 3 →₀ F2) :
    f = 0 ∨ f = Finsupp.single 0 1 ∨ f = Finsupp.single 1 1 ∨
    f = Finsupp.single 2 1 ∨ f = Finsupp.single 0 1 + Finsupp.single 1 1 ∨
    f = Finsupp.single 0 1 + Finsupp.single 2 1 ∨
    f = Finsupp.single 1 1 + Finsupp.single 2 1 ∨
    f = Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1 := by
  classical
  have hf : f = Finsupp.single 0 (f 0) + Finsupp.single 1 (f 1) + Finsupp.single 2 (f 2) := by
    ext i
    fin_cases i <;> simp
  generalize h0 : f 0 = a at hf
  generalize h1 : f 1 = b at hf
  generalize h2 : f 2 = c at hf
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals simp only [show (⟨0,by decide⟩ : F2) = 0 from rfl, show (⟨1,by decide⟩ : F2) = 1 from rfl, Finsupp.single_zero, zero_add, add_zero] at hf
  all_goals subst f; tauto


private theorem stem124_finite_pages_low124_af9_four (I : KIP126.Computation.Route.Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (9,133)) ∧
    (∀ y : (sequence D .sphere).Page 4 (12,135),
      RepresentsOnPage (sequence D .sphere) 4 (12,135) (I.realization.basis .sphere 12 135 2) y → y ≠ 0) ∧
    ∀ x : (sequence D .sphere).Page 2 (9,133), (sequence D .sphere).d 2 (9,133) x = 0 ∨
      (sequence D .sphere).d 2 (9,133) x = I.realization.basis .sphere 11 134 4 := by
  classical
  let E := sequence D .sphere
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {xr yr : E.Page r p}
      (hx : RepresentsOnPage E r p x xr) (hy : RepresentsOnPage E r p y yr) :
      RepresentsOnPage E r p (x+y) (xr+yr) := by
    exact represents_add_tail (by assumption) (by assumption)
  have h221 : HasDifferential E 3 (9,133) (12,135)
      (I.realization.basis .sphere 9 133 1 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 0) := by
    have hrow := I.results ⟨.sphere,.equation,3,9,133,[1, 2],12,135,[0],"S0_AdamsE2_ss",2626⟩ (by
      exact List.mem_of_getElem? (i := 221) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,133) (12,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1, 2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h222 : HasDifferential E 3 (9,133) (12,135)
      (I.realization.basis .sphere 9 133 0 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 1 + I.realization.basis .sphere 12 135 2) := by
    have hrow := I.results ⟨.sphere,.equation,3,9,133,[0, 2],12,135,[1, 2],"S0_AdamsE2_ss",2627⟩ (by
      exact List.mem_of_getElem? (i := 222) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,133) (12,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [0, 2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [1, 2] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h223 : HasDifferential E 2 (9,133) (11,134)
      (I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 11 134 4) := by
    have hrow := I.results ⟨.sphere,.equation,2,9,133,[2],11,134,[4],"S0_AdamsE2_ss",2628⟩ (by
      exact List.mem_of_getElem? (i := 223) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (9,133) (11,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 134 [4] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,133,["374,1", "373,1", "0,1,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 172) (by rfl))
  change E.Page 2 (9,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 133 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,11,134,["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl))
  change E.Page 2 (11,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 134 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,12,135,["408,1", "0,1,386,1", "0,2,69,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  change E.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at g
  change ∀ i : Fin 3, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 135 i.val at hg
  have e0 : e.symm (Finsupp.single 0 1) = I.realization.basis .sphere 9 133 0 := he 0
  have e1 : e.symm (Finsupp.single 1 1) = I.realization.basis .sphere 9 133 1 := he 1
  have e2 : e.symm (Finsupp.single 2 1) = I.realization.basis .sphere 9 133 2 := he 2
  have f4 : f.symm (Finsupp.single 4 1) = I.realization.basis .sphere 11 134 4 := hf 4
  have g0 : g.symm (Finsupp.single 0 1) = I.realization.basis .sphere 12 135 0 := hg 0
  have g1 : g.symm (Finsupp.single 1 1) = I.realization.basis .sphere 12 135 1 := hg 1
  have g2 : g.symm (Finsupp.single 2 1) = I.realization.basis .sphere 12 135 2 := hg 2
  have ht2 : I.realization.basis .sphere 11 134 4 + I.realization.basis .sphere 11 134 4 = 0 := by
    rw [← f4,← f.symm.map_add,← Finsupp.single_add,show (1:F2)+1=0 from rfl,Finsupp.single_zero,map_zero]
  have he22 : I.realization.basis .sphere 9 133 2 + I.realization.basis .sphere 9 133 2 = 0 := by
    rw [← e2,← e.symm.map_add,← Finsupp.single_add,show (1:F2)+1=0 from rfl,Finsupp.single_zero,map_zero]
  have htne : I.realization.basis .sphere 11 134 4 ≠ 0 := by
    intro h
    have hh := congrArg (fun x => f x 4) h
    rw [← f4,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  obtain ⟨_,v,a,hv,ha,dv⟩ := h221
  obtain ⟨_,w,b,hw,hb,dw⟩ := h222
  have d2v := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨v,hv⟩
  have d2w := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨w,hw⟩
  have d22 : E.d 2 (9,133) (I.realization.basis .sphere 9 133 2) = I.realization.basis .sphere 11 134 4 := by
    obtain ⟨_,hd⟩ := h223.eq_on_page_two
    exact hd
  have d20 : E.d 2 (9,133) (I.realization.basis .sphere 9 133 0) = I.realization.basis .sphere 11 134 4 := by
    have hh := congrArg (fun z => z + I.realization.basis .sphere 11 134 4) d2w
    simpa only [map_add,d22,add_assoc,ht2,add_zero,zero_add] using hh
  have d21 : E.d 2 (9,133) (I.realization.basis .sphere 9 133 1) = I.realization.basis .sphere 11 134 4 := by
    have hh := congrArg (fun z => z + I.realization.basis .sphere 11 134 4) d2v
    simpa only [map_add,d22,add_assoc,ht2,add_zero,zero_add] using hh
  have hker2 (x : E.Page 2 (9,133)) (hx : E.d 2 (9,133) x = 0) :
      x = 0 ∨ x = I.realization.basis .sphere 9 133 1 + I.realization.basis .sphere 9 133 2 ∨
      x = I.realization.basis .sphere 9 133 0 + I.realization.basis .sphere 9 133 2 ∨
      x = (I.realization.basis .sphere 9 133 1 + I.realization.basis .sphere 9 133 2) +
        (I.realization.basis .sphere 9 133 0 + I.realization.basis .sphere 9 133 2) := by
    rcases stem124_finite_pages_f2_three (e x) with h|h|h|h|h|h|h|h
    all_goals have hh := congrArg e.symm h
    all_goals simp only [LinearEquiv.symm_apply_apply,map_zero,map_add,e0,e1,e2] at hh
    · exact Or.inl hh
    · exact (htne (by simpa only [hh,d20] using hx)).elim
    · exact (htne (by simpa only [hh,d21] using hx)).elim
    · exact (htne (by simpa only [hh,d22] using hx)).elim
    · right; right; right
      rw [hh]
      calc
        _ = (I.realization.basis .sphere 9 133 0 + I.realization.basis .sphere 9 133 1) +
          (I.realization.basis .sphere 9 133 2 + I.realization.basis .sphere 9 133 2) := by rw [he22,add_zero]
        _ = _ := by abel
    · exact Or.inr (Or.inr (Or.inl hh))
    · exact Or.inr (Or.inl hh)
    · exact (htne (by simpa only [hh,map_add,d20,d21,d22,ht2,zero_add] using hx)).elim
  have frame (x : E.Page 3 (9,133)) : x=0 ∨ x=v ∨ x=w ∨ x=v+w := by
    let A := E.ssData (9,133)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance x
    let x0 : E.Page 2 (9,133) := (Subobject.ofLE (A.Z 1) (A.Z 0) (A.Z_anti (by decide)) ≫ A.pageπ 0) z
    have hr : RepresentsOnPage E 3 (9,133) x0 x := ⟨by decide,z,rfl,hz⟩
    have hd0 : E.d 2 (9,133) x0 = 0 := by
      change x0 ∈ LinearMap.ker (E.d 2 (9,133)).hom
      rw [← subobjectModule_kernel,E.Z_succ 2 (9,133) (by change (2:ℤ)≤2; omega),subobjectModule_image]
      exact ⟨z,rfl⟩
    rcases hker2 x0 hd0 with h0|h0|h0|h0
    · exact Or.inl (represents_unique (E := E) (h0 ▸ hr) (RepresentsOnPage.zero (by decide)))
    · exact Or.inr (Or.inl (represents_unique (E := E) (h0 ▸ hr) hv))
    · exact Or.inr (Or.inr (Or.inl (represents_unique (E := E) (h0 ▸ hr) hw)))
    · exact Or.inr (Or.inr (Or.inr (represents_unique (E := E) (h0 ▸ hr) (hadd hv hw))))
  have reflect {x : E.Page 2 (12,135)} {y : E.Page 3 (12,135)}
      (h : RepresentsOnPage E 3 (12,135) x y) (hy : y=0) : x=0 := by
    obtain ⟨_,z,hx,hz⟩ := h
    have hp := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (10,134) z).mp (hz.trans hy)
    change (Subobject.ofLE _ _ ((E.ssData (12,135)).Z_anti bot_le) ≫ (E.ssData (12,135)).pageπ 0) z ∈ LinearMap.range (E.d 2 (10,134)).hom at hp
    change (Subobject.ofLE _ _ ((E.ssData (12,135)).Z_anti bot_le) ≫ (E.ssData (12,135)).pageπ 0) z = x at hx
    rw [hx] at hp
    obtain ⟨u,hu⟩ := hp
    rw [stem124_finite_pages_low124_d2_10 I] at hu
    exact hu.symm
  have ane : a ≠ 0 := by
    intro hz
    have hh := congrArg (fun x => g x 0) (reflect ha hz)
    rw [← g0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have bne : b ≠ 0 := by
    intro hz
    have hh := congrArg (fun x => g x 1) (reflect hb hz)
    rw [← g1,← g2,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have abne : a+b ≠ 0 := by
    intro hz
    have hh := congrArg (fun x => g x 0) (reflect (hadd ha hb) hz)
    rw [← g0,← g1,← g2,map_add,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have dv' : E.d 3 (9,133) v = a := dv
  have dw' : E.d 3 (9,133) w = b := dw
  have hker3 (x : E.Page 3 (9,133)) (hx : E.d 3 (9,133) x=0) : x=0 := by
    rcases frame x with h|h|h|h
    · exact h
    · exact (ane (by simpa only [h,dv'] using hx)).elim
    · exact (bne (by simpa only [h,dw'] using hx)).elim
    · exact (abne (by simpa only [h,map_add,dv',dw'] using hx)).elim
  let S := E.pageShortComplex 3 ((9,133)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [hker3 x hx,map_zero]⟩)
  refine ⟨ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (9,133)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs)), ?_, ?_⟩
  intro y hrep hy
  obtain ⟨_,z,hx,hz⟩ := hrep
  let A := E.ssData (12,135)
  let z1 := (Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide))) z
  have hr3 : RepresentsOnPage E 3 (12,135) (I.realization.basis .sphere 12 135 2) (A.pageπ 1 z1) := by
    refine ⟨by decide,z1,?_,rfl⟩
    change (Subobject.ofLE (A.Z 1) (A.Z 0) (A.Z_anti bot_le) ≫ A.pageπ 0) z1 = _
    dsimp only [z1]
    rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hx
  have hi := (next_projection_zero_iff_incoming E 3 (by change (2:ℤ)≤3; omega) (9,133) z).mp (hz.trans hy)
  change ∃ u, E.d 3 (9,133) u = A.pageπ 1 z1 at hi
  obtain ⟨u,hu⟩ := hi
  have hsub {x x' : E.Page 2 (12,135)} {a a' : E.Page 3 (12,135)}
      (hx : RepresentsOnPage E 3 (12,135) x a) (hx' : RepresentsOnPage E 3 (12,135) x' a') :
      RepresentsOnPage E 3 (12,135) (x-x') (a-a') := by
    exact represents_sub_tail (by assumption) (by assumption)
  rcases frame u with hu0|hu0|hu0|hu0
  · have hn := reflect hr3 (by rw [← hu,hu0,map_zero])
    have hh := congrArg (fun x => g x 2) hn
    rw [← g2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · have hn := reflect (hsub hr3 ha) (sub_eq_zero.mpr (by rw [← hu,hu0,dv']))
    have hh := congrArg (fun x => g x 2) hn
    rw [← g2,← g0,map_sub,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · have hn := reflect (hsub hr3 hb) (sub_eq_zero.mpr (by rw [← hu,hu0,dw']))
    have hh := congrArg (fun x => g x 1) hn
    rw [← g2,← g1,map_sub,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · have hn := reflect (hsub hr3 (hadd ha hb)) (sub_eq_zero.mpr (by rw [← hu,hu0,map_add,dv',dw']))
    have hh := congrArg (fun x => g x 0) hn
    rw [← g2,← g1,← g0,map_sub,map_add,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  intro x
  change E.d 2 (9,133) x = 0 ∨ E.d 2 (9,133) x = I.realization.basis .sphere 11 134 4
  rcases stem124_finite_pages_f2_three (e x) with h|h|h|h|h|h|h|h
  all_goals have hh := congrArg e.symm h
  all_goals simp only [LinearEquiv.symm_apply_apply,map_zero,map_add,e0,e1,e2] at hh
  all_goals simp only [hh,map_zero,map_add,d20,d21,d22,ht2,zero_add,add_zero]; tauto


private theorem stem124_finite_pages_s8_d2 (I : KIP126.Computation.Route.Inputs D L G) :
    (sequence D .sphere).d 2 (8,132) (I.realization.basis .sphere 8 132 0) =
      I.realization.basis .sphere 10 133 2 := by
  classical
  let E := sequence D .sphere
  have hrow := I.results
    ⟨.sphere, .equation, 2, 8, 132, [0], 10, 133, [2], "S0_AdamsE2_ss", 2571⟩ (by
      exact List.mem_of_getElem? (i := 199) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x, hx, y, hy, h⟩ := hrow
  change I.realization.decode .sphere 8 132 [0] = some x at hx
  change I.realization.decode .sphere 10 133 [2] = some y at hy
  change HasDifferential E 2 (8,132) (10,133) x y at h
  have hx' : x = I.realization.basis .sphere 8 132 0 := by
    have hv : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0] = true := by decide
    exact Option.some.inj (hx.symm.trans (by simp [Realization.decode, hv]))
  have hy' : y = I.realization.basis .sphere 10 133 2 := by
    have hv : Raw.coordinatesValid Raw.degrees .sphere 10 133 [2] = true := by decide
    exact Option.some.inj (hy.symm.trans (by simp [Realization.decode, hv]))
  have hd : E.d 2 (8,132) (I.realization.basis .sphere 8 132 0) =
      I.realization.basis .sphere 10 133 2 := by
    obtain ⟨_, hd⟩ := h.eq_on_page_two
    have hd' : E.d 2 (8,132) x = y := by exact hd
    rw [hx', hy'] at hd'
    exact hd'
  exact hd


private theorem stem124_finite_pages_s8_basis (I : KIP126.Computation.Route.Inputs D L G) : ∃ e : (sequence D .sphere).Page 2 (8,132) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2), ∀i, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 8 132 i.val := by
  classical
  let E := sequence D .sphere
  obtain ⟨e, he⟩ := I.basis ⟨.sphere, 8, 132, ["367,1"]⟩ (by
      exact List.mem_of_getElem? (i := 160) (by rfl))
  change E.Page 2 (8,132) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 8 132 i.val at he
  exact ⟨e,he⟩


private theorem stem124_finite_pages_s10_basis (I : KIP126.Computation.Route.Inputs D L G) : ∃ f : (sequence D .sphere).Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Core.Algebra.F2), ∀i, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 133 i.val := by
  classical
  let E := sequence D .sphere
  obtain ⟨f, hf⟩ := I.basis ⟨.sphere, 10, 133, ["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
      exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Core.Algebra.F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 133 i.val at hf
  exact ⟨f,hf⟩


private theorem stem124_finite_pages_low124_af8_three (I : KIP126.Computation.Route.Inputs D L G) : Subsingleton ((sequence D .sphere).Page 3 (8,132)) := by
  classical
  let E := sequence D .sphere
  have hd := stem124_finite_pages_s8_d2 I
  obtain ⟨e, he⟩ := stem124_finite_pages_s8_basis I
  obtain ⟨f,hf⟩ := stem124_finite_pages_s10_basis I
  have hf2 : f.symm (Finsupp.single 2 1) = I.realization.basis .sphere 10 133 2 := hf 2
  have he0 : e.symm (Finsupp.single 0 1) = I.realization.basis .sphere 8 132 0 := he 0
  have hn : I.realization.basis .sphere 10 133 2 ≠ 0 := by
    rw [← hf2]
    intro hzero
    have hz := congrArg (fun y => f y 2) hzero
    simpa using hz
  have hde : ∀ z, E.d 2 (8,132) (e.symm z) = 0 → z = 0 := by
    intro z hz
    have hzrepr : z = Finsupp.single 0 (z 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    rw [hzrepr] at hz
    have hc : z 0 = 0 ∨ z 0 = 1 := by generalize z 0 = a; fin_cases a <;> simp
    rcases hc with hc | hc
    · rw [hzrepr, hc, Finsupp.single_zero]
    · rw [hc, he0, hd] at hz
      exact (hn hz).elim
  have hinj : Function.Injective (E.d 2 (8,132)) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    apply e.injective
    simpa using hde (e z) (by simpa using hz)
  let S := E.pageShortComplex 2 ((8,132)-E.diffDeg 2)
  have hs : Function.Injective S.g := hinj
  have hsex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro z hz
    have hz0 : z = 0 := hs (hz.trans (map_zero _).symm)
    exact ⟨0, by simpa [hz0]⟩)
  have hzero := (S.exact_iff_isZero_homology).mp hsex
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 2 (8,132)
    (by change (2:ℤ)≤2; omega)).isZero_iff.mpr hzero)


private theorem stem124_finite_pages_low124_s7_four (I : KIP126.Computation.Route.Inputs D L G) :
    ∃ b : (sequence D .sphere).Page 4 (7,131),
      RepresentsOnPage (sequence D .sphere) 4 (7,131) (I.realization.basis .sphere 7 131 1) b ∧
      (∀ a : (sequence D .sphere).Page 4 (7,131), a=0 ∨ a=b) ∧
      (sequence D .sphere).d 4 (7,131) = 0 := by
  classical
  let E := sequence D .sphere
  have h163 : HasDifferential E 2 (5,130) (7,131)
      (I.realization.basis .sphere 5 130 0) (I.realization.basis .sphere 7 131 2) := by
    have hrow := I.results ⟨.sphere,.equation,2,5,130,[0],7,131,[2],"S0_AdamsE2_ss",2435⟩ (by
      exact List.mem_of_getElem? (i := 163) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (5,130) (7,131) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h182 : HasDifferential E 5 (7,131) (12,135)
      (I.realization.basis .sphere 7 131 1) (I.realization.basis .sphere 12 135 2) := by
    have hrow := I.results ⟨.sphere,.equation,5,7,131,[1],12,135,[2],"S0_AdamsE2_ss",2490⟩ (by
      exact List.mem_of_getElem? (i := 182) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (7,131) (12,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  have h183 : HasDifferential E 3 (7,131) (10,133)
      (I.realization.basis .sphere 7 131 0) (I.realization.basis .sphere 10 133 0 + I.realization.basis .sphere 10 133 1) := by
    have hrow := I.results ⟨.sphere,.equation,3,7,131,[0],10,133,[0, 1],"S0_AdamsE2_ss",2491⟩ (by
      exact List.mem_of_getElem? (i := 183) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (7,131) (10,133) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0, 1] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,7,131,["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 131 i.val at he
  obtain ⟨f,hf⟩ := stem124_finite_pages_s8_basis I
  obtain ⟨g,hg⟩ := stem124_finite_pages_s10_basis I
  have g0 : g.symm (Finsupp.single 0 1) = I.realization.basis .sphere 10 133 0 := hg 0
  have g1 : g.symm (Finsupp.single 1 1) = I.realization.basis .sphere 10 133 1 := hg 1
  have g2 : g.symm (Finsupp.single 2 1) = I.realization.basis .sphere 10 133 2 := hg 2
  obtain ⟨_,a,c,ha,hc,hd⟩ := h183
  obtain ⟨_,b5,z5,hb5,hz5,hd5⟩ := h182
  obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) hb5
  have htzero : RepresentsOnPage E 3 (7,131) (I.realization.basis .sphere 7 131 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h163
  have hcn : c ≠ 0 := by
    intro hc0
    obtain ⟨_,z,hx,hz⟩ := hc
    have hin := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (8,132) z).mp (hz.trans hc0)
    change ∃ u, E.d 2 (8,132) u = (Subobject.ofLE _ _ ((E.ssData (10,133)).Z_anti bot_le) ≫ (E.ssData (10,133)).pageπ 0) z at hin
    change (Subobject.ofLE _ _ ((E.ssData (10,133)).Z_anti bot_le) ≫ (E.ssData (10,133)).pageπ 0) z = _ at hx
    rw [hx] at hin
    obtain ⟨u,hu⟩ := hin
    have hrepr : f u = Finsupp.single 0 ((f u) 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have hu0 : u = f.symm (Finsupp.single 0 ((f u) 0)) := by
      rw [← hrepr,LinearEquiv.symm_apply_apply]
    rw [hu0] at hu
    generalize hcoef : (f u) 0 = v at hu
    fin_cases v
    · simp only [show (⟨0,by decide⟩ : KIP126.Core.Algebra.F2)=0 from rfl,Finsupp.single_zero,map_zero] at hu
      have hh := congrArg (fun q => g q 0) hu
      rw [← g0,← g1,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change E.d 2 (8,132) (f.symm (Finsupp.single 0 1)) = _ at hu
      have f0 : f.symm (Finsupp.single 0 1) = I.realization.basis .sphere 8 132 0 := hf 0
      have hs8 : E.d 2 (8,132) (I.realization.basis .sphere 8 132 0) = I.realization.basis .sphere 10 133 2 := stem124_finite_pages_s8_d2 I
      rw [f0,hs8] at hu
      have hh := congrArg (fun q => g q 0) hu
      rw [← g0,← g1,← g2,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have frame3 (x : E.Page 3 (7,131)) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    let v : Fin 3 → E.Page 3 (7,131) := ![a,b,0]
    have hv (i : Fin 3) : RepresentsOnPage E 3 (7,131) (e.symm (Finsupp.single i 1)) (v i) := by
      rw [he i]
      fin_cases i
      · exact ha
      · exact hb
      · exact htzero
    obtain ⟨coeff,hcoeff⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e v hv x
    simp only [Fin.sum_univ_three] at hcoeff
    change x = (if coeff 0=0 then 0 else a) + (if coeff 1=0 then 0 else b) + (if coeff 2=0 then 0 else 0) at hcoeff
    by_cases h0 : coeff 0 = 0 <;> by_cases h1 : coeff 1 = 0
    all_goals simp only [h0,h1,ite_true,ite_false,ite_self,add_zero,zero_add] at hcoeff
    · exact Or.inl hcoeff
    · exact Or.inr (Or.inr (Or.inl hcoeff))
    · exact Or.inr (Or.inl hcoeff)
    · exact Or.inr (Or.inr (Or.inr hcoeff))
  have hda : E.d 3 (7,131) a = c := hd
  have hdb : E.d 3 (7,131) b = 0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) hb ⟨b5,hb5⟩
  have ker3 (x : E.Page 3 (7,131)) (hx : E.d 3 (7,131) x=0) : x=0 ∨ x=b := by
    rcases frame3 x with h|h|h|h
    · exact Or.inl h
    · exact (hcn (by simpa only [h,hda] using hx)).elim
    · exact Or.inr h
    · exact (hcn (by simpa only [h,map_add,hda,hdb,add_zero] using hx)).elim
  obtain ⟨b4,hb4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hb5
  have hb4save := hb4
  obtain ⟨_,z,hz,hzb⟩ := hb4
  have hz3 : RepresentsOnPage E 3 (7,131) (I.realization.basis .sphere 7 131 1)
      ((Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (1:WithTop ℕ)≤2)) ≫ (E.ssData (7,131)).pageπ 1) z) := by
    refine ⟨by decide, (Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (1:WithTop ℕ)≤2))) z, ?_,rfl⟩
    change ((Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (1:WithTop ℕ)≤2))) ≫ Subobject.ofLE _ _ _ ≫ (E.ssData (7,131)).pageπ 0) z = _
    rw [← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz
  have frame4 (x : E.Page 4 (7,131)) : x=0 ∨ x=b4 := by
    have h := next_page_two_of_kernel E 3 (by change (2:ℤ)≤3; omega) (7,131) z (by
      intro q hq
      have hk := ker3 q hq
      rwa [represents_unique (E := E) hb hz3] at hk) x
    change x=0 ∨ x=(E.ssData (7,131)).pageπ 2 z at h
    change (E.ssData (7,131)).pageπ 2 z=b4 at hzb
    rwa [hzb] at h
  refine ⟨b4,hb4save,frame4,?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases frame4 x with hx|hx
  · simp only [hx,map_zero]
  · rw [hx]
    exact represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) hb4save ⟨b5,hb5⟩


private theorem stem124_finite_pages_low124_s7_six (I : KIP126.Computation.Route.Inputs D L G)
    (h8 : Subsingleton ((sequence D .sphere).Page 4 (8,132)))
    (htarget : ∀ y : (sequence D .sphere).Page 4 (12,135),
      RepresentsOnPage (sequence D .sphere) 4 (12,135) (I.realization.basis .sphere 12 135 2) y → y ≠ 0) :
    Subsingleton ((sequence D .sphere).Page 6 (7,131)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨b4,hb4,frame4,hd4⟩ := stem124_finite_pages_low124_s7_four I
  have h182 : HasDifferential E 5 (7,131) (12,135)
      (I.realization.basis .sphere 7 131 1) (I.realization.basis .sphere 12 135 2) := by
    have hrow := I.results ⟨.sphere,.equation,5,7,131,[1],12,135,[2],"S0_AdamsE2_ss",2490⟩ (by
      exact List.mem_of_getElem? (i := 182) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (7,131) (12,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [← ha,← hb] at h
    simpa only [add_assoc] using h
  obtain ⟨_,b5,c5,hb5,hc5,hd5⟩ := h182
  obtain ⟨c4,hc4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hc5
  have hc4n : c4 ≠ 0 := htarget c4 hc4
  have hin : E.d 4 ((12,135)-E.diffDeg 4) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change E.d 4 (8,132) x = 0
    rw [h8.elim x 0,map_zero]
  have hc5n : c5 ≠ 0 := represents_next_nonzero_of_incoming_zero
    (by change (2:ℤ)≤4; omega) (by decide : (2:ℤ)≤4) hin hc5 hc4 hc4n
  have hb5save := hb5
  obtain ⟨_,z,hz,hzb⟩ := hb5
  have hz4 : RepresentsOnPage E 4 (7,131) (I.realization.basis .sphere 7 131 1)
      ((Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (2:WithTop ℕ)≤3)) ≫ (E.ssData (7,131)).pageπ 2) z) := by
    refine ⟨by decide, (Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (2:WithTop ℕ)≤3))) z, ?_,rfl⟩
    change ((Subobject.ofLE _ _ ((E.ssData (7,131)).Z_anti (by decide : (2:WithTop ℕ)≤3))) ≫ Subobject.ofLE _ _ _ ≫ (E.ssData (7,131)).pageπ 0) z = _
    rw [← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz
  have frame5 (x : E.Page 5 (7,131)) : x=0 ∨ x=b5 := by
    have h := next_page_two_of_kernel E 4 (by change (2:ℤ)≤4; omega) (7,131) z (by
      intro q hq
      have hk := frame4 q
      rwa [represents_unique (E := E) hb4 hz4] at hk) x
    change x=0 ∨ x=(E.ssData (7,131)).pageπ 3 z at h
    change (E.ssData (7,131)).pageπ 3 z=b5 at hzb
    rwa [hzb] at h
  have hd5' : E.d 5 (7,131) b5=c5 := hd5
  have ker5 (x : E.Page 5 (7,131)) (hx : E.d 5 (7,131) x=0) : x=0 := by
    rcases frame5 x with hx0|hxb
    · exact hx0
    · exact (hc5n (by simpa only [hxb,hd5'] using hx)).elim
  let S := E.pageShortComplex 5 ((7,131)-E.diffDeg 5)
  have hex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [ker5 x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 5 (7,131)
    (by change (2:ℤ)≤5; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hex))


private theorem stem124_finite_pages_low124_af6_six (I : KIP126.Computation.Route.Inputs D L G)
    (h74 : (sequence D .sphere).d 4 (7,131) = 0) : Subsingleton ((sequence D .sphere).Page 6 (6,130)) := by
  classical
  let E := sequence D .sphere
  have hrow := I.results ⟨.sphere,.equation,5,6,130,[0],11,134,[2],"S0_AdamsE2_ss",2434⟩ (by
    exact List.mem_of_getElem? (i := 170) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,h⟩ := hrow
  change HasDifferential E 5 (6,130) (11,134) x y at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 134 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [← hx,← hy] at h
  obtain ⟨_,x5,y5,hx5,hy5,hd5⟩ := h
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,6,130,["339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 136) (by rfl))
  change E.Page 2 (6,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 6 130 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,11,134,["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl))
  change E.Page 2 (11,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 134 i.val at hf
  have f2 : f.symm (Finsupp.single 2 1) = I.realization.basis .sphere 11 134 2 := hf 2
  have f4 : f.symm (Finsupp.single 4 1) = I.realization.basis .sphere 11 134 4 := hf 4
  have target3 (z3 : E.Page 3 (11,134))
      (h3 : RepresentsOnPage E 3 (11,134) (I.realization.basis .sphere 11 134 2) z3) : z3 ≠ 0 := by
    intro hz3
    obtain ⟨_,z,hz,hzp⟩ := h3
    have hi := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (9,133) z).mp (hzp.trans hz3)
    change ∃ u, E.d 2 (9,133) u = (Subobject.ofLE _ _ ((E.ssData (11,134)).Z_anti bot_le) ≫ (E.ssData (11,134)).pageπ 0) z at hi
    obtain ⟨u,hu⟩ := hi
    have hlabel : E.d 2 (9,133) u = I.realization.basis .sphere 11 134 2 := hu.trans hz
    rcases (stem124_finite_pages_low124_af9_four I).2.2 u with hu0|hu4
    · have hh := congrArg (fun x => f x 2) (hu0.symm.trans hlabel)
      rw [← f2,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · have hh := congrArg (fun x => f x 2) (hu4.symm.trans hlabel)
      rw [← f2,← f4,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) hy5
  obtain ⟨y4,hy4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy5
  have hin3 : E.d 3 ((11,134)-E.diffDeg 3) = 0 := by
    ext z
    change E.d 3 (8,132) z = 0
    rw [(stem124_finite_pages_low124_af8_three I).elim z 0,map_zero]
  have hy4ne := represents_next_nonzero_of_incoming_zero (by change (2:ℤ)≤3; omega)
    (by decide : (2:ℤ)≤3) hin3 hy4 hy3 (target3 y3 hy3)
  have hin4 : E.d 4 ((11,134)-E.diffDeg 4) = 0 := h74
  have hy5ne := represents_next_nonzero_of_incoming_zero (by change (2:ℤ)≤4; omega)
    (by decide : (2:ℤ)≤4) hin4 hy5 hy4 hy4ne
  have he0 : e.symm (Finsupp.single 0 1) = I.realization.basis .sphere 6 130 0 := he 0
  have hbas (i : Fin 1) : RepresentsOnPage E 5 (6,130) (e.symm (Finsupp.single i 1)) x5 := by
    have hi : i=0 := Fin.eq_zero i
    subst i
    exact he0.symm ▸ hx5
  have frame (z : E.Page 5 (6,130)) : z=0 ∨ z=x5 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (E := E) (r := 5) (p := (6,130))
      (by decide) e (fun _ => x5) hbas z
    simp only [Fin.sum_univ_one] at hc
    split_ifs at hc <;> tauto
  have hd5' : E.d 5 (6,130) x5 = y5 := hd5
  have hker5 (z : E.Page 5 (6,130)) (hz : E.d 5 (6,130) z=0) : z=0 := by
    rcases frame z with hz0|hzx
    · exact hz0
    · exact (hy5ne (by simpa only [hzx,hd5'] using hz)).elim
  let S := E.pageShortComplex 5 ((6,130)-E.diffDeg 5)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro z hz
    exact ⟨0,by rw [hker5 z hz,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 5 (6,130)
    (by change (2:ℤ)≤5; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))


private theorem stem124_finite_pages
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H} (I : KIP126.Computation.Route.Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 6 (6,130)) ∧
    Subsingleton ((sequence D .sphere).Page 6 (7,131)) ∧
    Subsingleton ((sequence D .sphere).Page 3 (8,132)) ∧
    Subsingleton ((sequence D .sphere).Page 4 (9,133)) := by
  classical
  classical
  obtain ⟨b,hb,hcases,h74⟩ := stem124_finite_pages_low124_s7_four I
  have h8 := stem124_finite_pages_low124_af8_three I
  have h9 := stem124_finite_pages_low124_af9_four I
  have h8four := adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 3 4 8 132
    (by omega) (by omega) h8
  exact ⟨stem124_finite_pages_low124_af6_six I h74, stem124_finite_pages_low124_s7_six I h8four h9.2.1, h8, h9.1⟩

private theorem stem124_weight128_filtration_ten_permanent_quotient_zero_of_stable_boundaries
    (X : C) (p : ℤ×ℤ) (b : ℤ)
    (hzero : Subsingleton ((adamsTowerInternalSpectralSequence H.unit X).ssData p).eInfty)
    (hB : ((adamsTowerInternalSpectralSequence H.unit X).ssData p).B ⊤ =
      ((adamsTowerInternalSpectralSequence H.unit X).ssData p).B ↑(b-1).toNat) :
    Subsingleton (PermanentQuotient H X b p) := by
  classical
  let E := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  have heq : LinearMap.range (boundaryMap H X ⊤ p).hom = boundaries H X b p := by
    have hh (B B' : Subobject E.V) (h : B ≤ E.Z 0) (h' : B' ≤ E.Z 0)
        (he : B = B') :
        LinearMap.range (Subobject.ofLE B _ h ≫ E.pageπ 0).hom =
          LinearMap.range (Subobject.ofLE B' _ h' ≫ E.pageπ 0).hom := by
      subst B'
      rfl
    exact hh _ _ _ _ hB
  have hcycles : permanentCycles H X p ≤ boundaries H X b p := by
    rintro x ⟨z,hz⟩
    have hz0 : E.pageπ ⊤ z = 0 := hzero.elim _ _
    obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (E.B ⊤) (E.Z ⊤) (E.B_le_Z ⊤)) z).mp hz0
    rw [← heq]
    refine ⟨y,?_⟩
    have hfactor : Subobject.ofLE (E.B ⊤) (E.Z ⊤) (E.B_le_Z ⊤) ≫
        cycleMap H X ⊤ p = boundaryMap H X ⊤ p := by
      dsimp only [cycleMap,boundaryMap,E]
      rw [← Category.assoc,Subobject.ofLE_comp_ofLE]
    change boundaryMap H X ⊤ p y = x
    rw [← hfactor,CategoryTheory.comp_apply,hy]
    exact hz
  have hall (a : PermanentQuotient H X b p) : a = 0 := by
    obtain ⟨x⟩ := a
    exact (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr (hcycles x.property)
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩


private theorem stem124_weight128_filtration_ten_nu124_low_zero
    (A : KIP126.Literature.Route.SyntheticInputs D) (I : KIP126.Computation.Route.Inputs D L G)
    (s : ℤ) (hs : s < 10)
    (hz : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData
      (s,124+s)).eInfty) :
    Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (s,124+s,128)).eInfty) := by
  classical
  by_cases hw : 128 ≤ 124+s
  · let E := adamsTowerInternalSpectralSequence H.unit (SphereSpectrum (C := C))
    have hin (r : ℤ) (hr : s-2 ≤ r) : E.d r ((s,124+s)-E.diffDeg r) = 0 := by
      have hi : (s,124+s)-E.diffDeg r = (s-r,(s-r)+125) := by
        change (s,124+s)-(r,r-1) = _
        ext <;> dsimp <;> omega
      rw [hi]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact no_outgoing_stem125_low I (s-r) (by omega) r (by omega) a
    have hB := boundaries_top_eq_of_d_eq_zero E (s-2) (by change (2:ℤ)≤s-2; omega)
      (s,124+s) hin
    have hB' : (E.ssData (s,124+s)).B ⊤ =
        (E.ssData (s,124+s)).B ↑(1+(124+s)-128-1).toNat := by
      change (E.ssData (s,124+s)).B ⊤ = (E.ssData (s,124+s)).B ↑(s-2-2).toNat at hB
      simpa only [show s-2-2 = 1+(124+s)-128-1 by omega] using hB
    haveI := stem124_weight128_filtration_ten_permanent_quotient_zero_of_stable_boundaries SphereSpectrum (s,124+s)
      (1+(124+s)-128) hz hB'
    exact (A.eInfty.presentation.nuWindow SphereSpectrum (s,124+s) 128 hw).injective.subsingleton
  · haveI : Subsingleton (nuEInftyModel H (SphereSpectrum (C := C)) (s,124+s) 128) := by
      simp only [nuEInftyModel,hw,ite_false]
      infer_instance
    exact (A.eInfty.presentation.nu SphereSpectrum (s,124+s) 128).injective.subsingleton


private theorem stem124_weight128_filtration_ten
    (A : KIP126.Literature.Route.SyntheticInputs D) (I : KIP126.Computation.Route.Inputs D L G)
    (hc : ∀ s : ℤ, s < 10 → Subsingleton
      ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData (s,s+124)).eInfty)
    (a : BiHom 124 128 (S_0_0 : Syn)) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 10 a := by
  classical
  classical
  apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
    0 10 124 128 (by omega) ?_ a).mp
  · refine ⟨a,?_⟩
    change a ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 0 _ = a
    rw [adamsTowerMap_self]
    change a ≫ 𝟙 _ = a
    exact Category.comp_id a
  · intro s hs hs10
    have hz : Subsingleton
        ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData (s,124+s)).eInfty := by
      simpa only [add_comm] using hc s hs10
    haveI := stem124_weight128_filtration_ten_nu124_low_zero A I s hs10 hz
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (s,124+s,128)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (s,124+s,128)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (s,124+s,128)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [← SpectralSequenceMorphism.eInftyMap_comp,← Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

private theorem stem124_af13_exhaustion_af13_labels (I : KIP126.Computation.Route.Inputs D L G) :
    I.realization.sphere 13 137 correction = I.realization.basis .sphere 13 137 1 ∧
    I.realization.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12)) = I.realization.basis .sphere 13 137 2 := by
  classical
  have hmem : (⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
    exact List.mem_of_getElem? (i := 208) (by rfl)
  have hc := I.csv _ hmem rfl
  constructor
  · obtain ⟨z,hz,he⟩ := hc (1 : Fin 4)
    have heq : correction = z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨9, by decide⟩ * generator ⟨251, by decide⟩ = projection (monomialOfString "9,1,251,1")
      have hs : "9,1,251,1" ≠ "" := by decide
      have hp : (("9,1,251,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [9,1,251,1] := by
        have split : "9,1,251,1".splitOn "," = ["9", "1", "251", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString, if_neg hs, hp]
      norm_num [polynomialOfPowers, RawData.generatorCount, generator, map_mul]
    rw [heq]
    exact he
  · obtain ⟨z,hz,he⟩ := hc (2 : Fin 4)
    have heq : mulAt (atom .h4) (atom .x_109_12) = z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨7, by decide⟩ * generator ⟨275, by decide⟩ = projection (monomialOfString "7,1,275,1")
      have hs : "7,1,275,1" ≠ "" := by decide
      have hp : (("7,1,275,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [7,1,275,1] := by
        have split : "7,1,275,1".splitOn "," = ["7", "1", "275", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString, if_neg hs, hp]
      norm_num [polynomialOfPowers, RawData.generatorCount, generator, map_mul]
    rw [heq]
    exact he


private theorem stem124_af13_exhaustion
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H} (I : KIP126.Computation.Route.Inputs D L G) (V : SphereVanishingLine H) :
    KIP126.Kervaire.Route.Section7.ClassicalInfinityGenerated 13 137
      (I.realization.sphere 13 137 correction) := by
  classical
  classical
  let E := sequence D .sphere
  let A := E.ssData (13,137)
  obtain ⟨hl1,hl2⟩ := stem124_af13_exhaustion_af13_labels I
  have facts := sphere_facts I V
  obtain ⟨z,hz,hzn⟩ := facts.correction_permanent
  change (Subobject.ofLE (A.Z ⊤) (A.Z 0) (A.Z_anti le_top) ≫ A.pageπ 0) z = _ at hz
  change A.pageπ ⊤ z ≠ 0 at hzn
  have h321 : HasDifferential E 2 (11,136) (13,137)
      (I.realization.basis .sphere 11 136 4) (I.realization.basis .sphere 13 137 3) := by
    have hrow := I.results ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2914⟩ (by
      exact List.mem_of_getElem? (i := 321) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,136) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h322 : HasDifferential E 3 (10,135) (13,137)
      (I.realization.basis .sphere 10 135 0) (I.realization.basis .sphere 13 137 0) := by
    have hrow := I.results ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2915⟩ (by
      exact List.mem_of_getElem? (i := 322) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (10,135) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  obtain ⟨_,incoming,a,hincoming,ha,hda⟩ := h322
  have hd2 := facts.d3_h4_x_109_12
  change HasNonzeroDifferential E 3 (13,137) (16,139)
    (I.realization.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12))) _ at hd2
  rw [hl2] at hd2
  obtain ⟨_,c,t,hc,ht,hdc,htn⟩ := hd2
  have hdc' : E.d 3 (13,137) c = t := hdc
  have hda' : E.d 3 (10,135) incoming = a := hda
  let down (r : ℤ) := Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-2).toNat) (A.Z_anti le_top)
  let val (r : ℤ) := down r ≫ A.pageπ ↑(r-2).toNat
  have rep (r : ℤ) (hr : 2 ≤ r) (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat.{v} ℤ)) :
      RepresentsOnPage E r (13,137) (val 2 q) (val r q) := by
    refine ⟨hr, down r q, ?_, rfl⟩
    change (Subobject.ofLE _ _ _ ≫ A.pageπ 0) ((down r) q) = val 2 q
    dsimp only [val, down]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    rfl
  let b : E.Page 3 (13,137) := val 3 z
  have hb : RepresentsOnPage E 3 (13,137) (I.realization.basis .sphere 13 137 1) b := by
    have h := rep 3 (by decide) z
    change val 2 z = _ at hz
    rw [hz,hl1] at h
    exact h
  have hthree : RepresentsOnPage E 3 (13,137) (I.realization.basis .sphere 13 137 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h321
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 137 i.val at he
  have hbzero : E.d 3 (13,137) b = 0 := by
    apply represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) (rep 3 (by decide) z)
    exact ⟨val 4 z,rep 4 (by decide) z⟩
  have hazero : E.d 3 (13,137) a = 0 := by
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(10,135)) ⟨incoming,hda'⟩
  have hkernel (q : E.Page 3 (13,137)) (hq : E.d 3 (13,137) q=0) :
      q=0 ∨ q=a ∨ q=b ∨ q=a+b := by
    let vv : Fin 4 → E.Page 3 (13,137) := ![a,b,c,0]
    have hv (i : Fin 4) : RepresentsOnPage E 3 (13,137) (e.symm (Finsupp.single i 1)) (vv i) := by
      rw [he i]
      fin_cases i
      · exact ha
      · exact hb
      · exact hc
      · exact hthree
    obtain ⟨coef,hcoef⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e vv hv q
    simp only [Fin.sum_univ_succ] at hcoef
    change q = (if coef 0=0 then 0 else a) + ((if coef 1=0 then 0 else b) + ((if coef 2=0 then 0 else c) + ((if coef 3=0 then 0 else 0) + 0))) at hcoef
    have hczero : coef 2 = 0 := by
      by_contra hh
      have hd := congrArg (E.d 3 (13,137)) hcoef
      simp only [hq,map_add,apply_ite,map_zero,hazero,hbzero,hdc',hh,ite_false,ite_self,zero_add,add_zero] at hd
      exact htn hd.symm
    by_cases h0 : coef 0=0 <;> by_cases h1 : coef 1=0
    all_goals simp only [h0,h1,hczero,ite_true,ite_false,ite_self,add_zero,zero_add] at hcoef
    · exact Or.inl hcoef
    · exact Or.inr (Or.inr (Or.inl hcoef))
    · exact Or.inr (Or.inl hcoef)
    · exact Or.inr (Or.inr (Or.inr hcoef))
  have kill (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat.{v} ℤ)) (hq : val 3 q=0 ∨ val 3 q=a) : A.pageπ ⊤ q=0 := by
    have hfour : A.pageπ 2 (down 4 q)=0 := by
      apply (next_projection_zero_iff_incoming E 3 (by change (2:ℤ)≤3; omega) (10,135) (down 4 q)).mpr
      have hdown : (Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2)) ≫ A.pageπ 1) (down 4 q) = val 3 q := by
        change (Subobject.ofLE (A.Z 2) (A.Z 1) _ ≫ A.pageπ 1)
          ((Subobject.ofLE (A.Z ⊤) (A.Z 2) _) q) =
          (Subobject.ofLE (A.Z ⊤) (A.Z 1) _ ≫ A.pageπ 1) q
        rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
      change ∃ x, E.d 3 (10,135) x = (Subobject.ofLE (A.Z 2) (A.Z 1) _ ≫ A.pageπ 1) (down 4 q)
      rw [hdown]
      rcases hq with hq|hq
      · exact ⟨0, by rw [hq,map_zero]⟩
      · exact ⟨incoming, hda'.trans hq.symm⟩
    change (A.pageπ 2) ((Subobject.ofLE (A.Z ⊤) (A.Z 2) _) q)=0 at hfour
    have heq := A.infinity_projection_eq_of_page_projection_eq 2 q 0 (by simpa only [CategoryTheory.comp_apply,map_zero] using hfour)
    simpa only [map_zero] using heq
  refine ⟨z,hz,hzn,?_⟩
  intro y
  haveI : Epi (A.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨q,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance y
  have hqzero : E.d 3 (13,137) (val 3 q)=0 := by
    exact represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4)
      (rep 3 (by decide) q) ⟨val 4 q,rep 4 (by decide) q⟩
  rcases hkernel (val 3 q) hqzero with hq|hq|hq|hq
  · exact Or.inl (kill q (Or.inl hq))
  · exact Or.inl (kill q (Or.inr hq))
  · apply Or.inr
    change A.pageπ ⊤ q = A.pageπ ⊤ z
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply kill (q-z)
    left
    simp only [map_sub,hq,b,sub_self]
  · apply Or.inr
    change A.pageπ ⊤ q = A.pageπ ⊤ z
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply kill (q-z)
    right
    simp only [map_sub,hq,b,add_sub_cancel_right]

private theorem stem124_af10_exhaustion
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H} (I : KIP126.Computation.Route.Inputs D L G) (V : SphereVanishingLine H) :
    KIP126.Kervaire.Route.Section7.ClassicalInfinityGenerated 10 134
      (I.realization.sphere 10 134 U) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e10_134,he10_134⟩ := I.basis ⟨.sphere, 10, 134, ["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e10_134
  change ∀i : Fin 5, e10_134.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 134 i.val at he10_134
  have he10_134_0 : e10_134.symm (Finsupp.single 0 1) = I.realization.basis .sphere 10 134 0 := he10_134 0
  have he10_134_1 : e10_134.symm (Finsupp.single 1 1) = I.realization.basis .sphere 10 134 1 := he10_134 1
  have he10_134_2 : e10_134.symm (Finsupp.single 2 1) = I.realization.basis .sphere 10 134 2 := he10_134 2
  have he10_134_3 : e10_134.symm (Finsupp.single 3 1) = I.realization.basis .sphere 10 134 3 := he10_134 3
  have he10_134_4 : e10_134.symm (Finsupp.single 4 1) = I.realization.basis .sphere 10 134 4 := he10_134 4
  obtain ⟨e11_135,he11_135⟩ := I.basis ⟨.sphere, 11, 135, ["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e11_135
  change ∀i : Fin 5, e11_135.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 135 i.val at he11_135
  have he11_135_0 : e11_135.symm (Finsupp.single 0 1) = I.realization.basis .sphere 11 135 0 := he11_135 0
  have he11_135_1 : e11_135.symm (Finsupp.single 1 1) = I.realization.basis .sphere 11 135 1 := he11_135 1
  have he11_135_2 : e11_135.symm (Finsupp.single 2 1) = I.realization.basis .sphere 11 135 2 := he11_135 2
  have he11_135_3 : e11_135.symm (Finsupp.single 3 1) = I.realization.basis .sphere 11 135 3 := he11_135 3
  have he11_135_4 : e11_135.symm (Finsupp.single 4 1) = I.realization.basis .sphere 11 135 4 := he11_135 4
  obtain ⟨e12_136,he12_136⟩ := I.basis ⟨.sphere, 12, 136, ["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e12_136
  change ∀i : Fin 5, e12_136.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 136 i.val at he12_136
  have he12_136_0 : e12_136.symm (Finsupp.single 0 1) = I.realization.basis .sphere 12 136 0 := he12_136 0
  have he12_136_1 : e12_136.symm (Finsupp.single 1 1) = I.realization.basis .sphere 12 136 1 := he12_136 1
  have he12_136_2 : e12_136.symm (Finsupp.single 2 1) = I.realization.basis .sphere 12 136 2 := he12_136 2
  have he12_136_3 : e12_136.symm (Finsupp.single 3 1) = I.realization.basis .sphere 12 136 3 := he12_136 3
  have he12_136_4 : e12_136.symm (Finsupp.single 4 1) = I.realization.basis .sphere 12 136 4 := he12_136 4
  obtain ⟨e13_137,he13_137⟩ := I.basis ⟨.sphere, 13, 137, ["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e13_137
  change ∀i : Fin 4, e13_137.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 137 i.val at he13_137
  have he13_137_0 : e13_137.symm (Finsupp.single 0 1) = I.realization.basis .sphere 13 137 0 := he13_137 0
  have he13_137_1 : e13_137.symm (Finsupp.single 1 1) = I.realization.basis .sphere 13 137 1 := he13_137 1
  have he13_137_2 : e13_137.symm (Finsupp.single 2 1) = I.realization.basis .sphere 13 137 2 := he13_137 2
  have he13_137_3 : e13_137.symm (Finsupp.single 3 1) = I.realization.basis .sphere 13 137 3 := he13_137 3
  obtain ⟨e15_138,he15_138⟩ := I.basis ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = I.realization.basis .sphere 15 138 i.val at he15_138
  have he15_138_0 : e15_138.symm (Finsupp.single 0 1) = I.realization.basis .sphere 15 138 0 := he15_138 0
  have he15_138_1 : e15_138.symm (Finsupp.single 1 1) = I.realization.basis .sphere 15 138 1 := he15_138 1
  have he15_138_2 : e15_138.symm (Finsupp.single 2 1) = I.realization.basis .sphere 15 138 2 := he15_138 2
  obtain ⟨e13_136,he13_136⟩ := I.basis ⟨.sphere, 13, 136, ["418,1", "417,1", "0,2,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  change E.Page 2 (13,136) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e13_136
  change ∀i : Fin 3, e13_136.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 136 i.val at he13_136
  have he13_136_0 : e13_136.symm (Finsupp.single 0 1) = I.realization.basis .sphere 13 136 0 := he13_136 0
  have he13_136_1 : e13_136.symm (Finsupp.single 1 1) = I.realization.basis .sphere 13 136 1 := he13_136 1
  have he13_136_2 : e13_136.symm (Finsupp.single 2 1) = I.realization.basis .sphere 13 136 2 := he13_136 2
  obtain ⟨e14_137,he14_137⟩ := I.basis ⟨.sphere, 14, 137, ["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀i : Fin 3, e14_137.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 137 i.val at he14_137
  have he14_137_0 : e14_137.symm (Finsupp.single 0 1) = I.realization.basis .sphere 14 137 0 := he14_137 0
  have he14_137_1 : e14_137.symm (Finsupp.single 1 1) = I.realization.basis .sphere 14 137 1 := he14_137 1
  have he14_137_2 : e14_137.symm (Finsupp.single 2 1) = I.realization.basis .sphere 14 137 2 := he14_137 2
  have h171 : HasDifferential E 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 0) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 3) := by
    have hrow := I.results ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3], "S0_AdamsE2_ss", 2492⟩ (by
      exact List.mem_of_getElem? (i := 171) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h172 : HasDifferential E 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 1) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 1 + I.realization.basis .sphere 10 134 3 + I.realization.basis .sphere 10 134 4) := by
    have hrow := I.results ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4], "S0_AdamsE2_ss", 2493⟩ (by
      exact List.mem_of_getElem? (i := 172) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (6,131) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h201 : HasDifferential E 2 (8,133) (10,134) (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := by
    have hrow := I.results ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "S0_AdamsE2_ss", 2630⟩ (by
      exact List.mem_of_getElem? (i := 201) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (8,133) (10,134) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := by
    have hrow := I.results ⟨.sphere, .equation, 5, 10, 134, [3], 15, 138, [1], "S0_AdamsE2_ss", 2694⟩ (by
      exact List.mem_of_getElem? (i := 250) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 5 (10,134) (15,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h200 : HasDifferential E 3 (8,133) (11,135) (I.realization.basis .sphere 8 133 0) (I.realization.basis .sphere 11 135 0) := by
    have hrow := I.results ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2629⟩ (by
      exact List.mem_of_getElem? (i := 200) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (8,133) (11,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h226 : HasDifferential E 3 (9,134) (12,136) (I.realization.basis .sphere 9 134 1) (I.realization.basis .sphere 12 136 0) := by
    have hrow := I.results ⟨.sphere, .equation, 3, 9, 134, [1], 12, 136, [0], "S0_AdamsE2_ss", 2697⟩ (by
      exact List.mem_of_getElem? (i := 226) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (9,134) (12,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h227 : HasDifferential E 2 (9,134) (11,135) (I.realization.basis .sphere 9 134 0) (I.realization.basis .sphere 11 135 3 + I.realization.basis .sphere 11 135 4) := by
    have hrow := I.results ⟨.sphere, .equation, 2, 9, 134, [0], 11, 135, [3, 4], "S0_AdamsE2_ss", 2698⟩ (by
      exact List.mem_of_getElem? (i := 227) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h228 : HasDifferential E 2 (9,134) (11,135) (I.realization.basis .sphere 9 134 4) (I.realization.basis .sphere 11 135 4) := by
    have hrow := I.results ⟨.sphere, .equation, 2, 9, 134, [4], 11, 135, [4], "S0_AdamsE2_ss", 2699⟩ (by
      exact List.mem_of_getElem? (i := 228) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h253 : HasDifferential E 2 (10,135) (12,136) (I.realization.basis .sphere 10 135 1) (I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) := by
    have hrow := I.results ⟨.sphere, .equation, 2, 10, 135, [1], 12, 136, [1, 2], "S0_AdamsE2_ss", 2785⟩ (by
      exact List.mem_of_getElem? (i := 253) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h254 : HasDifferential E 2 (10,135) (12,136) (I.realization.basis .sphere 10 135 2) (I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4) := by
    have hrow := I.results ⟨.sphere, .equation, 2, 10, 135, [2], 12, 136, [3, 4], "S0_AdamsE2_ss", 2786⟩ (by
      exact List.mem_of_getElem? (i := 254) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h255 : HasDifferential E 2 (10,135) (12,136) (I.realization.basis .sphere 10 135 4) (I.realization.basis .sphere 12 136 4) := by
    have hrow := I.results ⟨.sphere, .equation, 2, 10, 135, [4], 12, 136, [4], "S0_AdamsE2_ss", 2787⟩ (by
      exact List.mem_of_getElem? (i := 255) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 15 138 0) := by
    have hrow := I.results ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0], "S0_AdamsE2_ss", 2781⟩ (by
      exact List.mem_of_getElem? (i := 277) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 4 (11,135) (15,138) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h278 : HasDifferential E 2 (11,135) (13,136) (I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 13 136 2) := by
    have hrow := I.results ⟨.sphere, .equation, 2, 11, 135, [2], 13, 136, [2], "S0_AdamsE2_ss", 2782⟩ (by
      exact List.mem_of_getElem? (i := 278) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,135) (13,136) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 136 [2] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h304 : HasDifferential E 2 (12,136) (14,137) (I.realization.basis .sphere 12 136 2) (I.realization.basis .sphere 14 137 2) := by
    have hrow := I.results ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2], "S0_AdamsE2_ss", 2849⟩ (by
      exact List.mem_of_getElem? (i := 304) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (12,136) (14,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 136 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 137 [2] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h321 : HasDifferential E 2 (11,136) (13,137) (I.realization.basis .sphere 11 136 4) (I.realization.basis .sphere 13 137 3) := by
    have hrow := I.results ⟨.sphere, .equation, 2, 11, 136, [4], 13, 137, [3], "S0_AdamsE2_ss", 2914⟩ (by
      exact List.mem_of_getElem? (i := 321) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,136) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h322 : HasDifferential E 3 (10,135) (13,137) (I.realization.basis .sphere 10 135 0) (I.realization.basis .sphere 13 137 0) := by
    have hrow := I.results ⟨.sphere, .equation, 3, 10, 135, [0], 13, 137, [0], "S0_AdamsE2_ss", 2915⟩ (by
      exact List.mem_of_getElem? (i := 322) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (10,135) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have h323 : ReachesPage E 1000 (13,137) (I.realization.basis .sphere 13 137 1) := by
    have hrow := I.results ⟨.sphere, .reaches, 1000, 13, 137, [1], 13, 137, [], "S0_AdamsE2_ss", 2916⟩ (by
      exact List.mem_of_getElem? (i := 323) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [1] = true := rfl
    simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
    rw [←ha] at h
    exact h
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := by
    have hrow := I.results ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
      exact List.mem_of_getElem? (i := 324) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (13,137) (16,139) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    simpa only [add_assoc] using h
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have hsub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have lift_e2 {r : ℤ} (hr : 2 ≤ r) {p : ℤ × ℤ} (x : E.Page r p) :
      ∃ a : E.Page 2 p, RepresentsOnPage E r p a x := by
    exact page_has_representative hr x
  have f2_expand {N : ℕ} (f : Fin N →₀ F2) :
      f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
    exact FinitePageCalculus.f2_expand f
  have rep_zero {r : ℤ} {p : ℤ × ℤ} {x : E.Page r p}
      (h : RepresentsOnPage E r p 0 x) : x=0 :=
    represents_unique h (RepresentsOnPage.zero h.1)
  have rep_double {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (hx : x+x=0) (ha : RepresentsOnPage E r p x a) : a+a=0 := by
    exact rep_zero (by simpa only [hx] using hadd ha ha)
  -- All four possible incoming d2 directions reach E3.
  have d2_13 : E.d 2 (13,137)=0 := by
    obtain ⟨_,x0,y0,hx0,hy0,_⟩ := h322
    obtain ⟨_,x2,y2,hx2,hy2,_⟩ := h324
    have h0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
    have h1 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000) (hrep2 _) h323
    have h2 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨x2,hx2⟩
    have h3 : E.d 2 (13,137) (I.realization.basis .sphere 13 137 3)=0 := by
      have hd := h321.eq_on_page_two.2
      change E.d 2 (11,136) _ = _ at hd
      rw [←hd]
      exact congrArg (fun f => f (I.realization.basis .sphere 11 136 4)) (E.d_comp_d 2 (11,136))
    have one (i : Fin 4) : E.d 2 (13,137) (e13_137.symm (Finsupp.single i 1))=0 := by
      rw [he13_137]
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    have all (f : Fin 4 →₀ F2) : E.d 2 (13,137) (e13_137.symm f)=0 := by
      induction f using Finsupp.induction with
      | zero => simp
      | @single_add i a f hi ha ih =>
        rw [map_add,map_add,ih,add_zero]
        fin_cases a
        · simp
        · exact one i
    ext x
    simpa only [LinearEquiv.symm_apply_apply,ModuleCat.hom_zero,LinearMap.zero_apply] using all (e13_137 x)
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  -- The complete d2 kernel in degree (12,136) consists of the d3 target
  -- basis0 and three d2 boundaries; consequently its entire d3 map is zero.
  have d3_12 : E.d 3 (12,136)=0 := by
    obtain ⟨_,in0,a0,hin0,ha0,hda0⟩ := h226
    have hd0 : E.d 3 (12,136) a0=0 :=
      IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(9,134)) ⟨in0,hda0⟩
    have rz12 : RepresentsOnPage E 3 (12,136)
        (I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h253
    have rz34 : RepresentsOnPage E 3 (12,136)
        (I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h254
    have rz4 : RepresentsOnPage E 3 (12,136) (I.realization.basis .sphere 12 136 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h255
    have rz3 : RepresentsOnPage E 3 (12,136) (I.realization.basis .sphere 12 136 3) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using hsub rz34 rz4
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a0,ha0⟩
    have d12 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz12⟩
    have d3 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz3⟩
    have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz4⟩
    have d2 := h304.eq_on_page_two.2
    change E.d 2 (12,136) (I.realization.basis .sphere 12 136 2) = I.realization.basis .sphere 14 137 2 at d2
    have tn : I.realization.basis .sphere 14 137 2 ≠ 0 := by
      rw [←he14_137_2]
      intro h
      have hh := congrArg e14_137 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
      norm_num at hh'
    have d1 : E.d 2 (12,136) (I.realization.basis .sphere 12 136 1) = -I.realization.basis .sphere 14 137 2 := by
      simpa only [map_add,d2,eq_neg_iff_add_eq_zero] using d12
    ext x
    obtain ⟨a,ha⟩ := lift_e2 (by decide : (2:ℤ)≤3) x
    have da := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 a) ⟨x,ha⟩
    let c : Fin 5 → F2 := e12_136 a
    have hcoef := congrArg e12_136.symm (f2_expand (e12_136 a))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change a = (if c 0=0 then 0 else e12_136.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e12_136.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e12_136.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e12_136.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e12_136.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he12_136_0,he12_136_1,he12_136_2,he12_136_3,he12_136_4,add_zero] at hcoef
    have hc : (c 1=0) ↔ (c 2=0) := by
      have hd := congrArg (E.d 2 (12,136)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [da,d0,d1,d2,d3,d4] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h1
        by_contra h2
        simp only [h1,h2,ite_true,ite_false,zero_add] at hd
        exact tn hd.symm
      · intro h2
        by_contra h1
        simp only [h1,h2,ite_true,ite_false,add_zero] at hd
        exact tn (neg_eq_zero.mp hd.symm)
    have hacomb : a = (if c 0=0 then 0 else I.realization.basis .sphere 12 136 0) +
        (if c 1=0 then 0 else I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) +
        (if c 3=0 then 0 else I.realization.basis .sphere 12 136 3) +
        (if c 4=0 then 0 else I.realization.basis .sphere 12 136 4) := by
      rw [hcoef]
      by_cases h1 : c 1=0
      · have h2 := hc.mp h1
        simp only [h1,h2,ite_true,zero_add,add_zero]
        abel
      · have h2 := mt hc.mpr h1
        simp only [h1,h2,ite_false]
        abel
    have hx : x=(if c 0=0 then 0 else a0) := by
      apply represents_unique ha
      rw [hacomb]
      simpa only [ite_self,add_zero] using hadd (hadd (hadd (hif (c 0) ha0) (hif (c 1) rz12)) (hif (c 3) rz3)) (hif (c 4) rz4)
    rw [hx]
    simp only [apply_ite,map_zero,hd0,ite_self,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a4,t0,ha4,ht0,hda4⟩ := h277
  have hd4 : E.d 4 (11,135) a4=t0 := hda4
  -- Incoming d2 and d3 kill every E4 direction except basis1+basis2.
  have kernel_11 (x : E.Page 4 (11,135)) : x=0 ∨ x=a4 := by
    have rz0 : RepresentsOnPage E 4 (11,135) (I.realization.basis .sphere 11 135 0) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h200
    have rz34 : RepresentsOnPage E 4 (11,135)
        (I.realization.basis .sphere 11 135 3 + I.realization.basis .sphere 11 135 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h227
    have rz4 : RepresentsOnPage E 4 (11,135) (I.realization.basis .sphere 11 135 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h228
    have rz3 : RepresentsOnPage E 4 (11,135) (I.realization.basis .sphere 11 135 3) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using hsub rz34 rz4
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz0⟩
    have d12 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨a4,ha4⟩
    have d3 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz3⟩
    have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz4⟩
    have d2 := h278.eq_on_page_two.2
    change E.d 2 (11,135) (I.realization.basis .sphere 11 135 2) = I.realization.basis .sphere 13 136 2 at d2
    have tn : I.realization.basis .sphere 13 136 2 ≠ 0 := by
      rw [←he13_136_2]
      intro h
      have hh := congrArg e13_136 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
      norm_num at hh'
    have d1 : E.d 2 (11,135) (I.realization.basis .sphere 11 135 1) = -I.realization.basis .sphere 13 136 2 := by
      simpa only [map_add,d2,eq_neg_iff_add_eq_zero] using d12
    obtain ⟨a,ha⟩ := lift_e2 (by decide : (2:ℤ)≤4) x
    have da := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 a) ⟨x,ha⟩
    let c : Fin 5 → F2 := e11_135 a
    have hcoef := congrArg e11_135.symm (f2_expand (e11_135 a))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change a = (if c 0=0 then 0 else e11_135.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e11_135.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e11_135.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e11_135.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e11_135.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he11_135_0,he11_135_1,he11_135_2,he11_135_3,he11_135_4,add_zero] at hcoef
    have hc : (c 1=0) ↔ (c 2=0) := by
      have hd := congrArg (E.d 2 (11,135)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [da,d0,d1,d2,d3,d4] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h1
        by_contra h2
        simp only [h1,h2,ite_true,ite_false,zero_add] at hd
        exact tn hd.symm
      · intro h2
        by_contra h1
        simp only [h1,h2,ite_true,ite_false,add_zero] at hd
        exact tn (neg_eq_zero.mp hd.symm)
    have hacomb : a = (if c 0=0 then 0 else I.realization.basis .sphere 11 135 0) +
        (if c 1=0 then 0 else I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) +
        (if c 3=0 then 0 else I.realization.basis .sphere 11 135 3) +
        (if c 4=0 then 0 else I.realization.basis .sphere 11 135 4) := by
      rw [hcoef]
      by_cases h1 : c 1=0
      · have h2 := hc.mp h1
        simp only [h1,h2,ite_true,zero_add,add_zero]
        abel
      · have h2 := mt hc.mpr h1
        simp only [h1,h2,ite_false]
        abel
    have hx : x=(if c 1=0 then 0 else a4) := by
      apply represents_unique ha
      rw [hacomb]
      simpa only [ite_self,add_zero,zero_add] using hadd (hadd (hadd (hif (c 0) rz0) (hif (c 1) ha4)) (hif (c 3) rz3)) (hif (c 4) rz4)
    by_cases h : c 1=0
    · exact Or.inl (by simpa only [h,ite_true] using hx)
    · exact Or.inr (by simpa only [h,ite_false] using hx)
  -- No d2 or d3 enters the d5 target degree, so distinct E2 labels
  -- that reach E4 remain distinct there.
  have nonzero4 {x : E.Page 2 (15,138)} (hx : x ≠ 0) {a : E.Page 4 (15,138)}
      (ha : RepresentsOnPage E 4 (15,138) x a) : a ≠ 0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    have hn3 : b ≠ 0 := represents_next_nonzero_of_incoming_zero
      (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) (by exact d2_13) hb (hrep2 x) hx
    exact represents_next_nonzero_of_incoming_zero
      (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) (by exact d3_12) ha hb hn3
  obtain ⟨_,c5,t1,hc5,ht1,hdc5⟩ := h250
  have hd5 : E.d 5 (10,134) c5=t1 := hdc5
  -- The only possible d4 image is target basis0, independent of basis1.
  have t1n : t1 ≠ 0 := by
    obtain ⟨_,z,hz2,hz5⟩ := ht1
    let T := E.ssData (15,138)
    let i := Subobject.ofLE (T.Z 3) (T.Z 2) (T.Z_anti (by decide : (2:WithTop ℕ)≤3))
    let t14 := T.pageπ 2 (i z)
    have ht14 : RepresentsOnPage E 4 (15,138) (I.realization.basis .sphere 15 138 1) t14 := by
      refine ⟨by decide,i z,?_,rfl⟩
      change (i ≫ Subobject.ofLE (T.Z 2) (T.Z 0) _ ≫ T.pageπ 0) z = _
      dsimp only [i]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz2
    have hn : t14 ≠ 0 := nonzero4 (by
      rw [←he15_138_1]
      intro h
      have hh := congrArg e15_138 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
      norm_num at hh') ht14
    have hne : t14 ≠ t0 := by
      intro heq
      have hh := nonzero4 (x:=I.realization.basis .sphere 15 138 1 - I.realization.basis .sphere 15 138 0) (by
        rw [←he15_138_1,←he15_138_0]
        intro h
        have hh := congrArg e15_138 h
        simp only [map_sub,LinearEquiv.apply_symm_apply,map_zero] at hh
        have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
        norm_num at hh') (hsub ht14 ht0)
      exact hh (sub_eq_zero.mpr heq)
    intro hzero
    have hinc := (next_projection_zero_iff_incoming E 4
      (by change (2:ℤ)≤4; omega) (11,135) z).mp (hz5.trans hzero)
    change t14 ∈ LinearMap.range (E.d 4 (11,135)).hom at hinc
    obtain ⟨a,ha⟩ := hinc
    rcases kernel_11 a with h|h
    · apply hn
      simpa only [h,map_zero] using ha.symm
    · apply hne
      simpa only [h,hd4] using ha.symm
  have u_label : I.realization.sphere 10 134 U = I.realization.basis .sphere 10 134 4 := by
    have hc := I.csv (⟨.sphere,10,134,["389,1","388,1","1,1,366,1","0,1,373,1","0,2,367,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 181) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (4 : Fin 5)
    have heq : U=z := by
      apply Subtype.ext
      rw [hz]
      change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨367,by decide⟩ = projection (monomialOfString "0,2,367,1")
      have hs : "0,2,367,1" ≠ "" := by decide
      have hp : (("0,2,367,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,2,367,1] := by
        have split : "0,2,367,1".splitOn "," = ["0","2","367","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  let A := E.ssData (10,134)
  obtain ⟨z,hz,hzn⟩ := nonzero_permanent_of_survives1000 (D := D) V
    10 134 (by decide) (by norm_num) (by norm_num) _ (named_survive1000 I).1
  change (Subobject.ofLE (A.Z ⊤) (A.Z 0) (A.Z_anti le_top) ≫ A.pageπ 0) z = _ at hz
  change A.pageπ ⊤ z ≠ 0 at hzn
  let down (r : ℤ) := Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-2).toNat) (A.Z_anti le_top)
  let val (r : ℤ) := down r ≫ A.pageπ ↑(r-2).toNat
  have rep (r : ℤ) (hr : 2≤r) (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat.{v} ℤ)) :
      RepresentsOnPage E r (10,134) (val 2 q) (val r q) := by
    refine ⟨hr,down r q,?_,rfl⟩
    change (Subobject.ofLE _ _ _ ≫ A.pageπ 0) ((down r) q) = val 2 q
    dsimp only [val,down]
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    rfl
  let u5 : E.Page 5 (10,134) := val 5 z
  have hu5 : RepresentsOnPage E 5 (10,134) (I.realization.basis .sphere 10 134 4) u5 := by
    have h := rep 5 (by decide) z
    change val 2 z = _ at hz
    rw [hz,u_label] at h
    exact h
  have hu0 : E.d 5 (10,134) u5=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<6)
      (rep 5 (by decide) z) ⟨val 6 z,rep 6 (by decide) z⟩
  have r03 : RepresentsOnPage E 5 (10,134)
      (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h171
  have r0134 : RepresentsOnPage E 5 (10,134)
      (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 1 +
        I.realization.basis .sphere 10 134 3 + I.realization.basis .sphere 10 134 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h172
  have r24 : RepresentsOnPage E 5 (10,134)
      (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) h201
  have ddouble (i : Fin 5) : I.realization.basis .sphere 10 134 i.val + I.realization.basis .sphere 10 134 i.val=0 := by
    rw [←he10_134 i]
    have hh : (Finsupp.single i (1:F2) : Fin 5 →₀ F2) + Finsupp.single i 1 = 0 := by
      rw [←Finsupp.single_add,show (1:F2)+1=0 from by decide,Finsupp.single_zero]
    have h := congrArg e10_134.symm hh
    simpa only [map_add,map_zero] using h
  have cdouble : c5+c5=0 := rep_double (ddouble 3) hc5
  have udouble : u5+u5=0 := rep_double (ddouble 4) hu5
  have cneg : -c5=c5 := by simpa only [add_sub_cancel_right,zero_sub] using (congrArg (fun t => t-c5) cdouble).symm
  have uneg : -u5=u5 := by simpa only [add_sub_cancel_right,zero_sub] using (congrArg (fun t => t-u5) udouble).symm
  have r0 : RepresentsOnPage E 5 (10,134) (I.realization.basis .sphere 10 134 0) c5 := by
    simpa only [add_sub_cancel_right,zero_sub,cneg] using hsub r03 hc5
  have r1 : RepresentsOnPage E 5 (10,134) (I.realization.basis .sphere 10 134 1) u5 := by
    have he : (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 1 + I.realization.basis .sphere 10 134 3 + I.realization.basis .sphere 10 134 4) - (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 3) - I.realization.basis .sphere 10 134 4 = I.realization.basis .sphere 10 134 1 := by abel
    simpa only [he,sub_self,zero_sub,uneg] using hsub (hsub r0134 r03) hu5
  have r2 : RepresentsOnPage E 5 (10,134) (I.realization.basis .sphere 10 134 2) u5 := by
    simpa only [add_sub_cancel_right,zero_sub,uneg] using hsub r24 hu5
  -- At E5 the complete five-element basis maps to [c,U,U,c,U].
  -- The nonzero differential of c leaves precisely zero and U in its kernel.
  have kernel5 (x : E.Page 5 (10,134)) (hx : E.d 5 (10,134) x=0) : x=0 ∨ x=u5 := by
    let vv : Fin 5 → E.Page 5 (10,134) := ![c5,u5,u5,c5,u5]
    have hv (i : Fin 5) : RepresentsOnPage E 5 (10,134) (e10_134.symm (Finsupp.single i 1)) (vv i) := by
      rw [he10_134]
      fin_cases i
      · exact r0
      · exact r1
      · exact r2
      · exact hc5
      · exact hu5
    obtain ⟨coef,hcoef⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤5) e10_134 vv hv x
    simp only [Fin.sum_univ_succ] at hcoef
    change x = (if coef 0=0 then 0 else c5) + ((if coef 1=0 then 0 else u5) + ((if coef 2=0 then 0 else u5) + ((if coef 3=0 then 0 else c5) + ((if coef 4=0 then 0 else u5) + 0)))) at hcoef
    have hc : (coef 0=0) ↔ (coef 3=0) := by
      have hd := congrArg (E.d 5 (10,134)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [hx,hd5,hu0] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h0
        by_contra h3
        simp only [h0,h3,ite_true,ite_false,zero_add] at hd
        exact t1n hd.symm
      · intro h3
        by_contra h0
        simp only [h0,h3,ite_true,ite_false,add_zero] at hd
        exact t1n hd.symm
    have hform : x=(if coef 1=0 then 0 else u5) + (if coef 2=0 then 0 else u5) + (if coef 4=0 then 0 else u5) := by
      rw [hcoef]
      by_cases h0 : coef 0=0
      · have h3 := hc.mp h0
        simp only [h0,h3,ite_true,zero_add,add_zero]
        abel
      · have h3 := mt hc.mpr h0
        simp only [h0,h3,ite_false,add_zero]
        calc
          _ = (c5+c5) + ((if coef 1=0 then 0 else u5) + (if coef 2=0 then 0 else u5) + (if coef 4=0 then 0 else u5)) := by abel
          _ = _ := by rw [cdouble,zero_add]
    by_cases h1 : coef 1=0 <;> by_cases h2 : coef 2=0 <;> by_cases h4 : coef 4=0
    all_goals simp only [h1,h2,h4,ite_true,ite_false,zero_add,add_zero,udouble] at hform
    all_goals first | exact Or.inl hform | exact Or.inr hform
  refine ⟨z,hz,hzn,?_⟩
  intro y
  haveI : Epi (A.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨q,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance y
  have hqzero : E.d 5 (10,134) (val 5 q)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<6)
      (rep 5 (by decide) q) ⟨val 6 q,rep 6 (by decide) q⟩
  rcases kernel5 (val 5 q) hqzero with hq|hq
  · left
    have h := A.infinity_projection_eq_of_page_projection_eq 3 q 0 (by
      change val 5 q = val 5 0
      rw [map_zero]
      exact hq)
    simpa only [map_zero] using h
  · right
    exact A.infinity_projection_eq_of_page_projection_eq 3 q z hq

private theorem theta_detection_step
    {D : Model H M Syn}
    (i : Tridegree) (x : (D.family.sphere).E₂ i)
    (hframe : ∀ e : ((D.family.sphere).sequence.ssData i).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) i.1 a) :
    DetectsNonzero D.sphereConvergence i x a ∨
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (i.1+1) a := by
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)
  have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0:Syn) (i.2.1-i.1,i.2.2)))
      (F.F i.1 (i.2.1-i.1,i.2.2)) := by
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
  obtain ⟨a',ha'⟩ := ham
  let q := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
  let e := (D.sphereConvergence.identification i).inv q
  have he : (D.sphereConvergence.identification i).hom e=q :=
    ConcreteCategory.congr_hom (D.sphereConvergence.identification i).inv_hom_id q
  by_cases he0 : e=0
  · right
    have hq : F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'=0 := by
      rw [he0,map_zero] at he
      exact he.symm
    have hmem := (subobject_cokernel_π_eq_zero_iff
      (F.F (i.1+1) (i.2.1-i.1,i.2.2)) (F.F i.1 (i.2.1-i.1,i.2.2))
      (F.mono i.1 (i.2.1-i.1,i.2.2)) a').mp hq
    rw [ha'] at hmem
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hmem
  · left
    have hr := (hframe e).resolve_left he0
    exact ⟨⟨e,hr,a',ha',he⟩,e,hr,he0⟩
/- The two complete frames and the intervening finite-page gap yield the
three branches, retaining an actual lambda preimage in the last branch. -/

private theorem theta_quotient_frame
    (I : KIP126.Computation.Route.Inputs D L G) (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t), x'.val=x ∧
      ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData (s,t)
  have hB : P.B ⊤ = P.B (k:WithTop ℕ) := by
    have hin : ∀ r : ℤ, (k:ℤ)+2 ≤ r → E.d r ((s,t)-E.diffDeg r)=0 := by
      intro r hr
      change E.d r (s-r,t-(r-1))=0
      rw [show t-(r-1)=(s-r)+125 by omega]
      ext z
      exact no_outgoing_stem125_low I (s-r) (by omega) r (by omega) z
    have h := boundaries_top_eq_of_d_eq_zero E (k+2) (by change (2:ℤ)≤_; omega) (s,t) hin
    change P.B ⊤ = P.B (↑((k:ℤ)+2-2).toNat) at h
    simpa only [add_sub_cancel_right,Int.toNat_natCast] using h
  obtain ⟨z,hz,_,hall⟩ := hx
  change PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z=x at hz
  let x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := ⟨x,⟨z,hz⟩⟩
  refine ⟨x',rfl,?_⟩
  have zero_of_infinity_zero (z' : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ))
      (hzero : P.pageπ ⊤ z'=0) :
      PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z' ∈
        PageRepresentatives.boundaries H SphereSpectrum (1+(k:ℤ)) (s,t) := by
    obtain ⟨b,hb⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (P.B ⊤) (P.Z ⊤) (P.B_le_Z ⊤)) z').mp hzero
    have hi : P.B ⊤ ≤ P.B (k:WithTop ℕ) := hB.le
    change ∃ q, PageRepresentatives.boundaryMap H SphereSpectrum
      (↑((1+(k:ℤ))-1).toNat) (s,t) q = _
    rw [show 1+(k:ℤ)-1=(k:ℤ) by omega,Int.toNat_natCast]
    refine ⟨(Subobject.ofLE _ _ hi) b,?_⟩
    rw [←hb]
    change (Subobject.ofLE _ _ hi ≫ PageRepresentatives.boundaryMap H SphereSpectrum (k:WithTop ℕ) (s,t)) b =
      (Subobject.ofLE _ _ (P.B_le_Z ⊤) ≫ PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t)) b
    congr 1
    dsimp only [PageRepresentatives.boundaryMap,PageRepresentatives.cycleMap,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE,←Category.assoc,Subobject.ofLE_comp_ofLE]
  rintro ⟨y⟩
  obtain ⟨z',hz'⟩ := y.property
  rcases hall (P.pageπ ⊤ z') with h0|h1
  · left
    apply (NestedQuotient.projection_eq_zero y).mpr
    rw [←hz']
    exact zero_of_infinity_zero z' h0
  · right
    apply sub_eq_zero.mp
    change NestedQuotient.projection _ _ y - NestedQuotient.projection _ _ x'=0
    rw [←map_sub]
    apply (NestedQuotient.projection_eq_zero (y-x')).mpr
    change y.val-x ∈ _
    rw [←hz',←hz,←map_sub]
    exact zero_of_infinity_zero (z'-z) (by rw [map_sub,h1,sub_self])


private theorem theta_sphere_frame_family_map_data {X Y : Syn} (f : X ⟶ Y) (i : Tridegree) :
    familyPageMap D.family f 2 i = (D.family.functor.map f).toSSDataMorphism.pageMap i 0 := by
  classical
  let F := (D.family.functor.map f).toSSDataMorphism
  let PX := (D.family.functor.obj X).ssData i
  let PY := (D.family.functor.obj Y).ssData i
  let nX : WithTop ℕ := ↑(2-(D.family.functor.obj X).r₀).toNat
  let nY : WithTop ℕ := ↑(2-(D.family.functor.obj Y).r₀).toNat
  change (@eqToHom (ModuleCat ℤ) _ (PX.page 0) (PX.page nX) _ ≫
    (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
    @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page 0) _) = F.pageMap i 0
  have hX : nX=0 := by dsimp only [nX]; rw [D.family.firstPage X]; rfl
  have hY : nY=0 := by dsimp only [nY]; rw [D.family.firstPage Y]; rfl
  have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
      (n m : WithTop ℕ) (hn : n=0) (hm : m=0)
      (h1 : A 0=A n) (h2 : B n=B m) (h3 : B m=B 0) :
      eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j 0 := by
    subst n
    subst m
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
  exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY hX hY _ _ _


private theorem theta_sphere_frame_map_infinity {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
    (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
    (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
    HasInfinityRepresentative (D.family.obj Y) 2 i
      (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
  classical
  obtain ⟨hr,z,hz,he⟩ := hy
  change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
    (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
  let F := (D.family.functor.map f).toSSDataMorphism
  refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
  · rw [theta_sphere_frame_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])


private theorem theta_sphere_frame
    (I : KIP126.Computation.Route.Inputs D L G) (BHS : SyntheticInputs D)
    (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∀ e : ((D.family.sphere).sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (s,t,t-k) (D.sphereE2 s t k x) e := by
  classical
  classical
  obtain ⟨x',hx',hframe⟩ := theta_quotient_frame I s t k hst hsk x hx
  intro e
  let i : Tridegree := (s,t,t-k)
  let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap i
  let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap i
  have hfg : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  have hback : f (g e)=e := ConcreteCategory.congr_hom hfg e
  let nuE := BHS.eInfty.presentation.nuWindow SphereSpectrum (s,t) (t-k) (by omega)
  have heqcut : 1+t-(t-(k:ℤ))=1+(k:ℤ) := by omega
  have hfq : nuE (g e)=0 ∨ nuE (g e)=NestedQuotient.projection _ _ x' := by
    have hh : ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+t-(t-(k:ℤ))) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
      rw [heqcut]
      exact hframe
    exact hh (nuE (g e))
  rcases hfq with h0|h1
  · left
    have hg0 : g e=0 := nuE.injective (h0.trans (map_zero nuE).symm)
    rw [←hback,hg0,map_zero]
  · right
    have hr := (BHS.eInfty.labels.2 .sphere (s,t) k x' (g e)).mpr h1
    have hh := theta_sphere_frame_map_infinity D.nu.unitIso.hom i _ _ hr
    have hlabel : familyPageMap D.family D.nu.unitIso.hom 2 i
        (targetNuLabel D .sphere s t k x'.val) = D.sphereE2 s t k x := by
      rw [hx']
      dsimp only [targetNuLabel]
      rw [theta_sphere_frame_family_map_data,theta_sphere_frame_family_map_data]
      dsimp only [i] at *
      change ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.pageMap (s,t,t-k) 0 ≫
        (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism.pageMap (s,t,t-k) 0) _ = _
      rw [←SSDataMorphism.pageMap_comp]
      have hp := D.comparisonCompatible.sphere_nu s t k x
      rw [theta_sphere_frame_family_map_data] at hp
      have hm : ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.comp
          (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism) =
          (D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom)).toSSDataMorphism := by
        change (D.family.functor.map _ ≫ D.family.functor.map _).toSSDataMorphism = _
        rw [←CategoryTheory.Functor.map_comp]
      rw [hm]
      exact hp
    change HasInfinityRepresentative D.family.sphere 2 i _ (f (g e)) at hh
    rw [hback,hlabel] at hh
    exact hh


private theorem theta_three_cases_from_frames_permanentQuotient_zero_of_page_six_zero (s t b : ℤ) (hb : 5 ≤ b)
    (hpage : Subsingleton ((sequence D .sphere).Page 6 (s, t))) :
    Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
  classical
  set_option backward.isDefEq.respectTransparency false in
    let E := (sequence D .sphere).ssData (s, t)
    haveI : Subsingleton (E.page 4) := hpage
    have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
        PageRepresentatives.boundaries H SphereSpectrum 5 (s, t) := by
      rintro x ⟨z, hz⟩
      let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 4) (E.Z_anti le_top)) z
      have hzero : E.pageπ 4 zf = 0 := Subsingleton.elim _ _
      obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4)) zf).mp hzero
      refine ⟨y, ?_⟩
      change PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) y = x
      have hfactor : Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4) ≫
          PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t) =
          PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) := by
        dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.Route.sequence, object]
        rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
      rw [← hfactor, CategoryTheory.comp_apply]
      apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t)) hy).trans
      exact (congrArg (fun f => f z)
        (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 4 ⊤ le_top)).trans hz
    have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
      rintro ⟨x⟩
      change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
      apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
      exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
    exact ⟨fun x y => (hall x).trans (hall y).symm⟩



private theorem theta_three_cases_from_frames
    (I : KIP126.Computation.Route.Inputs D L G) (BHS : SyntheticInputs D)
    (x10 : E2 H SphereSpectrum 10 134) (x13 : E2 H SphereSpectrum 13 137)
    (h10 : ClassicalInfinityGenerated 10 134 x10)
    (h13 : ClassicalInfinityGenerated 13 137 x13)
    (h11 : Subsingleton ((Computation.Route.sequence D .sphere).Page 5 (11,135)))
    (h12 : Subsingleton ((Computation.Route.sequence D .sphere).Page 4 (12,136)))
    (a : BiHom 124 128 (S_0_0 : Syn))
    (ha10 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 10 a) :
    SphereDetected D 10 134 6 x10 a ∨ SphereDetected D 13 137 9 x13 a ∨
      ∃ b : BiHom 124 138 (S_0_0:Syn), lambdaMultiply 10 b=a := by
  classical
  have hgap : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 13 a := by
    classical
    apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
      11 13 124 128 (by omega) ?_ a).mp
    intro j hj hj'
    have hpage : Subsingleton ((Computation.Route.sequence D .sphere).Page 6 (j,124+j)) := by
      interval_cases j
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 11 135
          (by omega) (by omega) h11
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 12 136
          (by omega) (by omega) h12
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(124+j)-128) (j,124+j)) :=
      theta_three_cases_from_frames_permanentQuotient_zero_of_page_six_zero j (124+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,124+j) 128 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,128)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,128)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,124+j,128)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,124+j,128)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])

  have hf10 := theta_sphere_frame I BHS 10 134 6 (by omega) (by omega) x10 h10

  classical
  rcases theta_detection_step (10,134,128) (D.sphereE2 10 134 6 x10) hf10 a ha10 with hdet|ha11
  · exact Or.inl hdet
  have ha13 := hgap ha11
  have hf13 := theta_sphere_frame I BHS 13 137 9 (by omega) (by omega) x13 h13
  rcases theta_detection_step (13,137,128) (D.sphereE2 13 137 9 x13) hf13 a ha13 with hdet|ha14
  · exact Or.inr (Or.inl hdet)
  right; right
  have hmap {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
      (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s x) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (x ≫ f) := by
    obtain ⟨z,hz⟩ := hx
    refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat,?_⟩
    change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat) ≫
      adamsTowerMap (nuCoefficientUnit H.unit D.nu) Y 0 s.toNat _ = x ≫ f
    change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) X 0 s.toNat _ = x at hz
    rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hz]
    rfl
  have h := BHS.filtration_lambda .sphere 124 128 14 (by omega) (a ≫ D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (a ≫ D.nu.unitIso.inv) ↔
    ∃ b : BiHom 124 138 (D.nu.functor.obj SphereSpectrum), lambdaMultiply 10 b=a ≫ D.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (hmap D.nu.unitIso.inv a ha14)
  refine ⟨b ≫ D.nu.unitIso.hom,?_⟩
  simpa [lambdaMultiply,Category.assoc] using congrArg (fun q => q ≫ D.nu.unitIso.hom) hb

private theorem prop78_theta_data (I : KIP126.Computation.Route.Inputs D L G)
    (BHS : SyntheticInputs D) (V : SphereVanishingLine H) :
    ClassicalInfinityGenerated 13 137 (I.realization.sphere 13 137 correction) ∧
      ∀ theta : BiHom 62 64 (S_0_0 : Syn),
        C4At M D.toModelData L theta ∨
          SphereDetected D 13 137 9 (I.realization.sphere 13 137 correction)
            (sphereProduct theta theta) ∨
          ∃ a : BiHom 124 138 (S_0_0 : Syn), lambdaMultiply 10 a=sphereProduct theta theta := by
  /- BHS label agreement and the actual nu-unit map transport common infinity
  representatives to the synthetic sphere, including the zero case. -/
  /- Actual convergence gives either nonzero leading detection or membership
  in the next actual tower filtration. -/

  have classical_low_same_input (I : KIP126.Computation.Route.Inputs D L G) (s : ℤ) (hs : s<10) :
      Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData (s,s+124)).eInfty := by
    set_option backward.isDefEq.respectTransparency false in
    set_option maxRecDepth 10000 in
      let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
      have collapse (r : ℤ) (hp : Subsingleton (E.Page r (s,s+124))) :
          Subsingleton ((E.ssData (s,s+124)).eInfty) := by
        let A := E.ssData (s,s+124)
        haveI : Epi (A.pageπ ⊤) := inferInstanceAs (Epi (CategoryTheory.Limits.cokernel.π _))
        refine ⟨fun x y => ?_⟩
        obtain ⟨x,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance x
        obtain ⟨y,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance y
        exact A.infinity_projection_eq_of_page_projection_eq ↑(r-E.r₀).toNat x y (hp.elim _ _)
      by_cases hneg : s < 0
      · exact collapse 2 (adamsTowerInternal_page_subsingleton_of_negative
          H.unit SphereSpectrum 2 s (s+124) hneg)
      have hs0 : 0 ≤ s := by omega
      by_cases hsmall : s ≤ 5
      · have hd : (⟨.sphere,s.toNat,(s+124).toNat,[]⟩ : KIP126.Computation.Route.Raw.Degree) ∈ KIP126.Computation.Route.Raw.degrees := by
          interval_cases s <;> simp [KIP126.Computation.Route.Raw.degrees]
        obtain ⟨e,_⟩ := I.basis _ hd
        change KIP126.Computation.Route.Page D .sphere s.toNat (s+124).toNat ≃ₗ[ℤ] (Fin 0 →₀ KIP126.Core.Algebra.F2) at e
        have he : Subsingleton (KIP126.Computation.Route.Page D .sphere s.toNat (s+124).toNat) := e.injective.subsingleton
        apply collapse 2
        simpa only [KIP126.Computation.Route.Page,KIP126.Computation.Route.sequence,KIP126.Computation.Route.object,E,
        Int.toNat_of_nonneg hs0,
          Int.toNat_of_nonneg (by omega : 0 ≤ s+124)] using he
      have hfinite := stem124_finite_pages I
      change Subsingleton (E.Page 6 (6,130)) ∧ Subsingleton (E.Page 6 (7,131)) ∧
        Subsingleton (E.Page 3 (8,132)) ∧ Subsingleton (E.Page 4 (9,133)) at hfinite
      interval_cases s
      · exact collapse 6 hfinite.1
      · exact collapse 6 hfinite.2.1
      · exact collapse 3 hfinite.2.2.1
      · exact collapse 4 hfinite.2.2.2
  have theta_three_cases_same_input (I : KIP126.Computation.Route.Inputs D L G)
      (BHS : SyntheticInputs D) (V : SphereVanishingLine H)
      (theta : BiHom 62 64 (S_0_0 : Syn)) :
      C4At M D.toModelData L theta ∨
        SphereDetected D 13 137 9 (I.realization.sphere 13 137 KIP126.Computation.Near126.correction)
          (sphereProduct theta theta) ∨
        ∃ a : BiHom 124 138 (S_0_0 : Syn), lambdaMultiply 10 a=sphereProduct theta theta := by
    have h10 := stem124_af10_exhaustion I V
    rw [(KIP126.Computation.Route.route_expression_labels I).2.1] at h10
    exact theta_three_cases_from_frames I BHS (L.U M)
      (I.realization.sphere 13 137 KIP126.Computation.Near126.correction)
      h10 (stem124_af13_exhaustion I V)
      (KIP126.Computation.Route.sphere_facts I V).e5_stem124_af11
      (KIP126.Computation.Route.sphere_facts I V).e4_stem124_af12
      (sphereProduct theta theta)
      (stem124_weight128_filtration_ten BHS I (classical_low_same_input I) (sphereProduct theta theta))
  exact ⟨stem124_af13_exhaustion I V,theta_three_cases_same_input I BHS V⟩

end
end KIP126.Main.Solution.Route

namespace KIP126.Main.Solution.Route
open KIP126.Core.SpectralSequence.FinitePageCalculus
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route KIP126.Algebra
open KIP126.LinE2 KIP126.Computation.Near126 KIP126.Computation.Route
noncomputable section
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
  {L : Labels H} {G : TmfLabels H} {η : BiHom 1 2 (S_0_0:Syn)}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem prop78_classical_data_h342_0 (I : KIP126.Computation.Route.Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (14,139) (I.realization.basis .sphere 14 139 1) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
    exact List.mem_of_getElem? (i := 342) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (14,139) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem prop78_classical_data_h341_1 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,138) (14,139)
    (I.realization.basis .sphere 12 138 1) (I.realization.basis .sphere 14 139 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,12,138,[1],14,139,[2],"S0_AdamsE2_ss",3079⟩ (by
    exact List.mem_of_getElem? (i := 341) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,138) (14,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 139 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem prop78_classical_data_h343_2 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,139) (16,140)
    (I.realization.basis .sphere 14 139 0) (I.realization.basis .sphere 16 140 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,14,139,[0],16,140,[2],"S0_AdamsE2_ss",3081⟩ (by
    exact List.mem_of_getElem? (i := 343) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,139) (16,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem prop78_classical_data_h342_3 (I : KIP126.Computation.Route.Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (14,139) (I.realization.basis .sphere 14 139 1) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
    exact List.mem_of_getElem? (i := 342) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (14,139) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem prop78_classical_data_nonzero_differential_not_permanent {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q} (hr0 : E.r₀ ≤ r)
    (h : HasNonzeroDifferential E r p q x y) : ¬ NonzeroSurvival E p x := by
  classical
  rintro ⟨z, hz, _⟩
  let A := E.ssData p
  let n : WithTop ℕ := ↑(r + 1 - E.r₀).toNat
  let z' := (Subobject.ofLE (A.Z ⊤) (A.Z n) (A.Z_anti le_top)) z
  obtain ⟨hdeg, xr, yr, hx, hy, hd, hne⟩ := h
  have hr2 := hx.1
  have hlater : ReachesPage E (r + 1) p x := by
    refine ⟨A.pageπ n z', by omega, z', ?_, rfl⟩
    dsimp only [z']
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  have hd0 := represents_d_zero_of_later hr0 (by omega : r < r + 1) hx hlater
  rw [ModuleCat.comp_apply, hd0, map_zero] at hd
  exact hne hd.symm


private theorem prop78_classical_data_earlier_zero_of_target_survives {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr0 : E.r₀ ≤ r) (hrt : r < t)
    {y : E.Page 2 (p + E.diffDeg r)}
    (hsource : SurvivesTo E r p x)
    (htargets : DifferentialTargets E r p x y)
    (htarget : SurvivesTo E t (p + E.diffDeg r) y) :
    HasDifferential E r p (p + E.diffDeg r) x 0 := by
  classical
  obtain ⟨xr, hxr, _⟩ := hsource
  have hd0 : E.d r p xr = 0 := by
    rcases htargets xr hxr with hz | ⟨yr, hyr, hdr⟩
    · exact hz
    · have hd : HasDifferential E r p (p + E.diffDeg r) x y :=
        ⟨rfl, xr, yr, hxr, hyr, by simpa only [eqToHom_refl, Category.comp_id] using hdr⟩
      have hlater := differential_target_later_zero hr0 hrt hd
      obtain ⟨yt, hyt, hne⟩ := htarget
      exact False.elim (hne (represents_unique hyt hlater))
  exact ⟨rfl, xr, 0, hxr, RepresentsOnPage.zero hxr.1,
    by simpa only [eqToHom_refl, Category.comp_id] using hd0⟩


private theorem prop78_classical_data_next_nonzero_of_not_hit {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
    {a : E.Page (r+1) p} {b : E.Page r p}
    (ha : RepresentsOnPage E (r+1) p x a) (hb : RepresentsOnPage E r p x b)
    (hne : b ≠ 0) (hnot : ¬ HitOnPage E r p x) : a ≠ 0 := by
  classical
  generalize hq : p-E.diffDeg r=q
  have hp : p=q+E.diffDeg r := by rw [←hq]; abel
  subst p
  obtain ⟨_,z,hz,hza⟩ := ha
  let A := E.ssData (q+E.diffDeg r)
  have hi : (r+1-E.r₀).toNat=(r-E.r₀).toNat+1 := by omega
  have hnm : (↑(r-E.r₀).toNat : WithTop ℕ) ≤ ↑(r+1-E.r₀).toNat := by
    exact_mod_cast (show (r-E.r₀).toNat≤(r+1-E.r₀).toNat by omega)
  let br := (Subobject.ofLE _ _ (A.Z_anti hnm) ≫ A.pageπ ↑(r-E.r₀).toNat) z
  have hbr : RepresentsOnPage E r (q+E.diffDeg r) x br := by
    refine ⟨hr, (Subobject.ofLE _ _ (A.Z_anti hnm)) z, ?_, rfl⟩
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  have heb : br=b := represents_unique hbr hb
  intro ha0
  have hv := next_projection_zero_iff_incoming E r hr0 q
  have hv' : ∀ zz : (Subobject.underlying.obj (A.Z ↑(r+1-E.r₀).toNat) : ModuleCat ℤ),
      A.pageπ ↑(r+1-E.r₀).toNat zz=0 ↔
        (Subobject.ofLE _ _ (A.Z_anti hnm) ≫ A.pageπ ↑(r-E.r₀).toNat) zz∈
          LinearMap.range (E.d r q).hom := by
    have transport (m : ℕ) (hm : m=(r-E.r₀).toNat+1)
        (hge : (↑(r-E.r₀).toNat : WithTop ℕ)≤↑m) :
        ∀ zz : (Subobject.underlying.obj (A.Z ↑m) : ModuleCat ℤ),
          A.pageπ ↑m zz=0 ↔
            (Subobject.ofLE _ _ (A.Z_anti hge) ≫ A.pageπ ↑(r-E.r₀).toNat) zz∈
              LinearMap.range (E.d r q).hom := by
      subst m
      exact hv
    exact transport _ hi hnm
  have hmem : br∈LinearMap.range (E.d r q).hom := by
    exact (hv' z).mp (hza.trans ha0)
  obtain ⟨c,hc⟩ := hmem
  apply hnot
  refine ⟨q, rfl, c,b,hb,hne,?_⟩
  simpa only [eqToHom_refl, Category.comp_id] using hc.trans heb


private theorem prop78_classical_data_permanent_survives_of_no_early_hit {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hstart : E.r₀≤2) (N : ℕ) (hN : 2≤N)
    (hperm : IsPermanentCycle E p x) (hne : x≠0)
    (hnot : ∀ r : ℤ, 2≤r → r<N → ¬HitOnPage E r p x) :
    SurvivesTo E N p x := by
  classical
  obtain ⟨z,hz⟩ := hperm
  let A := E.ssData p
  have hrep (r : ℤ) (hr : 2≤r) : ReachesPage E r p x := by
    let zr := (Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-E.r₀).toNat) (A.Z_anti le_top)) z
    refine ⟨A.pageπ _ zr,hr,zr,?_,rfl⟩
    dsimp only [zr]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  have hall (n : ℕ) : n+2≤N → SurvivesTo E ((n:ℤ)+2) p x := by
    induction n with
    | zero =>
      intro hn
      obtain ⟨a,ha⟩ := hrep 2 (by omega)
      change SurvivesTo E 2 p x
      exact ⟨a,ha,by rw [←ha.eq_on_page_two]; exact hne⟩
    | succ n ih =>
      intro hn
      obtain ⟨b,hb,hbn⟩ := ih (by omega)
      obtain ⟨a,ha⟩ := hrep ((n:ℤ)+2+1) (by omega)
      have han := prop78_classical_data_next_nonzero_of_not_hit (by omega) (by omega) ha hb hbn
        (hnot _ (by omega) (by omega))
      have he : ((n+1:ℕ):ℤ)+2=(n:ℤ)+2+1 := by omega
      rw [he]
      exact ⟨a,ha,han⟩
  have h := hall (N-2) (by omega)
  have he : ((N-2:ℕ):ℤ)+2=N := by omega
  rwa [he] at h


private theorem prop78_classical_data_nonzero_differential_not_zero {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
    (h : HasNonzeroDifferential E r p q x y)
    (hzero : HasDifferential E r p q x 0) : False := by
  classical
  obtain ⟨he,a,b,ha,hb,hd,hbn⟩ := h
  obtain ⟨he',a',b',ha',hb',hd'⟩ := hzero
  have haa : a=a' := represents_unique ha ha'
  have hbb : b'=0 := represents_unique hb' (RepresentsOnPage.zero hb'.1)
  apply hbn
  calc b = (E.d r p ≫ eqToHom (congrArg (E.Page r) he)) a := hd.symm
       _ = b' := by simpa only [haa] using hd'
       _ = 0 := hbb


private theorem prop78_classical_data_cycle_successor_lift
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((E.ssData p).Z ↑(r-E.r₀).toNat) : ModuleCat.{v} ℤ))
    (hz : E.d r p ((E.ssData p).pageπ ↑(r-E.r₀).toNat z) = 0) :
    ∃ zn : (Subobject.underlying.obj ((E.ssData p).Z ↑((r-E.r₀).toNat+1)) : ModuleCat.{v} ℤ),
      (Subobject.ofLE _ _ ((E.ssData p).Z_anti (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat))) zn = z := by
  classical
  let D := E.ssData p
  let n := (r-E.r₀).toNat
  have hsucc : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hsucc)
  have hker : D.pageπ ↑n z ∈ LinearMap.ker (E.d r p).hom := hz
  rw [←subobjectModule_kernel,E.Z_succ r p hr,subobjectModule_image] at hker
  obtain ⟨z',hz'⟩ := hker
  change D.pageπ ↑n (i z') = D.pageπ ↑n z at hz'
  have hzero : D.pageπ ↑n (z-i z')=0 := by rw [map_sub,hz',sub_self]
  have hb : ∃ b : (Subobject.underlying.obj (D.B ↑n) : ModuleCat.{v} ℤ),
      (Subobject.ofLE (D.B ↑n) (D.Z ↑n) (D.B_le_Z _)) b = z-i z' :=
    (cokernel_π_eq_zero_iff_mem_range _ _).mp hzero
  obtain ⟨b,hb⟩ := hb
  have hBZ : D.B ↑n ≤ D.Z ↑(n+1) := (D.B_mono hsucc).trans (D.B_le_Z _)
  let zn : (Subobject.underlying.obj (D.Z ↑(n+1)) : ModuleCat.{v} ℤ) :=
    z' + (Subobject.ofLE (D.B ↑n) (D.Z ↑(n+1)) hBZ) b
  have hnz : i zn=z := by
    dsimp only [zn]
    rw [map_add]
    change i z' + (Subobject.ofLE (D.B ↑n) (D.Z ↑(n+1)) hBZ ≫ i) b = z
    dsimp only [i]
    rw [Subobject.ofLE_comp_ofLE,hb]
    abel
  exact ⟨zn,hnz⟩


private theorem prop78_classical_data_reaches_before {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr : 2≤r) (hrt : r≤t) (ht : ReachesPage E t p x) : ReachesPage E r p x := by
  classical
  obtain ⟨a,_,z,hz,_⟩ := ht
  let D := E.ssData p
  have hrt' : (↑(r-E.r₀).toNat : WithTop ℕ)≤↑(t-E.r₀).toNat := by
    exact_mod_cast (show (r-E.r₀).toNat≤(t-E.r₀).toNat by omega)
  let zr := (Subobject.ofLE (D.Z ↑(t-E.r₀).toNat) (D.Z ↑(r-E.r₀).toNat) (D.Z_anti hrt')) z
  refine ⟨D.pageπ _ zr,hr,zr,?_,rfl⟩
  dsimp only [zr]
  rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
  exact hz


private theorem prop78_classical_data_later_page_frame_of_earlier {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr : 2≤r) (hrt : r≤t)
    (hframe : ∃ a : E.Page r p, RepresentsOnPage E r p x a ∧ ∀ y:E.Page r p,y=0∨y=a)
    (ht : ReachesPage E t p x) :
    ∃ a : E.Page t p, RepresentsOnPage E t p x a ∧ ∀ y:E.Page t p,y=0∨y=a := by
  classical
  obtain ⟨ar,har,hall⟩ := hframe
  obtain ⟨at',htrep⟩ := ht
  have htrep' := htrep
  obtain ⟨ht2,z,hzt,hat⟩ := htrep'
  let A := E.ssData p
  let nr : WithTop ℕ := ↑(r-E.r₀).toNat
  let nt : WithTop ℕ := ↑(t-E.r₀).toNat
  have hrt' : nr≤nt := by
    dsimp only [nr,nt]
    exact_mod_cast (show (r-E.r₀).toNat≤(t-E.r₀).toNat by omega)
  let i := Subobject.ofLE (A.Z nt) (A.Z nr) (A.Z_anti hrt')
  have har' : RepresentsOnPage E r p x (A.pageπ nr (i z)) := by
    refine ⟨hr,i z,?_,rfl⟩
    dsimp only [i]
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hzt
  have hzr : A.pageπ nr (i z)=ar := represents_unique har' har
  have hzero (w : (Subobject.underlying.obj (A.Z nt) : ModuleCat ℤ))
      (hw : A.pageπ nr (i w)=0) : A.pageπ nt w=0 := by
    apply (subobject_cokernel_π_eq_zero_iff (A.B nt) (A.Z nt) (A.B_le_Z _) _).mpr
    have hh := (subobject_cokernel_π_eq_zero_iff (A.B nr) (A.Z nr) (A.B_le_Z _) _).mp hw
    have he : (A.Z nr).arrow (i w)=(A.Z nt).arrow w :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow (A.Z_anti hrt')) w
    rw [he] at hh
    exact (ModuleCat.subobjectModule A.V).monotone (A.B_mono hrt') hh
  refine ⟨at',htrep,?_⟩
  intro y
  haveI : Epi (A.pageπ nt) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨w,hw⟩ := (ModuleCat.epi_iff_surjective (A.pageπ nt)).mp inferInstance y
  rcases hall (A.pageπ nr (i w)) with h0|ha
  · left
    rw [←hw]
    exact hzero w h0
  · right
    have hh : A.pageπ nr (i (w-z))=0 := by rw [map_sub,map_sub,ha,hzr,sub_self]
    have hh' := hzero (w-z) hh
    rw [map_sub,hw,hat,sub_eq_zero] at hh'
    exact hh'


private theorem prop78_classical_data_target_page_six_frame (I : KIP126.Computation.Route.Inputs D L G) :
    (∃ a : (sequence D .sphere).Page 6 (14,139),
      RepresentsOnPage (sequence D .sphere) 6 (14,139) (L.target M) a ∧
      ∀ y : (sequence D .sphere).Page 6 (14,139), y=0 ∨ y=a) ∧
    ReachesPage (sequence D .sphere) 1000 (14,139) (L.target M) := by
  classical
  classical

  have t_label (I : KIP126.Computation.Route.Inputs D L G) :
      I.realization.sphere 14 139 T = I.realization.basis .sphere 14 139 1 := by
    have hmem : (⟨.sphere,14,139,["449,1","1,1,7,1,275,1","0,2,425,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
      exact List.mem_of_getElem? (i := 217) (by rfl)
    have hc := I.csv _ hmem rfl
    obtain ⟨z,hz,he⟩ := hc (1 : Fin 3)
    have heq : T=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨1,by decide⟩ * (generator ⟨7,by decide⟩ * generator ⟨275,by decide⟩) = projection (monomialOfString "1,1,7,1,275,1")
      have hs : "1,1,7,1,275,1" ≠ "" := by decide
      have hp : (("1,1,7,1,275,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1,1,7,1,275,1] := by
        have split : "1,1,7,1,275,1".splitOn "," = ["1","1","7","1","275","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,mul_assoc]
    rw [heq]
    exact he

  have t_page6_frame (I : KIP126.Computation.Route.Inputs D L G) :
      ∃ a : (sequence D .sphere).Page 6 (14,139),
        RepresentsOnPage (sequence D .sphere) 6 (14,139) (I.realization.basis .sphere 14 139 1) a ∧
        ∀ y : (sequence D .sphere).Page 6 (14,139), y=0 ∨ y=a := by
    let E := sequence D .sphere
    have h342 : ReachesPage E 1000 (14,139) (I.realization.basis .sphere 14 139 1) := prop78_classical_data_h342_0 I
    have h341 : HasDifferential E 2 (12,138) (14,139)
        (I.realization.basis .sphere 12 138 1) (I.realization.basis .sphere 14 139 2) := prop78_classical_data_h341_1 I
    have h343 : HasDifferential E 2 (14,139) (16,140)
        (I.realization.basis .sphere 14 139 0) (I.realization.basis .sphere 16 140 2) := prop78_classical_data_h343_2 I
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,14,139,["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
      exact List.mem_of_getElem? (i := 217) (by rfl))
    change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
    change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 139 i.val at he
    have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 14 139 0 := he 0
    have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 14 139 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 14 139 2 := he 2
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere,16,140,["9,1,261,1", "1,1,438,1", "0,1,448,1", "0,2,440,1", "0,2,439,1"]⟩ (by
      exact List.mem_of_getElem? (i := 231) (by rfl))
    change E.Page 2 (16,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
    change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 140 i.val at hf
    have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 16 140 0 := hf 0
    have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 16 140 1 := hf 1
    have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 16 140 2 := hf 2
    have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 16 140 3 := hf 3
    have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 16 140 4 := hf 4
    obtain ⟨a1000,ha1000⟩ := h342
    obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤1000) ha1000
    have hz2 : RepresentsOnPage E 6 (14,139) (I.realization.basis .sphere 14 139 2) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h341
    have dz {x : E.Page 2 (14,139)} {b : E.Page 6 (14,139)}
        (hb : RepresentsOnPage E 6 (14,139) x b) : E.d 2 (14,139) x=0 := by
      obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hb
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<6) hb2 ⟨b,hb⟩
      simpa only [hb2.eq_on_page_two] using hh
    have hd0 : E.d 2 (14,139) (I.realization.basis .sphere 14 139 0)=I.realization.basis .sphere 16 140 2 := h343.eq_on_page_two.2
    have hd1 : E.d 2 (14,139) (I.realization.basis .sphere 14 139 1)=0 := dz ha
    have hd2 : E.d 2 (14,139) (I.realization.basis .sphere 14 139 2)=0 := dz hz2
    refine ⟨a,ha,?_⟩
    intro y
    let A := E.ssData (14,139)
    haveI : Epi (A.pageπ 4) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 4)).mp inferInstance y
    let x := (Subobject.ofLE (A.Z 4) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤4)) ≫ A.pageπ 0) z
    have hxrep : RepresentsOnPage E 6 (14,139) x y := ⟨by decide,z,rfl,hz⟩
    have hx : E.d 2 (14,139) x=0 := dz hxrep
    have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [Finsupp.single_apply]
    have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    generalize hc2 : e x 2=c2 at hxe
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      left
      apply represents_unique hxrep
      exact RepresentsOnPage.zero (by decide)
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      left
      apply represents_unique hxrep
      rw [he2]
      exact hz2
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      right
      apply represents_unique hxrep
      rw [he1]
      exact ha
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      right
      apply represents_unique hxrep
      rw [he1,he2]
      simpa only [add_zero] using represents_add_tail ha hz2
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      simp only [map_add, he0, hd0, zero_add, add_zero] at hx
      have hh := congrArg (fun y=>f y 2) hx
      rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      simp only [map_add, he0, he2, hd0, hd2, zero_add, add_zero] at hx
      have hh := congrArg (fun y=>f y 2) hx
      rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      simp only [map_add, he0, he1, hd0, hd1, zero_add, add_zero] at hx
      have hh := congrArg (fun y=>f y 2) hx
      rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx hxrep
      simp only [map_add, he0, he1, he2, hd0, hd1, hd2, zero_add, add_zero] at hx
      have hh := congrArg (fun y=>f y 2) hx
      rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
  obtain ⟨a,ha,hall⟩ := t_page6_frame I
  have hlabel := (route_expression_labels I).2.2
  have hl : L.target M = I.realization.basis .sphere 14 139 1 := hlabel.symm.trans (t_label I)
  constructor
  · exact ⟨a,by rw [hl]; exact ha,hall⟩
  let E := sequence D .sphere
  have h342 : ReachesPage E 1000 (14,139) (I.realization.basis .sphere 14 139 1) := prop78_classical_data_h342_3 I
  rw [hl]
  exact h342


private theorem prop78_classical_data_h6_twelve_outgoing_nonzero
    (h12 : SurvivesTo (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      12 (2,128) (Sphere.Internal.hiSquare H M 6))
    (h13 : ¬SurvivesTo (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      13 (2,128) (Sphere.Internal.hiSquare H M 6)) :
    ∃ a, RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      12 (2,128) (Sphere.Internal.hiSquare H M 6) a ∧
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d 12 (2,128) a≠0 := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit (SphereSpectrum (C:=C))
  obtain ⟨a,ha,hane⟩ := h12
  refine ⟨a,ha,?_⟩
  intro hzero
  have ha' := ha
  obtain ⟨_,z,hz2,hza⟩ := ha'
  have hz : E.d 12 (2,128) ((E.ssData (2,128)).pageπ 10 z)=0 := by
    change E.d 12 (2,128) ((E.ssData (2,128)).pageπ ↑(12-E.r₀).toNat z)=0
    rw [hza]
    exact hzero
  obtain ⟨zn,hnz⟩ := prop78_classical_data_cycle_successor_lift E 12 (by change (2:ℤ)≤12; omega) (2,128) z hz
  let A := E.ssData (2,128)
  change (Subobject.ofLE (A.Z 11) (A.Z 10) (A.Z_anti (by decide : (10:WithTop ℕ)≤11))) zn=z at hnz
  let b := A.pageπ 11 zn
  have hb : RepresentsOnPage E 13 (2,128) (Sphere.Internal.hiSquare H M 6) b := by
    refine ⟨by decide,zn,?_,rfl⟩
    calc
      (Subobject.ofLE (A.Z 11) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤11)) ≫ A.pageπ 0) zn =
        (Subobject.ofLE (A.Z 10) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤10)) ≫ A.pageπ 0)
          ((Subobject.ofLE (A.Z 11) (A.Z 10) (A.Z_anti (by decide : (10:WithTop ℕ)≤11))) zn) := by
          rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
      _ = _ := by rw [hnz]; exact hz2
  have hnot : ¬HitOnPage E 12 (2,128) (Sphere.Internal.hiSquare H M 6) := by
    rintro ⟨q,hq,c,d,hd,hdne,hcd⟩
    have hfst : q.1+12=2 := congrArg Prod.fst hq
    haveI : Subsingleton (E.Page 12 q) :=
      adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
        12 q.1 q.2 (by omega)
    rw [Subsingleton.elim c 0,map_zero] at hcd
    exact hdne hcd.symm
  have hbn : b≠0 := prop78_classical_data_next_nonzero_of_not_hit (by change (2:ℤ)≤12; omega : E.r₀≤12)
    (by decide : (2:ℤ)≤12) hb ha hane hnot
  exact h13 ⟨b,hb,hbn⟩


private theorem prop78_classical_data_target_page_twelve_frame (I : KIP126.Computation.Route.Inputs D L G) :
    ∃ a : (sequence D .sphere).Page 12 (14,139),
      RepresentsOnPage (sequence D .sphere) 12 (14,139) (L.target M) a ∧
      ∀ y : (sequence D .sphere).Page 12 (14,139), y=0 ∨ y=a := by
  classical
  obtain ⟨hframe,hreach⟩ := prop78_classical_data_target_page_six_frame I
  exact prop78_classical_data_later_page_frame_of_earlier (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤12)
    hframe (prop78_classical_data_reaches_before (by decide : (2:ℤ)≤12) (by decide : (12:ℤ)≤1000) hreach)


private theorem prop78_classical_data_survives_twelve_not_thirteen_d12 (I : KIP126.Computation.Route.Inputs D L G)
    (h12 : SurvivesTo (sequence D .sphere)
      12 (2,128) (Sphere.Internal.hiSquare H M 6))
    (h13 : ¬SurvivesTo (sequence D .sphere)
      13 (2,128) (Sphere.Internal.hiSquare H M 6)) : D12 M L := by
  classical
  obtain ⟨a,ha,hdne⟩ := prop78_classical_data_h6_twelve_outgoing_nonzero h12 h13
  obtain ⟨b,hb,hall⟩ := prop78_classical_data_target_page_twelve_frame I
  have hdb : (sequence D .sphere).d 12 (2,128) a=b :=
    (hall ((sequence D .sphere).d 12 (2,128) a)).resolve_left hdne
  refine ⟨rfl,a,b,ha,hb,?_,?_⟩
  · simp only [eqToHom_refl,Category.comp_id]
    exact hdb
  · intro hb0
    exact hdne (hdb.trans hb0)


private theorem bx_lambda_nine_not_ten_d12
    (I : KIP126.Computation.Route.Inputs D L G)
    (comparison : KIP126.Comparison.ClassicalSynthetic.SphereFirstQuotientComparison H Syn)
    (η : KIP126.Kervaire.SyntheticTheta5.Eta Syn)
    (θ : KIP126.Kervaire.SyntheticTheta5.Theta Syn)
    (hBX : KIP126.Kervaire.BJMOriginalCriterion H M comparison η θ)
    (h9 : KIP126.Synthetic.Context.VanishesModLambda 9
      (KIP126.Kervaire.SyntheticTheta5.etaThetaSquare η θ))
    (h10 : ¬KIP126.Synthetic.Context.VanishesModLambda 10
      (KIP126.Kervaire.SyntheticTheta5.etaThetaSquare η θ)) : D12 M L := by
  classical
  have h12 := (hBX.2.2.2 9 (by omega)).mpr h9

  have h13 : ¬SurvivesTo (sequence D .sphere) 13 (2,128) (Sphere.Internal.hiSquare H M 6) := by
    classical
    intro hh
    exact h10 ((hBX.2.2.2 10 (by omega)).mp hh)

  classical
  exact prop78_classical_data_survives_twelve_not_thirteen_d12 I h12 h13

private theorem c3_iff_target_survives_twelve
    (I : KIP126.Computation.Route.Inputs D L G) (SF : Derived.SphereFacts I.realization) :
    C3 L ↔ SurvivesTo (sequence D .sphere) 12 (14,139) (L.target M) := by
  classical
  have labels := route_expression_labels I

  have hW : SurvivesTo (sequence D .sphere) 6 (8,134) L.W := by
    classical
    have hw := SF.w_to_e6
    change SurvivesTo (sequence D .sphere) 6 (8,134) (I.realization.sphere 8 134 W) at hw
    rwa [labels.1] at hw

  have htargets : DifferentialTargets (sequence D .sphere) 6 (8,134) L.W (L.target M) := by
    classical
    simpa only [labels.1, labels.2.2] using SF.w_d6_targets

  classical
  constructor
  · intro hc3
    have hp := SF.t_permanent_cycle
    rw [labels.2.2] at hp
    have hn : L.target M≠0 := by
      intro hz
      apply SF.t_not_h0_multiple
      refine ⟨0,?_⟩
      rw [labels.2.2,hz]
      simp only [Sphere.Internal.product,map_zero]
    apply prop78_classical_data_permanent_survives_of_no_early_hit (by change (2:ℤ)≤2; decide) 12 (by decide) hp hn
    intro r hr hr12 hit
    rw [←labels.2.2] at hit
    rcases SF.t_only_incoming r hit with ⟨he,hd⟩ | ⟨he,_⟩
    · subst r
      change HasNonzeroDifferential (sequence D .sphere) 6 (8,134) (14,139)
        (I.realization.sphere 8 134 W) (I.realization.sphere 14 139 T) at hd
      rw [labels.1,labels.2.2] at hd
      exact prop78_classical_data_nonzero_differential_not_zero hd hc3
    · omega
  · intro hs
    exact prop78_classical_data_earlier_zero_of_target_survives
      (E:=sequence D .sphere) (r:=6) (t:=12)
      (by change (2:ℤ)≤6; decide) (by decide) hW htargets hs

private theorem d12_necessary_from_sphere_facts
    (I : KIP126.Computation.Route.Inputs D L G) (SF : Derived.SphereFacts I.realization)
    (hd : D12 M L) : ¬ PermanentH6Square M ∧ C3 L := by
  classical
  have labels := route_expression_labels I

  classical
  refine ⟨?_, ?_⟩
  · exact prop78_classical_data_nonzero_differential_not_permanent (by change (2 : ℤ) ≤ 12; decide) hd
  · have hW : SurvivesTo (sequence D .sphere) 6 (8,134) L.W := by
      have hw := SF.w_to_e6
      change SurvivesTo (sequence D .sphere) 6 (8,134) (I.realization.sphere 8 134 W) at hw
      rwa [labels.1] at hw
    have htargets : DifferentialTargets (sequence D .sphere) 6 (8,134) L.W (L.target M) := by
      simpa only [labels.1, labels.2.2] using SF.w_d6_targets
    exact prop78_classical_data_earlier_zero_of_target_survives
      (E := sequence D .sphere) (r := 6) (t := 12)
      (by change (2 : ℤ) ≤ 6; decide) (by decide) hW htargets hd.target_survives

private theorem prop78_classical_data (I : KIP126.Computation.Route.Inputs D L G)
    (SF : Derived.SphereFacts I.realization) :
    (C3 L ↔ SurvivesTo (sequence D .sphere) 12 (14,139) (L.target M)) ∧
    (D12 M L → ¬PermanentH6Square M ∧ C3 L) ∧
    (∀ (eta : BiHom 1 2 (S_0_0 : Syn)) (theta : BiHom 62 64 (S_0_0 : Syn)),
      BJMOriginalCriterion H M D.sphereFirstQuotient eta theta →
      VanishesModLambda 9 (sphereProduct eta (sphereProduct theta theta)) →
      ¬VanishesModLambda 10 (sphereProduct eta (sphereProduct theta theta)) → D12 M L) ∧
    ((∃ a : (sequence D .sphere).Page 6 (14,139),
      RepresentsOnPage (sequence D .sphere) 6 (14,139) (L.target M) a ∧
      ∀ y : (sequence D .sphere).Page 6 (14,139),y=0∨y=a) ∧
      ReachesPage (sequence D .sphere) 1000 (14,139) (L.target M)) := by
  classical
  exact ⟨c3_iff_target_survives_twelve I SF,d12_necessary_from_sphere_facts I SF,
    fun eta theta h h9 h10=>bx_lambda_nine_not_ten_d12 I D.sphereFirstQuotient eta theta h h9 h10,
    prop78_classical_data_target_page_six_frame I⟩
end
end KIP126.Main.Solution.Route

namespace KIP126.Main.Solution.Route
open KIP126.Core.SpectralSequence.FinitePageCalculus
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route KIP126.Algebra
open KIP126.LinE2 KIP126.Computation.Near126 KIP126.Computation.Route
noncomputable section
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
  {L : Labels H} {G : TmfLabels H} {η : BiHom 1 2 (S_0_0:Syn)}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem prop78_choice_invariance_h365_0 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (1,64) (3,65) (I.realization.basis .sphere 1 64 0) (I.realization.basis .sphere 3 65 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 1, 64, [0], 3, 65, [0], "S0_AdamsE2_ss", 401⟩ (by
    exact List.mem_of_getElem? (i := 142) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (1,64) (3,65) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 1 64 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 3 65 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem prop78_choice_invariance_h466_1 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (2,65) (4,66) (I.realization.basis .sphere 2 65 0) (I.realization.basis .sphere 4 66 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 2, 65, [0], 4, 66, [0], "S0_AdamsE2_ss", 417⟩ (by
    exact List.mem_of_getElem? (i := 145) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (2,65) (4,66) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 2 65 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 4 66 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem prop78_choice_invariance_h567_2 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (3,66) (5,67) (I.realization.basis .sphere 3 66 1) (I.realization.basis .sphere 5 67 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 3, 66, [1], 5, 67, [2], "S0_AdamsE2_ss", 437⟩ (by
    exact List.mem_of_getElem? (i := 150) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (3,66) (5,67) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 66 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 5 67 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem prop78_choice_invariance_h3_3 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 3 (5,67) (8,69) (I.realization.basis .sphere 5 67 1) (I.realization.basis .sphere 8 69 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 5, 67, [1], 8, 69, [0], "S0_AdamsE2_ss", 453⟩ (by
    exact List.mem_of_getElem? (i := 160) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (5,67) (8,69) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 67 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 8 69 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem prop78_choice_invariance_h668_4 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (4,67) (6,68) (I.realization.basis .sphere 4 67 0) (I.realization.basis .sphere 6 68 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 4, 67, [0], 6, 68, [1], "S0_AdamsE2_ss", 455⟩ (by
    exact List.mem_of_getElem? (i := 155) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (4,67) (6,68) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 67 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 6 68 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem prop78_choice_invariance_choice_differential_target_later_zero {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
    (hr0 : E.r₀ ≤ r) (hrt : r < t)
    (h : HasDifferential E r p q x y) : RepresentsOnPage E t q y 0 := by
  classical
  obtain ⟨rfl, xr, yr, hx, hy, hd⟩ := h
  simp only [eqToHom_refl, Category.comp_id] at hd
  obtain ⟨hr, z, hz2, hzr⟩ := hy
  let A := E.ssData (p + E.diffDeg r)
  let n : ℕ := (r-E.r₀).toNat
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  let m : WithTop ℕ := ↑(t-E.r₀).toNat
  have hnm : (↑(n+1) : WithTop ℕ) ≤ m := by
    dsimp only [n,m]
    exact_mod_cast (show (r-E.r₀).toNat+1 ≤ (t-E.r₀).toNat by omega)
  have hn0 : n₀ ≤ ↑n := by
    dsimp only [n₀,n]
    exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega)
  have hn1 : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  have hdmem : yr ∈ LinearMap.range (E.d r p).hom := ⟨xr, hd⟩
  rw [← subobjectModule_image, E.B_succ r p hr0, subobjectModule_image] at hdmem
  obtain ⟨b, hb⟩ := hdmem
  let j := Subobject.ofLE (A.B ↑(n+1)) (A.Z ↑n)
    ((A.B_le_Z _).trans (A.Z_anti hn1))
  have hb' : A.pageπ ↑n (j b) = yr := hb
  have hdif : A.pageπ ↑n (z-j b) = 0 := by rw [map_sub, hzr, hb', sub_self]
  have hmem := (subobject_cokernel_π_eq_zero_iff (A.B ↑n) (A.Z ↑n) (A.B_le_Z _) _).mp hdif
  have hmem' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono hn1) hmem
  have hj : (A.Z ↑n).arrow (j b) ∈ (ModuleCat.subobjectModule A.V) (A.B ↑(n+1)) := by
    change (j ≫ (A.Z ↑n).arrow) b ∈ _
    dsimp only [j]
    rw [Subobject.ofLE_arrow]
    exact ⟨b,rfl⟩
  have hzmem := ((ModuleCat.subobjectModule A.V) (A.B ↑(n+1))).add_mem hmem' hj
  rw [map_sub, sub_add_cancel] at hzmem
  obtain ⟨b', hb'⟩ := hzmem
  let i := Subobject.ofLE (A.B ↑(n+1)) (A.Z m) ((A.B_mono hnm).trans (A.B_le_Z _))
  refine ⟨by omega, i b', ?_, ?_⟩
  · have he : (Subobject.ofLE (A.Z m) (A.Z n₀) (A.Z_anti (hn0.trans (hn1.trans hnm))))
        (i b') = (Subobject.ofLE (A.Z ↑n) (A.Z n₀) (A.Z_anti hn0)) z := by
      apply (ModuleCat.mono_iff_injective (A.Z n₀).arrow).mp inferInstance
      change (i ≫ Subobject.ofLE (A.Z m) (A.Z n₀) _ ≫ (A.Z n₀).arrow) b' =
        (Subobject.ofLE (A.Z ↑n) (A.Z n₀) _ ≫ (A.Z n₀).arrow) z
      simpa only [Category.assoc, i, Subobject.ofLE_arrow] using hb'
    exact (congrArg (fun v => A.pageπ n₀ v) he).trans hz2
  · apply (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z _) _).mpr
    change (i ≫ (A.Z m).arrow) b' ∈ _
    dsimp only [i]
    rw [Subobject.ofLE_arrow]
    exact (ModuleCat.subobjectModule A.V).monotone (A.B_mono hnm) ⟨b',rfl⟩


private theorem prop78_choice_invariance_choice_nonzero_differential_not_permanent {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q} (hr0 : E.r₀ ≤ r)
    (h : HasNonzeroDifferential E r p q x y) : ¬ NonzeroSurvival E p x := by
  classical
  rintro ⟨z, hz, _⟩
  let A := E.ssData p
  let n : WithTop ℕ := ↑(r + 1 - E.r₀).toNat
  let z' := (Subobject.ofLE (A.Z ⊤) (A.Z n) (A.Z_anti le_top)) z
  obtain ⟨hdeg, xr, yr, hx, hy, hd, hne⟩ := h
  have hr2 := hx.1
  have hlater : ReachesPage E (r + 1) p x := by
    refine ⟨A.pageπ n z', by omega, z', ?_, rfl⟩
    dsimp only [z']
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  have hd0 := represents_d_zero_of_later hr0 (by omega : r < r + 1) hx hlater
  rw [ModuleCat.comp_apply, hd0, map_zero] at hd
  exact hne hd.symm


private theorem prop78_choice_invariance_choice_earlier_zero_of_target_survives {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr0 : E.r₀ ≤ r) (hrt : r < t)
    {y : E.Page 2 (p + E.diffDeg r)}
    (hsource : SurvivesTo E r p x)
    (htargets : DifferentialTargets E r p x y)
    (htarget : SurvivesTo E t (p + E.diffDeg r) y) :
    HasDifferential E r p (p + E.diffDeg r) x 0 := by
  classical
  obtain ⟨xr, hxr, _⟩ := hsource
  have hd0 : E.d r p xr = 0 := by
    rcases htargets xr hxr with hz | ⟨yr, hyr, hdr⟩
    · exact hz
    · have hd : HasDifferential E r p (p + E.diffDeg r) x y :=
        ⟨rfl, xr, yr, hxr, hyr, by simpa only [eqToHom_refl, Category.comp_id] using hdr⟩
      have hlater := prop78_choice_invariance_choice_differential_target_later_zero hr0 hrt hd
      obtain ⟨yt, hyt, hne⟩ := htarget
      exact False.elim (hne (represents_unique hyt hlater))
  exact ⟨rfl, xr, 0, hxr, RepresentsOnPage.zero hxr.1,
    by simpa only [eqToHom_refl, Category.comp_id] using hd0⟩


private theorem prop78_choice_invariance_choice_next_projection_zero_iff_incoming
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((E.ssData (p+E.diffDeg r)).Z
      ↑((r-E.r₀).toNat+1)) : ModuleCat ℤ)) :
    (E.ssData (p+E.diffDeg r)).pageπ ↑((r-E.r₀).toNat+1) z = 0 ↔
      (Subobject.ofLE _ _ ((E.ssData (p+E.diffDeg r)).Z_anti
        (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
          (E.ssData (p+E.diffDeg r)).pageπ ↑(r-E.r₀).toNat) z ∈
        LinearMap.range (E.d r p).hom := by
  classical
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


private theorem prop78_choice_invariance_choice_next_nonzero_of_not_hit {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr0 : E.r₀ ≤ r) (hr : 2 ≤ r)
    {a : E.Page (r+1) p} {b : E.Page r p}
    (ha : RepresentsOnPage E (r+1) p x a) (hb : RepresentsOnPage E r p x b)
    (hne : b ≠ 0) (hnot : ¬ HitOnPage E r p x) : a ≠ 0 := by
  classical
  generalize hq : p-E.diffDeg r=q
  have hp : p=q+E.diffDeg r := by rw [←hq]; abel
  subst p
  obtain ⟨_,z,hz,hza⟩ := ha
  let A := E.ssData (q+E.diffDeg r)
  have hi : (r+1-E.r₀).toNat=(r-E.r₀).toNat+1 := by omega
  have hnm : (↑(r-E.r₀).toNat : WithTop ℕ) ≤ ↑(r+1-E.r₀).toNat := by
    exact_mod_cast (show (r-E.r₀).toNat≤(r+1-E.r₀).toNat by omega)
  let br := (Subobject.ofLE _ _ (A.Z_anti hnm) ≫ A.pageπ ↑(r-E.r₀).toNat) z
  have hbr : RepresentsOnPage E r (q+E.diffDeg r) x br := by
    refine ⟨hr, (Subobject.ofLE _ _ (A.Z_anti hnm)) z, ?_, rfl⟩
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  have heb : br=b := represents_unique hbr hb
  intro ha0
  have hv := prop78_choice_invariance_choice_next_projection_zero_iff_incoming E r hr0 q
  have hv' : ∀ zz : (Subobject.underlying.obj (A.Z ↑(r+1-E.r₀).toNat) : ModuleCat ℤ),
      A.pageπ ↑(r+1-E.r₀).toNat zz=0 ↔
        (Subobject.ofLE _ _ (A.Z_anti hnm) ≫ A.pageπ ↑(r-E.r₀).toNat) zz∈
          LinearMap.range (E.d r q).hom := by
    have transport (m : ℕ) (hm : m=(r-E.r₀).toNat+1)
        (hge : (↑(r-E.r₀).toNat : WithTop ℕ)≤↑m) :
        ∀ zz : (Subobject.underlying.obj (A.Z ↑m) : ModuleCat ℤ),
          A.pageπ ↑m zz=0 ↔
            (Subobject.ofLE _ _ (A.Z_anti hge) ≫ A.pageπ ↑(r-E.r₀).toNat) zz∈
              LinearMap.range (E.d r q).hom := by
      subst m
      exact hv
    exact transport _ hi hnm
  have hmem : br∈LinearMap.range (E.d r q).hom := by
    exact (hv' z).mp (hza.trans ha0)
  obtain ⟨c,hc⟩ := hmem
  apply hnot
  refine ⟨q, rfl, c,b,hb,hne,?_⟩
  simpa only [eqToHom_refl, Category.comp_id] using hc.trans heb


private theorem prop78_choice_invariance_choice_permanent_survives_of_no_early_hit {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hstart : E.r₀≤2) (N : ℕ) (hN : 2≤N)
    (hperm : IsPermanentCycle E p x) (hne : x≠0)
    (hnot : ∀ r : ℤ, 2≤r → r<N → ¬HitOnPage E r p x) :
    SurvivesTo E N p x := by
  classical
  obtain ⟨z,hz⟩ := hperm
  let A := E.ssData p
  have hrep (r : ℤ) (hr : 2≤r) : ReachesPage E r p x := by
    let zr := (Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-E.r₀).toNat) (A.Z_anti le_top)) z
    refine ⟨A.pageπ _ zr,hr,zr,?_,rfl⟩
    dsimp only [zr]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    exact hz
  have hall (n : ℕ) : n+2≤N → SurvivesTo E ((n:ℤ)+2) p x := by
    induction n with
    | zero =>
      intro hn
      obtain ⟨a,ha⟩ := hrep 2 (by omega)
      change SurvivesTo E 2 p x
      exact ⟨a,ha,by rw [←ha.eq_on_page_two]; exact hne⟩
    | succ n ih =>
      intro hn
      obtain ⟨b,hb,hbn⟩ := ih (by omega)
      obtain ⟨a,ha⟩ := hrep ((n:ℤ)+2+1) (by omega)
      have han := prop78_choice_invariance_choice_next_nonzero_of_not_hit (by omega) (by omega) ha hb hbn
        (hnot _ (by omega) (by omega))
      have he : ((n+1:ℕ):ℤ)+2=(n:ℤ)+2+1 := by omega
      rw [he]
      exact ⟨a,ha,han⟩
  have h := hall (N-2) (by omega)
  have he : ((N-2:ℕ):ℤ)+2=N := by omega
  rwa [he] at h


private theorem prop78_choice_invariance_choice_nonzero_differential_not_zero {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {p : ℤ × ℤ} {q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
    (h : HasNonzeroDifferential E r p q x y)
    (hzero : HasDifferential E r p q x 0) : False := by
  classical
  obtain ⟨he,a,b,ha,hb,hd,hbn⟩ := h
  obtain ⟨he',a',b',ha',hb',hd'⟩ := hzero
  have haa : a=a' := represents_unique ha ha'
  have hbb : b'=0 := represents_unique hb' (RepresentsOnPage.zero hb'.1)
  apply hbn
  calc b = (E.d r p ≫ eqToHom (congrArg (E.Page r) he)) a := hd.symm
       _ = b' := by simpa only [haa] using hd'
       _ = 0 := hbb


private theorem prop78_choice_invariance_choice_cycle_successor_lift
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (r : ℤ) (hr : E.r₀ ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj ((E.ssData p).Z ↑(r-E.r₀).toNat) : ModuleCat.{v} ℤ))
    (hz : E.d r p ((E.ssData p).pageπ ↑(r-E.r₀).toNat z) = 0) :
    ∃ zn : (Subobject.underlying.obj ((E.ssData p).Z ↑((r-E.r₀).toNat+1)) : ModuleCat.{v} ℤ),
      (Subobject.ofLE _ _ ((E.ssData p).Z_anti (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat))) zn = z := by
  classical
  let D := E.ssData p
  let n := (r-E.r₀).toNat
  have hsucc : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hsucc)
  have hker : D.pageπ ↑n z ∈ LinearMap.ker (E.d r p).hom := hz
  rw [←subobjectModule_kernel,E.Z_succ r p hr,subobjectModule_image] at hker
  obtain ⟨z',hz'⟩ := hker
  change D.pageπ ↑n (i z') = D.pageπ ↑n z at hz'
  have hzero : D.pageπ ↑n (z-i z')=0 := by rw [map_sub,hz',sub_self]
  have hb : ∃ b : (Subobject.underlying.obj (D.B ↑n) : ModuleCat.{v} ℤ),
      (Subobject.ofLE (D.B ↑n) (D.Z ↑n) (D.B_le_Z _)) b = z-i z' :=
    (cokernel_π_eq_zero_iff_mem_range _ _).mp hzero
  obtain ⟨b,hb⟩ := hb
  have hBZ : D.B ↑n ≤ D.Z ↑(n+1) := (D.B_mono hsucc).trans (D.B_le_Z _)
  let zn : (Subobject.underlying.obj (D.Z ↑(n+1)) : ModuleCat.{v} ℤ) :=
    z' + (Subobject.ofLE (D.B ↑n) (D.Z ↑(n+1)) hBZ) b
  have hnz : i zn=z := by
    dsimp only [zn]
    rw [map_add]
    change i z' + (Subobject.ofLE (D.B ↑n) (D.Z ↑(n+1)) hBZ ≫ i) b = z
    dsimp only [i]
    rw [Subobject.ofLE_comp_ofLE,hb]
    abel
  exact ⟨zn,hnz⟩


private theorem prop78_choice_invariance_choice_later_page_frame_of_earlier {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)} {r : ℤ} {t : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p}
    (hr : 2≤r) (hrt : r≤t)
    (hframe : ∃ a : E.Page r p, RepresentsOnPage E r p x a ∧ ∀ y:E.Page r p,y=0∨y=a)
    (ht : ReachesPage E t p x) :
    ∃ a : E.Page t p, RepresentsOnPage E t p x a ∧ ∀ y:E.Page t p,y=0∨y=a := by
  classical
  obtain ⟨ar,har,hall⟩ := hframe
  obtain ⟨at',htrep⟩ := ht
  have htrep' := htrep
  obtain ⟨ht2,z,hzt,hat⟩ := htrep'
  let A := E.ssData p
  let nr : WithTop ℕ := ↑(r-E.r₀).toNat
  let nt : WithTop ℕ := ↑(t-E.r₀).toNat
  have hrt' : nr≤nt := by
    dsimp only [nr,nt]
    exact_mod_cast (show (r-E.r₀).toNat≤(t-E.r₀).toNat by omega)
  let i := Subobject.ofLE (A.Z nt) (A.Z nr) (A.Z_anti hrt')
  have har' : RepresentsOnPage E r p x (A.pageπ nr (i z)) := by
    refine ⟨hr,i z,?_,rfl⟩
    dsimp only [i]
    rw [←CategoryTheory.comp_apply,←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hzt
  have hzr : A.pageπ nr (i z)=ar := represents_unique har' har
  have hzero (w : (Subobject.underlying.obj (A.Z nt) : ModuleCat ℤ))
      (hw : A.pageπ nr (i w)=0) : A.pageπ nt w=0 := by
    apply (subobject_cokernel_π_eq_zero_iff (A.B nt) (A.Z nt) (A.B_le_Z _) _).mpr
    have hh := (subobject_cokernel_π_eq_zero_iff (A.B nr) (A.Z nr) (A.B_le_Z _) _).mp hw
    have he : (A.Z nr).arrow (i w)=(A.Z nt).arrow w :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow (A.Z_anti hrt')) w
    rw [he] at hh
    exact (ModuleCat.subobjectModule A.V).monotone (A.B_mono hrt') hh
  refine ⟨at',htrep,?_⟩
  intro y
  haveI : Epi (A.pageπ nt) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨w,hw⟩ := (ModuleCat.epi_iff_surjective (A.pageπ nt)).mp inferInstance y
  rcases hall (A.pageπ nr (i w)) with h0|ha
  · left
    rw [←hw]
    exact hzero w h0
  · right
    have hh : A.pageπ nr (i (w-z))=0 := by rw [map_sub,map_sub,ha,hzr,sub_self]
    have hh' := hzero (w-z) hh
    rw [map_sub,hw,hat,sub_eq_zero] at hh'
    exact hh'


private theorem prop78_choice_invariance_choice_theta_choice_late_page_generic
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (hr0 : E.r₀≤2) (hdeg2 : E.diffDeg 2=(2,1))
    (b5 : Fin 3 → E.Page 2 (5,67)) (b6 : Fin 2 → E.Page 2 (6,68))
    (b7 : Fin 2 → E.Page 2 (7,68)) (b8 : Fin 1 → E.Page 2 (8,69))
    (e5 : E.Page 2 (5,67) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Core.Algebra.F2))
    (he5 : ∀i:Fin 3, e5.symm (Finsupp.single i 1)=b5 i)
    (e6 : E.Page 2 (6,68) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Core.Algebra.F2))
    (he6 : ∀i:Fin 2, e6.symm (Finsupp.single i 1)=b6 i)
    (e7 : E.Page 2 (7,68) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Core.Algebra.F2))
    (he7 : ∀i:Fin 2, e7.symm (Finsupp.single i 1)=b7 i)
    (e8 : E.Page 2 (8,69) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2))
    (he8 : ∀i:Fin 1, e8.symm (Finsupp.single i 1)=b8 i)
    (h3 : HasDifferential E 3 (5,67) (8,69) (b5 1) (b8 0))
    (h2out : HasDifferential E 2 (5,67) (7,68) (b5 0) (b7 0+b7 1))
    (hz567 : RepresentsOnPage E 3 (5,67) (b5 2) 0)
    (hd60 : E.d 2 (6,68) (b6 0)=0)
    (hd61 : E.d 2 (6,68) (b6 1)=0) :
    Subsingleton (E.Page 4 (5,67)) := by
  classical
  classical
  change E.d 2 (6,68) (b6 0)=0 at hd60
  change E.d 2 (6,68) (b6 1)=0 at hd61
  have he60 : e6.symm (Finsupp.single 0 1)=b6 0 := he6 0
  have he61 : e6.symm (Finsupp.single 1 1)=b6 1 := he6 1
  have he70 : e7.symm (Finsupp.single 0 1)=b7 0 := he7 0
  have he71 : e7.symm (Finsupp.single 1 1)=b7 1 := he7 1
  have he80 : e8.symm (Finsupp.single 0 1)=b8 0 := he8 0
  have hd6 (x:E.Page 2 (6,68)) : E.d 2 (6,68) x=0 := by
    have hex : e6 x=Finsupp.single 0 (e6 x 0)+Finsupp.single 1 (e6 x 1) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hx : x=e6.symm (Finsupp.single 0 (e6 x 0)+Finsupp.single 1 (e6 x 1)) := by
      rw [←hex,LinearEquiv.symm_apply_apply]
    generalize h0 : e6 x 0=c0 at hx
    generalize h1 : e6 x 1=c1 at hx
    fin_cases c0 <;> fin_cases c1
    · change x=e6.symm (Finsupp.single 0 (0:KIP126.Core.Algebra.F2)+Finsupp.single 1 (0:KIP126.Core.Algebra.F2)) at hx
      simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he60,he61] at hx
      rw [hx]
      simp only [map_add,map_zero,hd60,hd61,add_zero]
    · change x=e6.symm (Finsupp.single 0 (0:KIP126.Core.Algebra.F2)+Finsupp.single 1 (1:KIP126.Core.Algebra.F2)) at hx
      simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he60,he61] at hx
      rw [hx]
      simp only [map_add,map_zero,hd60,hd61,add_zero]
    · change x=e6.symm (Finsupp.single 0 (1:KIP126.Core.Algebra.F2)+Finsupp.single 1 (0:KIP126.Core.Algebra.F2)) at hx
      simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he60,he61] at hx
      rw [hx]
      simp only [map_add,map_zero,hd60,hd61,add_zero]
    · change x=e6.symm (Finsupp.single 0 (1:KIP126.Core.Algebra.F2)+Finsupp.single 1 (1:KIP126.Core.Algebra.F2)) at hx
      simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he60,he61] at hx
      rw [hx]
      simp only [map_add,map_zero,hd60,hd61,add_zero]
  obtain ⟨heq,a3,b3,ha3,hb3,hdb⟩ := h3
  have hne2 : b8 0≠0 := by
    intro hz
    have he := congrArg (fun v=>e8 v 0) hz
    rw [←he80,LinearEquiv.apply_symm_apply,e8.map_zero] at he
    norm_num at he
  have hnot : ¬HitOnPage E 2 (8,69) (b8 0) := by
    rintro ⟨q,hq,c,d,hd,hdne,hcd⟩
    have hq' : q=(6,68) := by
      rw [hdeg2] at hq
      apply Prod.ext
      · have h := congrArg Prod.fst hq
        change q.1+2=8 at h
        omega
      · have h := congrArg Prod.snd hq
        change q.2+(2-1)=69 at h
        omega
    subst q
    change (eqToHom (congrArg (E.Page 2) hq)) (E.d 2 (6,68) c)=d at hcd
    rw [hd6,map_zero] at hcd
    exact hdne hcd.symm
  obtain ⟨b2,hb2⟩ := reaches_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) ⟨b3,hb3⟩
  have hbn : b3≠0 := prop78_choice_invariance_choice_next_nonzero_of_not_hit hr0
    (by decide : (2:ℤ)≤2) hb3 hb2 (by rw [←hb2.eq_on_page_two]; exact hne2) hnot
  have hd0 : E.d 2 (5,67) (b5 0)≠0 := by
    intro h0
    have h := h2out.eq_on_page_two.2
    change (eqToHom (congrArg (E.Page 2) h2out.1)) (E.d 2 (5,67) (b5 0))=b7 0+b7 1 at h
    rw [h0,map_zero] at h
    have he := congrArg (fun v=>e7 v 0) h
    rw [e7.map_zero,e7.map_add,←he70,←he71,LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply] at he
    norm_num at he
  have hall := choice_frame_of_three_basis (E:=E) (r:=3) (p:=(5,67)) (by decide : (2:ℤ)<3)
    hr0 e5 _ _ _ (he5 0) (he5 1) (he5 2) a3 ha3 hz567 hd0
  have hdn : E.d 3 (5,67) a3≠0 := by
    intro hz
    apply hbn
    rw [←hdb]
    change (eqToHom (congrArg (E.Page 3) heq)) (E.d 3 (5,67) a3)=0
    rw [hz,map_zero]
  exact choice_next_zero_of_single_frame_nonzero_differential (E:=E) (r:=3) (p:=(5,67)) (by decide : (2:ℤ)≤3)
    (by omega : E.r₀≤3) a3 hdn hall


private theorem prop78_choice_invariance_choice_theta_choice_raw_relations (I : KIP126.Computation.Route.Inputs D L G) :
    HasDifferential (sequence D .sphere) 2 (1,64) (3,65) (I.realization.basis .sphere 1 64 0) (I.realization.basis .sphere 3 65 0) ∧
    HasDifferential (sequence D .sphere) 2 (2,65) (4,66) (I.realization.basis .sphere 2 65 0) (I.realization.basis .sphere 4 66 0) ∧
    HasDifferential (sequence D .sphere) 2 (3,66) (5,67) (I.realization.basis .sphere 3 66 1) (I.realization.basis .sphere 5 67 2) ∧
    HasDifferential (sequence D .sphere) 3 (5,67) (8,69) (I.realization.basis .sphere 5 67 1) (I.realization.basis .sphere 8 69 0) ∧
    HasDifferential (sequence D .sphere) 2 (5,67) (7,68) (I.realization.basis .sphere 5 67 0) (I.realization.basis .sphere 7 68 0+I.realization.basis .sphere 7 68 1) ∧
    HasDifferential (sequence D .sphere) 2 (4,67) (6,68) (I.realization.basis .sphere 4 67 0) (I.realization.basis .sphere 6 68 1) ∧
    ReachesPage (sequence D .sphere) 1000 (6,68) (I.realization.basis .sphere 6 68 0) := by
  classical
  classical
  let E := sequence D .sphere
  have h365 : HasDifferential E 2 (1,64) (3,65) (I.realization.basis .sphere 1 64 0) (I.realization.basis .sphere 3 65 0) := prop78_choice_invariance_h365_0 I
  have h466 : HasDifferential E 2 (2,65) (4,66) (I.realization.basis .sphere 2 65 0) (I.realization.basis .sphere 4 66 0) := prop78_choice_invariance_h466_1 I
  have h567 : HasDifferential E 2 (3,66) (5,67) (I.realization.basis .sphere 3 66 1) (I.realization.basis .sphere 5 67 2) := prop78_choice_invariance_h567_2 I
  have h3 : HasDifferential E 3 (5,67) (8,69) (I.realization.basis .sphere 5 67 1) (I.realization.basis .sphere 8 69 0) := prop78_choice_invariance_h3_3 I
  have h2out : HasDifferential E 2 (5,67) (7,68) (I.realization.basis .sphere 5 67 0) (I.realization.basis .sphere 7 68 0+I.realization.basis .sphere 7 68 1) := by
    have hrow := I.results ⟨.sphere, .equation, 2, 5, 67, [0], 7, 68, [0, 1], "S0_AdamsE2_ss", 454⟩ (by
      exact List.mem_of_getElem? (i := 161) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (5,67) (7,68) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 5 67 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 7 68 [0, 1] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h668 : HasDifferential E 2 (4,67) (6,68) (I.realization.basis .sphere 4 67 0) (I.realization.basis .sphere 6 68 1) := prop78_choice_invariance_h668_4 I
  have hcycle : ReachesPage E 1000 (6,68) (I.realization.basis .sphere 6 68 0) := by
    have hrow := I.results ⟨.sphere, .reaches, 1000, 6, 68, [0], 6, 68, [], "S0_AdamsE2_ss", 470⟩ (by
      exact List.mem_of_getElem? (i := 167) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,hd⟩ := hrow
    change ReachesPage E 1000 (6,68) x at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 68 [0] = true := rfl
    simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hd
    exact hd
  exact ⟨h365,h466,h567,h3,h2out,h668,hcycle⟩


private theorem prop78_choice_invariance_choice_theta_choice_late_page (I : KIP126.Computation.Route.Inputs D L G)
    (e5 : (sequence D .sphere).Page 2 (5,67) ≃ₗ[ℤ] (Fin 3 →₀ F2))
    (he5 : ∀i:Fin 3, e5.symm (Finsupp.single i 1)=I.realization.basis .sphere 5 67 i.val)
    (e6 : (sequence D .sphere).Page 2 (6,68) ≃ₗ[ℤ] (Fin 2 →₀ F2))
    (he6 : ∀i:Fin 2, e6.symm (Finsupp.single i 1)=I.realization.basis .sphere 6 68 i.val)
    (e7 : (sequence D .sphere).Page 2 (7,68) ≃ₗ[ℤ] (Fin 2 →₀ F2))
    (he7 : ∀i:Fin 2, e7.symm (Finsupp.single i 1)=I.realization.basis .sphere 7 68 i.val)
    (e8 : (sequence D .sphere).Page 2 (8,69) ≃ₗ[ℤ] (Fin 1 →₀ F2))
    (he8 : ∀i:Fin 1, e8.symm (Finsupp.single i 1)=I.realization.basis .sphere 8 69 i.val)
    (h3 : HasDifferential (sequence D .sphere) 3 (5,67) (8,69) (I.realization.basis .sphere 5 67 1) (I.realization.basis .sphere 8 69 0))
    (h2out : HasDifferential (sequence D .sphere) 2 (5,67) (7,68) (I.realization.basis .sphere 5 67 0) (I.realization.basis .sphere 7 68 0+I.realization.basis .sphere 7 68 1))
    (hz567 : RepresentsOnPage (sequence D .sphere) 3 (5,67) (I.realization.basis .sphere 5 67 2) 0)
    (hd60 : (sequence D .sphere).d 2 (6,68) (I.realization.basis .sphere 6 68 0)=0)
    (hd61 : (sequence D .sphere).d 2 (6,68) (I.realization.basis .sphere 6 68 1)=0) :
    Subsingleton ((sequence D .sphere).Page 4 (5,67)) := by
  classical
  exact prop78_choice_invariance_choice_theta_choice_late_page_generic (sequence D .sphere) (by change (2:ℤ)≤2; omega) rfl
    (fun i=>I.realization.basis .sphere 5 67 i.val)
    (fun i=>I.realization.basis .sphere 6 68 i.val)
    (fun i=>I.realization.basis .sphere 7 68 i.val)
    (fun i=>I.realization.basis .sphere 8 69 i.val)
    e5 he5 e6 he6 e7 he7 e8 he8 h3 h2out hz567 hd60 hd61


private theorem prop78_choice_invariance_choice_theta_choice_finite_pages (I : KIP126.Computation.Route.Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 3 (3,65)) ∧
    Subsingleton ((sequence D .sphere).Page 3 (4,66)) ∧
    Subsingleton ((sequence D .sphere).Page 4 (5,67)) := by
  classical
  classical
  let E := sequence D .sphere
  obtain ⟨h365,h466,h567,h3,h2out,h668,hcycle⟩ := prop78_choice_invariance_choice_theta_choice_raw_relations I
  obtain ⟨e3,he3⟩ := I.basis ⟨.sphere, 3, 65, ["0,1,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 102) (by rfl))
  change E.Page 2 (3,65) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e3
  change ∀i:Fin 1, e3.symm (Finsupp.single i 1)=I.realization.basis .sphere 3 65 i.val at he3
  obtain ⟨e4,he4⟩ := I.basis ⟨.sphere, 4, 66, ["0,2,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 113) (by rfl))
  change E.Page 2 (4,66) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e4
  change ∀i:Fin 1, e4.symm (Finsupp.single i 1)=I.realization.basis .sphere 4 66 i.val at he4
  obtain ⟨e5,he5⟩ := I.basis ⟨.sphere, 5, 67, ["76,1", "1,1,70,1", "0,3,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 121) (by rfl))
  change E.Page 2 (5,67) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e5
  change ∀i:Fin 3, e5.symm (Finsupp.single i 1)=I.realization.basis .sphere 5 67 i.val at he5
  obtain ⟨e6,he6⟩ := I.basis ⟨.sphere, 6, 68, ["18,1,24,1", "0,4,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 131) (by rfl))
  change E.Page 2 (6,68) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e6
  change ∀i:Fin 2, e6.symm (Finsupp.single i 1)=I.realization.basis .sphere 6 68 i.val at he6
  obtain ⟨e7,he7⟩ := I.basis ⟨.sphere, 7, 68, ["0,1,75,1", "0,1,74,1"]⟩ (by
    exact List.mem_of_getElem? (i := 141) (by rfl))
  change E.Page 2 (7,68) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e7
  change ∀i:Fin 2, e7.symm (Finsupp.single i 1)=I.realization.basis .sphere 7 68 i.val at he7
  obtain ⟨e8,he8⟩ := I.basis ⟨.sphere, 8, 69, ["0,2,74,1"]⟩ (by
    exact List.mem_of_getElem? (i := 154) (by rfl))
  change E.Page 2 (8,69) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e8
  change ∀i:Fin 1, e8.symm (Finsupp.single i 1)=I.realization.basis .sphere 8 69 i.val at he8
  have he60 : e6.symm (Finsupp.single 0 1)=I.realization.basis .sphere 6 68 0 := he6 0
  have he61 : e6.symm (Finsupp.single 1 1)=I.realization.basis .sphere 6 68 1 := he6 1
  have he70 : e7.symm (Finsupp.single 0 1)=I.realization.basis .sphere 7 68 0 := he7 0
  have he71 : e7.symm (Finsupp.single 1 1)=I.realization.basis .sphere 7 68 1 := he7 1
  have he80 : e8.symm (Finsupp.single 0 1)=I.realization.basis .sphere 8 69 0 := he8 0
  have dz (r:ℤ) (hr:2<r) (p:ℤ×ℤ) (x:E.Page 2 p)
      (hx:ReachesPage E r p x) : E.d 2 p x=0 := by
    obtain ⟨x2,hx2⟩ := reaches_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) hx
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) hr hx2 hx
    simpa only [hx2.eq_on_page_two] using hh
  have hz365 := prop78_choice_invariance_choice_differential_target_later_zero (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)<3) h365
  have hz466 := prop78_choice_invariance_choice_differential_target_later_zero (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)<3) h466
  have hz567 := prop78_choice_invariance_choice_differential_target_later_zero (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)<3) h567
  have hz668 := prop78_choice_invariance_choice_differential_target_later_zero (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)<3) h668
  refine ⟨choice_single_basis_zero_page (by decide : (2:ℤ)≤3) e3 _ (he3 0) hz365,
    choice_single_basis_zero_page (by decide : (2:ℤ)≤3) e4 _ (he4 0) hz466,?_⟩
  have hd60 := dz 1000 (by decide) (6,68) _ hcycle
  have hd61 := dz 3 (by decide) (6,68) _ ⟨0,hz668⟩
  exact prop78_choice_invariance_choice_theta_choice_late_page I e5 he5 e6 he6 e7 he7 e8 he8 h3 h2out hz567 hd60 hd61


private theorem prop78_choice_invariance_choice_theta_square_difference (D : Model H M Syn)
    (θ θ' : BiHom 62 64 (S_0_0 : Syn)) (h2 : θ'+θ'=0) :
    sphereProduct θ θ-sphereProduct θ' θ'=sphereProduct (θ-θ') (θ-θ') := by
  classical
  let d := θ-θ'
  have ht : θ=θ'+d := by dsimp only [d]; abel
  have hc : sphereProduct d θ'=sphereProduct θ' d := by
    have h := D.sphereProductCommutative 62 64 62 64 d θ'
    norm_num [homotopyRegrade] at h
    exact h
  have hz : sphereProduct θ' d+sphereProduct d θ'=0 := by
    rw [hc]
    dsimp only [sphereProduct]
    rw [←Preadditive.comp_add,←Preadditive.add_comp,←Functor.map_add,h2,Functor.map_zero,
      zero_comp,comp_zero]
  have hs : sphereProduct (θ'+d) (θ'+d)=sphereProduct θ' θ'+sphereProduct d d := by
    have he : sphereProduct (θ'+d) (θ'+d)=
        sphereProduct θ' θ'+sphereProduct θ' d+(sphereProduct d θ'+sphereProduct d d) := by
      simp only [sphereProduct,Functor.map_add,Preadditive.add_comp,Preadditive.comp_add]
      abel
    rw [he]
    calc
      _ = sphereProduct θ' θ'+(sphereProduct θ' d+sphereProduct d θ')+sphereProduct d d := by abel
      _ = _ := by rw [hz,add_zero]
  change sphereProduct θ θ-sphereProduct θ' θ'=sphereProduct d d
  rw [ht,hs,add_sub_cancel_left]


private theorem prop78_choice_invariance_choice_detects_of_difference_in_next_filtration
    {H' : Syn} {unit : S_0_0 ⟶ H'} {F : SyntheticAdamsFamily Syn} {X : Syn}
    (c : TowerConvergence unit F X) (i : Tridegree)
    {x : (F.obj X).E₂ i} {a b : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a) (hb : FiltrationAtLeast unit (i.1+1) (b-a)) :
    Detects c i x b := by
  classical
  obtain ⟨e,he,a',ha',hga⟩ := ha
  let P := towerFiltration unit X
  let p := (i.2.1-i.1,i.2.2)
  have hmem : b-a∈(ModuleCat.subobjectModule (syntheticHomotopy X p)) (P.F (i.1+1) p) := by
    simpa only [P,p,FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply] using hb
  obtain ⟨z,hz⟩ := hmem
  let j := Subobject.ofLE (P.F (i.1+1) p) (P.F i.1 p) (P.mono i.1 p)
  refine ⟨e,he,a'+j z,?_,?_⟩
  · rw [map_add]
    have hj : (P.F i.1 p).arrow (j z)=(P.F (i.1+1) p).arrow z :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow (P.mono i.1 p)) z
    rw [hj,ha',hz]
    abel
  · rw [map_add]
    have hj : P.toAssociatedGraded i.1 p (j z)=0 :=
      ConcreteCategory.congr_hom (cokernel.condition j) z
    rw [hj,add_zero]
    exact hga


private theorem prop78_choice_invariance_choice_realization_additive {D : Model H M Syn} : D.recovery.realization.Additive := by
  classical
  letI := D.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts D.recovery.realization
  exact Functor.additive_of_preservesBinaryBiproducts _


private theorem prop78_choice_invariance_choice_realization_injective_of_lambda_powers
    (kernel : KIP126.Literature.Route.RealizationKernel D) (X : SyntheticObject) (m wt : ℤ)
    (h : LambdaPowersInjectiveAt m wt (X.obj D.nu D.auxiliary)) :
    Function.Injective (fun a : BiHom m wt (X.obj D.nu D.auxiliary) =>
      D.recovery.realization.map a) := by
  classical
  letI := prop78_choice_invariance_choice_realization_additive (D := D)
  intro a b hab
  apply sub_eq_zero.mp
  obtain ⟨k, hk⟩ := (kernel X m wt (a-b)).mp (by simp only [Functor.map_sub, hab, sub_self])
  apply h k
  simpa only [lambdaMultiply, Category.comp_id, Category.assoc, Limits.comp_zero] using hk


private theorem prop78_choice_invariance_choice_theta_degree_order_two (BHS : SyntheticInputs D)
    (RL : RealizationInput D) {η : BiHom 1 2 (S_0_0 : Syn)}
    (CL : ClassicalInputs D η) (theta : BiHom 62 64 (S_0_0 : Syn)) :
    theta+theta=0 := by
  classical
  have hnu : LambdaPowersInjectiveAt 62 64 (D.nu.functor.obj SphereSpectrum) := by
    apply nu_lambda_powers_injective_of_source_halfplane BHS .sphere 62 64
    intro q hq
    simpa only [ClassicalObject.obj,KIP126.Computation.Route.sequence,KIP126.Computation.Route.object,add_assoc,show (62:ℤ)+1=63 by norm_num] using
      no_outgoing_stem63_nonpositive (D:=D) q (by omega)
  have hsphere : LambdaPowersInjectiveAt 62 64 (S_0_0 : Syn) := by
    intro n a b hab
    apply (cancel_mono D.nu.unitIso.inv).mp
    apply hnu n
    simpa only [lambdaMultiply,Category.assoc] using
      congrArg (fun z=>z ≫ D.nu.unitIso.inv) hab
  have hinj := prop78_choice_invariance_choice_realization_injective_of_lambda_powers BHS.realization_kernel
    .sphere 62 64 hsphere
  letI := D.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts D.recovery.realization
  letI : D.recovery.realization.Additive := Functor.additive_of_preservesBinaryBiproducts _
  apply hinj
  simp only [Functor.map_add,Functor.map_zero]
  let α : HomotopyGroup (C:=C) 62 SphereSpectrum :=
    (RL.coordinates.sphere 62 64).hom ≫ D.recovery.realization.map theta ≫
      D.recovery.realization.map D.nu.unitIso.inv ≫ D.recovery.nuRealizationIso.hom.app SphereSpectrum
  have h := CL.stem62_exponent_two α
  apply (cancel_epi (RL.coordinates.sphere 62 64).hom).mp
  apply (cancel_mono (D.recovery.realization.map D.nu.unitIso.inv)).mp
  apply (cancel_mono ((D.recovery.nuRealizationIso.app SphereSpectrum).hom)).mp
  erw [Preadditive.comp_add,Preadditive.add_comp,Preadditive.add_comp,
    Limits.comp_zero,Limits.zero_comp,Limits.zero_comp]
  repeat erw [Category.assoc]
  exact h


private theorem prop78_choice_invariance_choice_theta_choice_filtration_gap_of_pages
    (BHS : SyntheticInputs D)
    (hpages : Subsingleton ((sequence D .sphere).Page 3 (3,65)) ∧
      Subsingleton ((sequence D .sphere).Page 3 (4,66)) ∧
      Subsingleton ((sequence D .sphere).Page 4 (5,67)))
    (θ θ' : BiHom 62 64 (S_0_0 : Syn))
    (hθ : ThetaChoice M D.toModelData θ) (hθ' : ThetaChoice M D.toModelData θ') :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 6 (θ-θ') := by
  classical
  have hlambda0 (a : BiHom 62 64 (S_0_0 : Syn)) : lambdaMultiply 0 a=a := by
    have hc := D.shiftCoherence.right_unit (62,64) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 62 64 : Syn) := by
      change (biShiftAddIso (62,64) (0,0) (62,64) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [Nat.cast_zero,neg_zero,sub_zero,eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app (S_0_0 : Syn) ≫ a=a
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have ht := D.comparisonCompatible.homotopy_lambda 2 64 0 θ
  have ht' := D.comparisonCompatible.homotopy_lambda 2 64 0 θ'
  rw [hlambda0,hθ] at ht
  rw [hlambda0,hθ'] at ht'
  have h3 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 3 (θ-θ') :=
    detects_sub_filtration D.sphereConvergence (2,64,64) ht ht'
  have permanentQuotient_zero_of_page_3_zero (s t b : ℤ) (hb : 2 ≤ b)
      (hpage : Subsingleton ((sequence D .sphere).Page 3 (s, t))) :
      Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
    set_option backward.isDefEq.respectTransparency false in
      let E := (sequence D .sphere).ssData (s, t)
      haveI : Subsingleton (E.page 1) := hpage
      have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
          PageRepresentatives.boundaries H SphereSpectrum 2 (s, t) := by
        rintro x ⟨z, hz⟩
        let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 1) (E.Z_anti le_top)) z
        have hzero : E.pageπ 1 zf = 0 := Subsingleton.elim _ _
        obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
          (Subobject.ofLE (E.B 1) (E.Z 1) (E.B_le_Z 1)) zf).mp hzero
        refine ⟨y, ?_⟩
        change PageRepresentatives.boundaryMap H SphereSpectrum 1 (s, t) y = x
        have hfactor : Subobject.ofLE (E.B 1) (E.Z 1) (E.B_le_Z 1) ≫
            PageRepresentatives.cycleMap H SphereSpectrum 1 (s, t) =
            PageRepresentatives.boundaryMap H SphereSpectrum 1 (s, t) := by
          dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.Route.sequence, object]
          rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
        rw [← hfactor, CategoryTheory.comp_apply]
        apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 1 (s, t)) hy).trans
        exact (congrArg (fun f => f z)
          (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 1 ⊤ le_top)).trans hz
      have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
        rintro ⟨x⟩
        change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
        exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
      exact ⟨fun x y => (hall x).trans (hall y).symm⟩

  have permanentQuotient_zero_of_page_4_zero (s t b : ℤ) (hb : 3 ≤ b)
      (hpage : Subsingleton ((sequence D .sphere).Page 4 (s, t))) :
      Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
    set_option backward.isDefEq.respectTransparency false in
      let E := (sequence D .sphere).ssData (s, t)
      haveI : Subsingleton (E.page 2) := hpage
      have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
          PageRepresentatives.boundaries H SphereSpectrum 3 (s, t) := by
        rintro x ⟨z, hz⟩
        let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 2) (E.Z_anti le_top)) z
        have hzero : E.pageπ 2 zf = 0 := Subsingleton.elim _ _
        obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
          (Subobject.ofLE (E.B 2) (E.Z 2) (E.B_le_Z 2)) zf).mp hzero
        refine ⟨y, ?_⟩
        change PageRepresentatives.boundaryMap H SphereSpectrum 2 (s, t) y = x
        have hfactor : Subobject.ofLE (E.B 2) (E.Z 2) (E.B_le_Z 2) ≫
            PageRepresentatives.cycleMap H SphereSpectrum 2 (s, t) =
            PageRepresentatives.boundaryMap H SphereSpectrum 2 (s, t) := by
          dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.Route.sequence, object]
          rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
        rw [← hfactor, CategoryTheory.comp_apply]
        apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 2 (s, t)) hy).trans
        exact (congrArg (fun f => f z)
          (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 2 ⊤ le_top)).trans hz
      have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
        rintro ⟨x⟩
        change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
        exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
      exact ⟨fun x y => (hall x).trans (hall y).symm⟩

  apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
    3 6 62 64 (by omega) ?_ (θ-θ')).mp h3
  intro j hj hj'
  haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
      (1+(62+j)-64) (j,62+j)) := by
    interval_cases j
    · exact permanentQuotient_zero_of_page_3_zero 3 65 2 (by omega) hpages.1
    · exact permanentQuotient_zero_of_page_3_zero 4 66 3 (by omega) hpages.2.1
    · exact permanentQuotient_zero_of_page_4_zero 5 67 4 (by omega) hpages.2.2
  let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,62+j) 64 (by omega)
  haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,62+j,64)).eInfty) := e.injective.subsingleton
  let hnu := ModuleCat.isZero_of_subsingleton
    (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,62+j,64)).eInfty)
  let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,62+j,64)
  let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,62+j,64)
  have hfg : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])


private theorem prop78_choice_invariance_choice_theta_choice_c4_invariance_of_pages
    (BHS : SyntheticInputs D) (RL : RealizationInput D)
    {η : BiHom 1 2 (S_0_0 : Syn)} (CL : ClassicalInputs D η)
    (AF : SphereActionFiltrationCompatible D)
    (hpages : Subsingleton ((sequence D .sphere).Page 3 (3,65)) ∧
      Subsingleton ((sequence D .sphere).Page 3 (4,66)) ∧
      Subsingleton ((sequence D .sphere).Page 4 (5,67)))
    (θ θ' : BiHom 62 64 (S_0_0 : Syn))
    (hθ : ThetaChoice M D.toModelData θ) (hθ' : ThetaChoice M D.toModelData θ')
    (hc : C4At M D.toModelData L θ') : C4At M D.toModelData L θ := by
  classical
  have hd := prop78_choice_invariance_choice_theta_choice_filtration_gap_of_pages BHS hpages θ θ' hθ hθ'
  have hsq : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12
      (sphereProduct θ θ-sphereProduct θ' θ') := by
    rw [prop78_choice_invariance_choice_theta_square_difference D θ θ' (prop78_choice_invariance_choice_theta_degree_order_two BHS RL CL θ')]
    exact AF .sphere 62 64 62 64 6 6 (θ-θ') (θ-θ') hd hd
  refine ⟨?_,hc.2⟩
  apply prop78_choice_invariance_choice_detects_of_difference_in_next_filtration D.sphereConvergence (10,134,128) hc.1
  exact towerFiltrationSubmodule_antitone (nuCoefficientUnit H.unit D.nu)
    (S_0_0 : Syn) (124,128) (by decide : (11:ℤ)≤12) hsq


private theorem prop78_choice_invariance_choice_theta_choice_c4_invariance (I : KIP126.Computation.Route.Inputs D L G)
    (BHS : SyntheticInputs D) (RL : RealizationInput D)
    {η : BiHom 1 2 (S_0_0 : Syn)} (CL : ClassicalInputs D η)
    (AF : SphereActionFiltrationCompatible D)
    (θ θ' : BiHom 62 64 (S_0_0 : Syn))
    (hθ : ThetaChoice M D.toModelData θ) (hθ' : ThetaChoice M D.toModelData θ')
    (hc : C4At M D.toModelData L θ') : C4At M D.toModelData L θ := by
  classical
  exact prop78_choice_invariance_choice_theta_choice_c4_invariance_of_pages BHS RL CL AF (prop78_choice_invariance_choice_theta_choice_finite_pages I) θ θ' hθ hθ' hc


private theorem prop78_choice_invariance (I : KIP126.Computation.Route.Inputs D L G)
    (BHS : SyntheticInputs D) (RL : RealizationInput D) (CL : ClassicalInputs D η)
    (AF : SphereActionFiltrationCompatible D)
    (theta theta' : BiHom 62 64 (S_0_0 : Syn))
    (h : ThetaChoice M D.toModelData theta) (h' : ThetaChoice M D.toModelData theta')
    (hc : C4At M D.toModelData L theta') : C4At M D.toModelData L theta := by
  classical
  exact prop78_choice_invariance_choice_theta_choice_c4_invariance I BHS RL CL AF theta theta' h h' hc
end
end KIP126.Main.Solution.Route

namespace KIP126.Main.Solution.Route
open KIP126.Core.SpectralSequence.FinitePageCalculus
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route KIP126.Algebra
open KIP126.LinE2 KIP126.Computation.Near126 KIP126.Computation.Route
noncomputable section
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
  {L : Labels H} {G : TmfLabels H} {η : BiHom 1 2 (S_0_0:Syn)}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem prop78_detection_data_bridge_family_map_data {D : Model H M Syn} {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
  classical
  let F := (D.family.functor.map f).toSSDataMorphism
  let PX := (D.family.functor.obj X).ssData i
  let PY := (D.family.functor.obj Y).ssData i
  let nX : WithTop ℕ := ↑(r-(D.family.functor.obj X).r₀).toNat
  let nY : WithTop ℕ := ↑(r-(D.family.functor.obj Y).r₀).toNat
  change (@eqToHom (ModuleCat ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
    (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
    @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
  have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D.family.firstPage X]
  have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D.family.firstPage Y]
  have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
      (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
      (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
      eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
    subst n
    subst m
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
  exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _


private theorem prop78_detection_data_bridge_family_page_comp {D : Model H M Syn} {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
  classical
  rw [prop78_detection_data_bridge_family_map_data,prop78_detection_data_bridge_family_map_data,prop78_detection_data_bridge_family_map_data,Functor.map_comp]
  exact (SSDataMorphism.pageMap_comp _ _ _ _).symm


private theorem prop78_detection_data_bridge_family_infinity_representative_map {D : Model H M Syn}
    {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
    (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
    (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
    HasInfinityRepresentative (D.family.obj Y) 2 i
      (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
  classical
  obtain ⟨hr,z,hz,he⟩ := hy
  change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
    (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
  let F := (D.family.functor.map f).toSSDataMorphism
  refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
  · rw [prop78_detection_data_bridge_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])


private theorem prop78_detection_data_bridge_sphere_quotient_label_to_nu {D : Model H M Syn} (q k : ℕ) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) :
    familyPageMap D.family (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)
      (D.quotientLabel q s t k x) = finiteTargetLabel D .sphere q s t k x := by
  classical
  let nx : (D.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (D.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
    simpa only [ClassicalObject.obj,add_zero] using D.nuE2 .sphere 0 s t k x
  let f := XModLambdaN.map D.nu.unitIso.inv q
  have hbase : familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)=
      targetNuLabel D .sphere s t k x := by
    have hc : familyPageMap D.family
        (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k) nx =
        D.sphereE2 s t k x := by
      convert D.comparisonCompatible.sphere_nu s t k x using 1 <;> simp [nx,ClassicalObject.obj] <;> rfl
    calc
      _ = familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k)
          (familyPageMap D.family (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k)
            nx) := congrArg (fun y => familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) y) hc.symm
      _ = familyPageMap D.family ((SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) ≫ D.nu.unitIso.inv)
          2 (s,t,t-k) nx :=
        ConcreteCategory.congr_hom (prop78_detection_data_bridge_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have hlabel : familyPageMap D.family f 2 (s,t,t-k) (D.quotientLabel q s t k x)=
      finiteTargetLabel D .sphere q s t k x := by
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D.nu.unitIso.inv q)
          2 (s,t,t-k) (D.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (prop78_detection_data_bridge_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)) (D.sphereE2 s t k x)
      _ = familyPageMap D.family (D.nu.unitIso.inv ≫ XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q)
          2 (s,t,t-k) (D.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
      _ = familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)) :=
        (ConcreteCategory.congr_hom (prop78_detection_data_bridge_family_page_comp (D:=D) D.nu.unitIso.inv (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D.sphereE2 s t k x)).symm
      _ = finiteTargetLabel D .sphere q s t k x := congrArg
        (fun y => familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
  exact hlabel


private theorem prop78_detection_data_bridge_detected_map {D : Model H M Syn}
    (X Y : SyntheticObject) (f : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary)
    (i : Tridegree) (x : (D.family.obj (X.obj D.nu D.auxiliary)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D.nu D.auxiliary))
    (ha : Detects (D.convergence X) i x a) :
    Detects (D.convergence Y) i (familyPageMap D.family f 2 i x) (a≫f) := by
  classical
  obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural X Y f
  obtain ⟨e,he,a',ha',hgr⟩ := ha
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (X.obj D.nu D.auxiliary)
  let G := towerFiltration (nuCoefficientUnit H.unit D.nu) (Y.obj D.nu D.auxiliary)
  let m := (i.2.1-i.1,i.2.2)
  let k := (c.filtration_compat i.1 m).choose
  have hk : k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫syntheticHomotopyMap f m := by
    have hh := (c.filtration_compat i.1 m).choose_spec
    change k≫(G.F i.1 m).arrow=(F.F i.1 m).arrow≫c.aMap m at hh
    rw [hca] at hh
    exact hh
  have hc : c.eMap i ≫ ((D.convergence Y).identification i).hom =
      ((D.convergence X).identification i).hom ≫ Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m := by
    have hh := c.iso_compat i
    simpa only [KIP126.Core.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] using hh
  have hq : F.toAssociatedGraded i.1 m ≫
      Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m =
      k≫G.toAssociatedGraded i.1 m := by
    exact cokernel.π_desc _ _ _
  refine ⟨(D.family.functor.map f).eInftyMap i e,prop78_detection_data_bridge_family_infinity_representative_map f i x e he,k a',?_,?_⟩
  · have hh := ConcreteCategory.congr_hom hk a'
    change (G.F i.1 m).arrow (k a')=((F.F i.1 m).arrow a')≫f at hh
    change (F.F i.1 m).arrow a'=a at ha'
    rw [ha'] at hh
    exact hh
  · have hh := ConcreteCategory.congr_hom hc e
    rw [hce] at hh
    change ((D.convergence Y).identification i).hom ((D.family.functor.map f).eInftyMap i e)=_
    calc
      _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
          (((D.convergence X).identification i).hom e) := hh
      _ = (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 m)
          (F.toAssociatedGraded i.1 m a') := by rw [hgr]
      _ = G.toAssociatedGraded i.1 m (k a') := ConcreteCategory.congr_hom hq a'


private theorem prop78_detection_data_bridge_detects_infinity_equal {D : Model H M Syn}
    (X : SyntheticObject) (i : Tridegree)
    (a : BiHom (i.2.1-i.1) i.2.2 (X.obj D.nu D.auxiliary))
    (x y : (D.family.obj (X.obj D.nu D.auxiliary)).E₂ i)
    (ha : Detects (D.convergence X) i x a)
    (hb : Detects (D.convergence X) i y a) :
    ∃ e, HasInfinityRepresentative (D.family.obj (X.obj D.nu D.auxiliary)) 2 i x e ∧
      HasInfinityRepresentative (D.family.obj (X.obj D.nu D.auxiliary)) 2 i y e := by
  classical
  obtain ⟨e,he,a',ha',hga⟩ := ha
  obtain ⟨f,hf,b',hb',hgb⟩ := hb
  have hab : a'=b' := (ModuleCat.mono_iff_injective _).mp inferInstance (ha'.trans hb'.symm)
  have hef : e=f := (ModuleCat.mono_iff_injective _).mp inferInstance (by rw [hga,hgb,hab])
  exact ⟨e,he,hef.symm ▸ hf⟩


private theorem prop78_detection_data_bridge_sphere_zero_weight_label_10_134 {D : Model H M Syn}
    (BHS : EInftyInput D) (x : E2 H SphereSpectrum 10 134)
    (a : BiHom (134-10) (134-0) (S_0_0 : Syn))
    (ha : Detects D.sphereConvergence (10,134,134-0) (D.sphereE2 10 134 0 x) a) :
    D.sphereFirstQuotient 10 134 (quotientClass 1 a)=x := by
  classical
  let y := D.sphereFirstQuotient 10 134 (quotientClass 1 a)
  have hd := prop78_detection_data_bridge_detected_map (D:=D) .sphere (.quotient 1 .sphere)
    (XModLambdaN.incl (S_0_0 : Syn) 1) (10,134,134-0) _ a ha
  have hd' := D.comparisonCompatible.first_quotient 10 134 y
  have hy : (D.sphereFirstQuotient 10 134).symm y=quotientClass 1 a := by
    exact (D.sphereFirstQuotient 10 134).symm_apply_apply _
  rw [hy] at hd'
  obtain ⟨e,he,hf⟩ := prop78_detection_data_bridge_detects_infinity_equal (.quotient 1 .sphere) (10,134,134-0)
    (quotientClass 1 a) _ _ hd hd'
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (10,134,134-0)
    (D.quotientLabel 1 10 134 0 x) e at he
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (10,134,134-0)
    (D.quotientLabel 1 10 134 0 y) e at hf
  let g := XModLambdaN.map D.nu.unitIso.inv 1
  have he' := prop78_detection_data_bridge_family_infinity_representative_map g (10,134,134-0) _ _ he
  have hf' := prop78_detection_data_bridge_family_infinity_representative_map g (10,134,134-0) _ _ hf
  have hlx := prop78_detection_data_bridge_sphere_quotient_label_to_nu (D:=D) 1 0 10 134 x
  have hly := prop78_detection_data_bridge_sphere_quotient_label_to_nu (D:=D) 1 0 10 134 y
  change familyPageMap D.family g 2 (10,134,134-0) (D.quotientLabel 1 10 134 0 x)=_ at hlx
  change familyPageMap D.family g 2 (10,134,134-0) (D.quotientLabel 1 10 134 0 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  let xx : PageRepresentatives.cycles H SphereSpectrum (1-134+(134-0)) (10,134) :=
    ⟨x,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
  let yy : PageRepresentatives.cycles H SphereSpectrum (1-134+(134-0)) (10,134) :=
    ⟨y,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
  have hxq := (BHS.labels.1 .sphere 1 (by decide) (10,134) 0 (by decide) xx _).mp he'
  have hyq := (BHS.labels.1 .sphere 1 (by decide) (10,134) 0 (by decide) yy _).mp hf'
  have heq := hxq.symm.trans hyq
  change NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (10,134)) xx =
    NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (10,134)) yy at heq
  have hz : NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (10,134)) (xx-yy)=0 := by rw [map_sub,heq,sub_self]
  have hm := (NestedQuotient.projection_eq_zero (xx-yy)).mp hz
  change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (10,134) at hm
  have ht : 1+134-(134-0)=1 := by omega
  change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (10,134) at hm
  rw [PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
  exact (sub_eq_zero.mp hm).symm


private theorem prop78_detection_data_bridge_shift_assoc_inv (coh : BiShiftCoherence Syn)
    (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (habc : ab+c=total) (habc' : a+bc=total) (A : Syn) :
    (biShiftAddIso ab c total habc).inv.app A ≫
      (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
    (biShiftAddIso a bc total habc').inv.app A ≫
      (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
  classical
  have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
      (biShiftAddIso ab c total habc).app A) =
    ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
      (biShiftAddIso a bc total habc').app A) :=
    Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
  have hi := congrArg Iso.inv he
  exact hi


private def prop78_detection_data_bridge_push3 {m w : ℤ} {X Y : Syn}
    (f : (SyntheticCategory.biShift (0,-3)).obj X ⟶ Y) (a : BiHom m w X) :
    BiHom m (w-3) Y :=
  eqToHom (by congr 1; simp [sub_eq_add_neg]) ≫
    (SyntheticCategory.biShift_comp (m,w) (0,-3)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (0,-3)).map a ≫ f


private theorem prop78_detection_data_bridge_eta_push3 (D : Model H M Syn) {X Y : Syn}
    (f : (SyntheticCategory.biShift (0,-3)).obj X ⟶ Y)
    (ν : BiHom 1 2 (S_0_0 : Syn)) (x : BiHom 124 134 X) :
    sphereAction ν (prop78_detection_data_bridge_push3 f x) = prop78_detection_data_bridge_push3 f (sphereAction ν x) := by
  classical
  have ha := prop78_detection_data_bridge_shift_assoc_inv D.shiftCoherence (1,2) (124,134) (0,-3)
    (125,136) (124,131) (125,133) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv,
    eqToHom_app, eqToHom_refl, Category.id_comp] at ha
  simp only [prop78_detection_data_bridge_push3, eqToHom_refl, Category.id_comp]
  change
    (SyntheticCategory.biShift_comp (1,2) (124,131)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (124,131)).map ν ≫
      ((SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift (0,-3)).map x ≫ f) =
    (SyntheticCategory.biShift_comp (125,136) (0,-3)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (0,-3)).map
        ((SyntheticCategory.biShift_comp (1,2) (124,134)).inv.app (S_0_0 : Syn) ≫
          (SyntheticCategory.biShift (124,134)).map ν ≫ x) ≫ f
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% ((SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.naturality ν)]
  erw [← reassoc_of% ha]


private theorem prop78_detection_data_bridge_eta_lambda3_right (D : Model H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn)) (u : BiHom 124 134 (S_0_0 : Syn)) :
    sphereProduct η (lambdaMultiply 3 u)=lambdaMultiply 3 (sphereProduct η u) := by
  classical
  have heq {m w : ℤ} (a : BiHom m w (S_0_0 : Syn)) :
      prop78_detection_data_bridge_push3 (lambdaPow 3 (S_0_0 : Syn)) a=lambdaMultiply 3 a := by
    simp only [prop78_detection_data_bridge_push3,lambdaMultiply,Category.assoc]
    erw [lambdaPow_naturality]
    rfl
  have h := prop78_detection_data_bridge_eta_push3 D (lambdaPow 3 (S_0_0 : Syn)) η u
  rw [heq,heq] at h
  exact h


private def prop78_detection_data_bridge_push6 {m w : ℤ} {X Y : Syn}
    (f : (SyntheticCategory.biShift (0,-6)).obj X ⟶ Y) (a : BiHom m w X) :
    BiHom m (w-6) Y :=
  eqToHom (by congr 1; simp [sub_eq_add_neg]) ≫
    (SyntheticCategory.biShift_comp (m,w) (0,-6)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (0,-6)).map a ≫ f


private theorem prop78_detection_data_bridge_eta_push6 (D : Model H M Syn) {X Y : Syn}
    (f : (SyntheticCategory.biShift (0,-6)).obj X ⟶ Y)
    (ν : BiHom 1 2 (S_0_0 : Syn)) (x : BiHom 124 134 X) :
    sphereAction ν (prop78_detection_data_bridge_push6 f x) = prop78_detection_data_bridge_push6 f (sphereAction ν x) := by
  classical
  have ha := prop78_detection_data_bridge_shift_assoc_inv D.shiftCoherence (1,2) (124,134) (0,-6)
    (125,136) (124,128) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv,
    eqToHom_app, eqToHom_refl, Category.id_comp] at ha
  simp only [prop78_detection_data_bridge_push6, eqToHom_refl, Category.id_comp]
  change
    (SyntheticCategory.biShift_comp (1,2) (124,128)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (124,128)).map ν ≫
      ((SyntheticCategory.biShift_comp (124,134) (0,-6)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift (0,-6)).map x ≫ f) =
    (SyntheticCategory.biShift_comp (125,136) (0,-6)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift (0,-6)).map
        ((SyntheticCategory.biShift_comp (1,2) (124,134)).inv.app (S_0_0 : Syn) ≫
          (SyntheticCategory.biShift (124,134)).map ν ≫ x) ≫ f
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% ((SyntheticCategory.biShift_comp (124,134) (0,-6)).inv.naturality ν)]
  erw [← reassoc_of% ha]


private theorem prop78_detection_data_bridge_eta_lambda6_right (D : Model H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn)) (u : BiHom 124 134 (S_0_0 : Syn)) :
    sphereProduct η (lambdaMultiply 6 u)=lambdaMultiply 6 (sphereProduct η u) := by
  classical
  have heq {m w : ℤ} (a : BiHom m w (S_0_0 : Syn)) :
      prop78_detection_data_bridge_push6 (lambdaPow 6 (S_0_0 : Syn)) a=lambdaMultiply 6 a := by
    simp only [prop78_detection_data_bridge_push6,lambdaMultiply,Category.assoc]
    erw [lambdaPow_naturality]
    rfl
  have h := prop78_detection_data_bridge_eta_push6 D (lambdaPow 6 (S_0_0 : Syn)) η u
  rw [heq,heq] at h
  exact h


private theorem prop78_detection_data_bridge_lambda_three_3_136 (D : Model H M Syn)
    (c : BiHom 125 136 (S_0_0 : Syn)) :
    lambdaMultiply 3 (lambdaMultiply 3 c)=lambdaMultiply 6 c := by
  classical
  have ha := prop78_detection_data_bridge_shift_assoc_inv D.shiftCoherence (125,136) (0,-3) (0,-3)
    (125,133) (0,-6) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso,Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,
    eqToHom_app,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Category.assoc,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (125,136) (0,-3)).inv.app (S_0_0 : Syn)))]
  erw [←reassoc_of% (lambdaPow_naturality 3 (lambdaPow 3 (Smn 125 136)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add D.shiftCoherence 3 3 6 (by decide) (Smn 125 136)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,eqToHom_app,eqToHom_refl,
    Category.id_comp,Category.assoc]
  rfl


private theorem prop78_detection_data_bridge_lambda_three_7_140 (D : Model H M Syn)
    (c : BiHom 125 140 (S_0_0 : Syn)) :
    lambdaMultiply 3 (lambdaMultiply 7 c)=lambdaMultiply 10 c := by
  classical
  have ha := prop78_detection_data_bridge_shift_assoc_inv D.shiftCoherence (125,140) (0,-7) (0,-3)
    (125,133) (0,-10) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso,Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,
    eqToHom_app,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Category.assoc,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (125,140) (0,-7)).inv.app (S_0_0 : Syn)))]
  erw [←reassoc_of% (lambdaPow_naturality 3 (lambdaPow 7 (Smn 125 140)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add D.shiftCoherence 7 3 10 (by decide) (Smn 125 140)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,eqToHom_app,eqToHom_refl,
    Category.id_comp,Category.assoc]
  rfl


private theorem prop78_detection_data_bridge_lambda_three_6_139 (D : Model H M Syn)
    (c : BiHom 125 139 (S_0_0 : Syn)) :
    lambdaMultiply 3 (lambdaMultiply 6 c)=lambdaMultiply 9 c := by
  classical
  have ha := prop78_detection_data_bridge_shift_assoc_inv D.shiftCoherence (125,139) (0,-6) (0,-3)
    (125,133) (0,-9) (125,130) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso,Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,
    eqToHom_app,eqToHom_refl,Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Category.assoc,Nat.cast_ofNat,Int.reduceSub]
  erw [←reassoc_of% (lambdaPow_naturality 3
    ((SyntheticCategory.biShift_comp (125,139) (0,-6)).inv.app (S_0_0 : Syn)))]
  erw [←reassoc_of% (lambdaPow_naturality 3 (lambdaPow 6 (Smn 125 139)))]
  erw [←Category.assoc,ha]
  erw [lambdaPow_add D.shiftCoherence 6 3 9 (by decide) (Smn 125 139)]
  simp only [lambdaShiftAddIso,biShiftAddIso,KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,eqToHom_app,eqToHom_refl,
    Category.id_comp,Category.assoc]
  rfl


private theorem prop78_detection_data_bridge_vanishes_mod_lambda_iff_multiple
    (n : ℕ) {X : Syn} (m w : ℤ) (z : BiHom m (w-(n:ℤ)) X) :
    VanishesModLambda n z ↔ ∃ b : BiHom m w X, lambdaMultiply n b=z := by
  classical
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-(n:ℤ))
  let e : F.obj (Smn m w : Syn) ≅ Smn m (w-(n:ℤ)) :=
    (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).app S_0_0 ≪≫
      eqToIso (by congr 1 <;> simp [sub_eq_add_neg])
  have he (b : BiHom m w X) : lambdaMultiply n b=e.inv≫F.map b≫lambdaPow n X := by
    have he' : lambdaMultiply n b=e.inv≫lambdaPow n (Smn m w)≫b := by
      unfold lambdaMultiply
      change eqToHom (by congr 1 <;> simp [sub_eq_add_neg]) ≫
        (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).inv.app S_0_0 ≫
        lambdaPow n (Smn m w) ≫ b =
        (eqToHom (by congr 1 <;> simp [sub_eq_add_neg]) ≫
          (SyntheticCategory.biShift_comp (m,w) (0,-(n:ℤ))).inv.app S_0_0) ≫
        lambdaPow n (Smn m w) ≫ b
      exact (Category.assoc _ _ _).symm
    rw [he',←lambdaPow_naturality n b]
  constructor
  · intro hz
    obtain ⟨a,ha⟩ := (vanishesModLambda_iff_factors n z).mp hz
    let b := (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-(n:ℤ))).preimage (e.hom≫a)
    have hb : F.map b=e.hom≫a :=
      (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-(n:ℤ))).map_preimage _
    refine ⟨b,?_⟩
    rw [he,hb]
    simp only [Category.assoc,e.inv_hom_id_assoc]
    exact ha
  · rintro ⟨b,rfl⟩
    apply (vanishesModLambda_iff_factors n (lambdaMultiply n b)).mpr
    exact ⟨e.inv≫F.map b,by rw [Category.assoc,←he]⟩


private theorem prop78_detection_data_bridge_map_filtration {D : Model H M Syn} {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
    (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s x) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (x ≫ f) := by
  classical
  obtain ⟨z,hz⟩ := hx
  refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat,?_⟩
  change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat) ≫
    adamsTowerMap (nuCoefficientUnit H.unit D.nu) Y 0 s.toNat _ = x ≫ f
  change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) X 0 s.toNat _ = x at hz
  rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hz]
  rfl


private theorem prop78_detection_data_bridge_lambda_9_iff_filtration_14 {D : Model H M Syn}
    (BHS : SyntheticInputs D) (a : BiHom 125 130 (S_0_0 : Syn)) :
    VanishesModLambda 9 a ↔ FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
  classical
  have h := BHS.filtration_lambda .sphere 125 130 14 (by omega) (a ≫ D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (a ≫ D.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 139 (D.nu.functor.obj SphereSpectrum), lambdaMultiply 9 b=a ≫ D.nu.unitIso.inv at h
  constructor
  · intro hz
    obtain ⟨b,hb⟩ := (prop78_detection_data_bridge_vanishes_mod_lambda_iff_multiple 9 125 139 a).mp hz
    have haν := h.mpr ⟨b ≫ D.nu.unitIso.inv,by
      simpa only [lambdaMultiply,Category.assoc] using
        (congrArg (fun z=>z ≫ D.nu.unitIso.inv) hb)⟩
    have hm := prop78_detection_data_bridge_map_filtration (D:=D) D.nu.unitIso.hom (a ≫ D.nu.unitIso.inv) haν
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hm
  · intro ha
    obtain ⟨b,hb⟩ := h.mp (prop78_detection_data_bridge_map_filtration (D:=D) D.nu.unitIso.inv a ha)
    apply (prop78_detection_data_bridge_vanishes_mod_lambda_iff_multiple 9 125 139 a).mpr
    refine ⟨b ≫ D.nu.unitIso.hom,?_⟩
    simpa only [lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun z=>z ≫ D.nu.unitIso.hom) hb


private theorem prop78_detection_data_bridge_lambda_10_iff_filtration_15 {D : Model H M Syn}
    (BHS : SyntheticInputs D) (a : BiHom 125 130 (S_0_0 : Syn)) :
    VanishesModLambda 10 a ↔ FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a := by
  classical
  have h := BHS.filtration_lambda .sphere 125 130 15 (by omega) (a ≫ D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (a ≫ D.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 140 (D.nu.functor.obj SphereSpectrum), lambdaMultiply 10 b=a ≫ D.nu.unitIso.inv at h
  constructor
  · intro hz
    obtain ⟨b,hb⟩ := (prop78_detection_data_bridge_vanishes_mod_lambda_iff_multiple 10 125 140 a).mp hz
    have haν := h.mpr ⟨b ≫ D.nu.unitIso.inv,by
      simpa only [lambdaMultiply,Category.assoc] using
        (congrArg (fun z=>z ≫ D.nu.unitIso.inv) hb)⟩
    have hm := prop78_detection_data_bridge_map_filtration (D:=D) D.nu.unitIso.hom (a ≫ D.nu.unitIso.inv) haν
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using hm
  · intro ha
    obtain ⟨b,hb⟩ := h.mp (prop78_detection_data_bridge_map_filtration (D:=D) D.nu.unitIso.inv a ha)
    apply (prop78_detection_data_bridge_vanishes_mod_lambda_iff_multiple 10 125 140 a).mpr
    refine ⟨b ≫ D.nu.unitIso.hom,?_⟩
    simpa only [lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun z=>z ≫ D.nu.unitIso.hom) hb


private theorem prop78_detection_data_bridge_theta_quotient_frame {D : Model H M Syn}
    (I : KIP126.Computation.Route.Inputs D L G) (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t), x'.val=x ∧
      ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData (s,t)
  have hB : P.B ⊤ = P.B (k:WithTop ℕ) := by
    have hin : ∀ r : ℤ, (k:ℤ)+2 ≤ r → E.d r ((s,t)-E.diffDeg r)=0 := by
      intro r hr
      change E.d r (s-r,t-(r-1))=0
      rw [show t-(r-1)=(s-r)+125 by omega]
      ext z
      exact no_outgoing_stem125_low I (s-r) (by omega) r (by omega) z
    have h := boundaries_top_eq_of_d_eq_zero E (k+2) (by change (2:ℤ)≤_; omega) (s,t) hin
    change P.B ⊤ = P.B (↑((k:ℤ)+2-2).toNat) at h
    simpa only [add_sub_cancel_right,Int.toNat_natCast] using h
  obtain ⟨z,hz,_,hall⟩ := hx
  change PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z=x at hz
  let x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := ⟨x,⟨z,hz⟩⟩
  refine ⟨x',rfl,?_⟩
  have zero_of_infinity_zero (z' : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ))
      (hzero : P.pageπ ⊤ z'=0) :
      PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z' ∈
        PageRepresentatives.boundaries H SphereSpectrum (1+(k:ℤ)) (s,t) := by
    obtain ⟨b,hb⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (P.B ⊤) (P.Z ⊤) (P.B_le_Z ⊤)) z').mp hzero
    have hi : P.B ⊤ ≤ P.B (k:WithTop ℕ) := hB.le
    change ∃ q, PageRepresentatives.boundaryMap H SphereSpectrum
      (↑((1+(k:ℤ))-1).toNat) (s,t) q = _
    rw [show 1+(k:ℤ)-1=(k:ℤ) by omega,Int.toNat_natCast]
    refine ⟨(Subobject.ofLE _ _ hi) b,?_⟩
    rw [←hb]
    change (Subobject.ofLE _ _ hi ≫ PageRepresentatives.boundaryMap H SphereSpectrum (k:WithTop ℕ) (s,t)) b =
      (Subobject.ofLE _ _ (P.B_le_Z ⊤) ≫ PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t)) b
    congr 1
    dsimp only [PageRepresentatives.boundaryMap,PageRepresentatives.cycleMap,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE,←Category.assoc,Subobject.ofLE_comp_ofLE]
  rintro ⟨y⟩
  obtain ⟨z',hz'⟩ := y.property
  rcases hall (P.pageπ ⊤ z') with h0|h1
  · left
    apply (NestedQuotient.projection_eq_zero y).mpr
    rw [←hz']
    exact zero_of_infinity_zero z' h0
  · right
    apply sub_eq_zero.mp
    change NestedQuotient.projection _ _ y - NestedQuotient.projection _ _ x'=0
    rw [←map_sub]
    apply (NestedQuotient.projection_eq_zero (y-x')).mpr
    change y.val-x ∈ _
    rw [←hz',←hz,←map_sub]
    exact zero_of_infinity_zero (z'-z) (by rw [map_sub,h1,sub_self])



private theorem prop78_detection_data_bridge_theta_sphere_frame {D : Model H M Syn}
    (I : KIP126.Computation.Route.Inputs D L G) (BHS : SyntheticInputs D)
    (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∀ e : ((D.family.sphere).sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (s,t,t-k) (D.sphereE2 s t k x) e := by
  have prop78_detection_data_bridge_family_map_data {X Y : Syn} (f : X ⟶ Y) (i : Tridegree) :
      familyPageMap D.family f 2 i = (D.family.functor.map f).toSSDataMorphism.pageMap i 0 := by
    let F := (D.family.functor.map f).toSSDataMorphism
    let PX := (D.family.functor.obj X).ssData i
    let PY := (D.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(2-(D.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(2-(D.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat ℤ) _ (PX.page 0) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page 0) _) = F.pageMap i 0
    have hX : nX=0 := by dsimp only [nX]; rw [D.family.firstPage X]; rfl
    have hY : nY=0 := by dsimp only [nY]; rw [D.family.firstPage Y]; rfl
    have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
        (n m : WithTop ℕ) (hn : n=0) (hm : m=0)
        (h1 : A 0=A n) (h2 : B n=B m) (h3 : B m=B 0) :
        eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j 0 := by
      subst n
      subst m
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY hX hY _ _ _
  have map_infinity {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
      (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
      (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
      HasInfinityRepresentative (D.family.obj Y) 2 i
        (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
    obtain ⟨hr,z,hz,he⟩ := hy
    change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
      (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
    let F := (D.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · rw [prop78_detection_data_bridge_family_map_data]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
        (((D.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [←F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
        rw [he])
  obtain ⟨x',hx',hframe⟩ := prop78_detection_data_bridge_theta_quotient_frame I s t k hst hsk x hx
  intro e
  let i : Tridegree := (s,t,t-k)
  let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap i
  let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap i
  have hfg : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  have hback : f (g e)=e := ConcreteCategory.congr_hom hfg e
  let nuE := BHS.eInfty.presentation.nuWindow SphereSpectrum (s,t) (t-k) (by omega)
  have heqcut : 1+t-(t-(k:ℤ))=1+(k:ℤ) := by omega
  have hfq : nuE (g e)=0 ∨ nuE (g e)=NestedQuotient.projection _ _ x' := by
    have hh : ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+t-(t-(k:ℤ))) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
      rw [heqcut]
      exact hframe
    exact hh (nuE (g e))
  rcases hfq with h0|h1
  · left
    have hg0 : g e=0 := nuE.injective (h0.trans (map_zero nuE).symm)
    rw [←hback,hg0,map_zero]
  · right
    have hr := (BHS.eInfty.labels.2 .sphere (s,t) k x' (g e)).mpr h1
    have hh := map_infinity D.nu.unitIso.hom i _ _ hr
    have hlabel : familyPageMap D.family D.nu.unitIso.hom 2 i
        (targetNuLabel D .sphere s t k x'.val) = D.sphereE2 s t k x := by
      rw [hx']
      dsimp only [targetNuLabel]
      rw [prop78_detection_data_bridge_family_map_data,prop78_detection_data_bridge_family_map_data]
      dsimp only [i] at *
      change ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.pageMap (s,t,t-k) 0 ≫
        (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism.pageMap (s,t,t-k) 0) _ = _
      rw [←SSDataMorphism.pageMap_comp]
      have hp := D.comparisonCompatible.sphere_nu s t k x
      rw [prop78_detection_data_bridge_family_map_data] at hp
      have hm : ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.comp
          (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism) =
          (D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom)).toSSDataMorphism := by
        change (D.family.functor.map _ ≫ D.family.functor.map _).toSSDataMorphism = _
        rw [←CategoryTheory.Functor.map_comp]
      rw [hm]
      exact hp
    change HasInfinityRepresentative D.family.sphere 2 i _ (f (g e)) at hh
    rw [hback,hlabel] at hh
    exact hh


private theorem prop78_detection_data_bridge_theta_detection_step {D : Model H M Syn}
    (i : Tridegree) (x : (D.family.sphere).E₂ i)
    (hframe : ∀ e : ((D.family.sphere).sequence.ssData i).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) i.1 a) :
    DetectsNonzero D.sphereConvergence i x a ∨
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (i.1+1) a := by
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)
  have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0:Syn) (i.2.1-i.1,i.2.2)))
      (F.F i.1 (i.2.1-i.1,i.2.2)) := by
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
  obtain ⟨a',ha'⟩ := ham
  let q := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
  let e := (D.sphereConvergence.identification i).inv q
  have he : (D.sphereConvergence.identification i).hom e=q :=
    ConcreteCategory.congr_hom (D.sphereConvergence.identification i).inv_hom_id q
  by_cases he0 : e=0
  · right
    have hq : F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'=0 := by
      rw [he0,map_zero] at he
      exact he.symm
    have hmem := (subobject_cokernel_π_eq_zero_iff
      (F.F (i.1+1) (i.2.1-i.1,i.2.2)) (F.F i.1 (i.2.1-i.1,i.2.2))
      (F.mono i.1 (i.2.1-i.1,i.2.2)) a').mp hq
    rw [ha'] at hmem
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hmem
  · left
    have hr := (hframe e).resolve_left he0
    exact ⟨⟨e,hr,a',ha',he⟩,e,hr,he0⟩

private theorem prop78_detection_data_bridge_stem124_weight128_filtration11_branches {D : Model H M Syn}
    (I : KIP126.Computation.Route.Inputs D L G) (BHS : SyntheticInputs D)
    (x13 : E2 H SphereSpectrum 13 137)
    (h13 : ClassicalInfinityGenerated 13 137 x13)
    (h11 : Subsingleton ((Computation.Route.sequence D .sphere).Page 5 (11,135)))
    (h12 : Subsingleton ((Computation.Route.sequence D .sphere).Page 4 (12,136)))
    (a : BiHom 124 128 (S_0_0 : Syn))
    (ha11 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a) :
    SphereDetected D 13 137 9 x13 a ∨
      ∃ b : BiHom 124 138 (S_0_0:Syn), lambdaMultiply 10 b=a := by
  have permanentQuotient_zero_of_page_six_zero (s t b : ℤ) (hb : 5 ≤ b)
      (hpage : Subsingleton ((sequence D .sphere).Page 6 (s, t))) :
      Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
    set_option backward.isDefEq.respectTransparency false in
      let E := (sequence D .sphere).ssData (s, t)
      haveI : Subsingleton (E.page 4) := hpage
      have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
          PageRepresentatives.boundaries H SphereSpectrum 5 (s, t) := by
        rintro x ⟨z, hz⟩
        let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 4) (E.Z_anti le_top)) z
        have hzero : E.pageπ 4 zf = 0 := Subsingleton.elim _ _
        obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
          (Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4)) zf).mp hzero
        refine ⟨y, ?_⟩
        change PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) y = x
        have hfactor : Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4) ≫
            PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t) =
            PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) := by
          dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.Route.sequence, object]
          rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
        rw [← hfactor, CategoryTheory.comp_apply]
        apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t)) hy).trans
        exact (congrArg (fun f => f z)
          (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 4 ⊤ le_top)).trans hz
      have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
        rintro ⟨x⟩
        change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
        exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
      exact ⟨fun x y => (hall x).trans (hall y).symm⟩

  have hgap : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 13 a := by
    apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
      11 13 124 128 (by omega) ?_ a).mp
    intro j hj hj'
    have hpage : Subsingleton ((Computation.Route.sequence D .sphere).Page 6 (j,124+j)) := by
      interval_cases j
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 11 135
          (by omega) (by omega) h11
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 12 136
          (by omega) (by omega) h12
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(124+j)-128) (j,124+j)) :=
      permanentQuotient_zero_of_page_six_zero j (124+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,124+j) 128 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,128)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,124+j,128)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,124+j,128)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,124+j,128)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  have ha13 := hgap ha11
  have hf13 := prop78_detection_data_bridge_theta_sphere_frame I BHS 13 137 9 (by omega) (by omega) x13 h13
  rcases prop78_detection_data_bridge_theta_detection_step (13,137,128) (D.sphereE2 13 137 9 x13) hf13 a ha13 with hdet|ha14
  · exact Or.inl hdet
  right
  have hmap {X Y : Syn} (f : X ⟶ Y) {m w s : ℤ} (x : BiHom m w X)
      (hx : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s x) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (x ≫ f) := by
    obtain ⟨z,hz⟩ := hx
    refine ⟨z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat,?_⟩
    change (z ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat) ≫
      adamsTowerMap (nuCoefficientUnit H.unit D.nu) Y 0 s.toNat _ = x ≫ f
    change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) X 0 s.toNat _ = x at hz
    rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hz]
    rfl
  have h := BHS.filtration_lambda .sphere 124 128 14 (by omega) (a ≫ D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (a ≫ D.nu.unitIso.inv) ↔
    ∃ b : BiHom 124 138 (D.nu.functor.obj SphereSpectrum), lambdaMultiply 10 b=a ≫ D.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (hmap D.nu.unitIso.inv a ha14)
  refine ⟨b ≫ D.nu.unitIso.hom,?_⟩
  simpa [lambdaMultiply,Category.assoc] using congrArg (fun q => q ≫ D.nu.unitIso.hom) hb

private theorem prop78_detection_data_bridge_eta_weight128_branches_filtration_fifteen {D : Model H M Syn}
    (I : KIP126.Computation.Route.Inputs D L G) (SF : Derived.SphereFacts I.realization)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toModelData η)
    (b : BiHom 124 128 (S_0_0 : Syn))
    (hbranch : SphereDetected D 13 137 9 (I.realization.sphere 13 137 correction)
        b ∨
      ∃ a : BiHom 124 138 (S_0_0 : Syn), lambdaMultiply 10 a=b) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (sphereProduct η b) := by
  have hη0 : lambdaMultiply 0 η=η := by
    have hc := D.shiftCoherence.right_unit (1,2) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 1 2 : Syn) := by
      change (biShiftAddIso (1,2) (0,0) (1,2) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [Nat.cast_zero,neg_zero,sub_zero,eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (1,2) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn) ≫ η=η
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hηd := D.comparisonCompatible.homotopy_lambda 1 2 0 η
  rw [hη0,hη] at hηd
  rcases hbranch with h13 | ⟨a,ha⟩
  · have hp : Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137)
        (Sphere.Internal.hi H M 1) (I.realization.sphere 13 137 correction)=0 := by
      have h := I.products ⟨1,2,13,137⟩ (by simp [Raw.products]) dataH1 correction
      dsimp only at h
      rw [I.labels.h1] at h
      exact h.symm.trans SF.h1_correction_zero
    have hd := D.multiplicationCompatible 1 2 13 137 0 9
      (Sphere.Internal.hi H M 1) (I.realization.sphere 13 137 correction)
      η b hηd h13.1
    change Detects D.sphereConvergence (14,139,130)
      (D.sphereE2 14 139 9 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137)
        (Sphere.Internal.hi H M 1) (I.realization.sphere 13 137 correction)))
      (sphereProduct η b) at hd
    rw [hp,map_zero] at hd
    exact detects_zero_filtration D.sphereConvergence (14,139,130) hd
  · have had := D.comparisonCompatible.homotopy_lambda 14 138 10 a
    rw [ha] at had
    have hd := D.multiplicationCompatible 1 2 14 138 0 10
      (Sphere.Internal.hi H M 1) (D.sphereFirstQuotient 14 138 (quotientClass 1 a))
      η b hηd had
    change Detects D.sphereConvergence (15,140,130) _ (sphereProduct η b) at hd
    obtain ⟨e,he,a',ha',hgr⟩ := hd
    rw [←ha']
    have hm : ((towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)).F 15 (125,130)).arrow a'∈
        (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : Syn) (125,130)))
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)).F 15 (125,130)) := ⟨a',rfl⟩
    simpa only [FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply,SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hm

private theorem prop78_detection_data_bridge_eta_weight128_filtration_eleven {D : Model H M Syn}
    (I : KIP126.Computation.Route.Inputs D L G) (BHS : SyntheticInputs D) (SF : Derived.SphereFacts I.realization)
    (h13 : ClassicalInfinityGenerated 13 137 (I.realization.sphere 13 137 correction))
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toModelData η)
    (a : BiHom 124 128 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (sphereProduct η a) := by
  exact prop78_detection_data_bridge_eta_weight128_branches_filtration_fifteen I SF η hη a
    (prop78_detection_data_bridge_stem124_weight128_filtration11_branches I BHS _ h13
      SF.e5_stem124_af11 SF.e4_stem124_af12 a ha)

private theorem prop78_detection_data_bridge_theta_u_eta_filtration_error {D : Model H M Syn}
    (I : KIP126.Computation.Route.Inputs D L G) (BHS : SyntheticInputs D) (SF : Derived.SphereFacts I.realization)
    (h13 : ClassicalInfinityGenerated 13 137 (I.realization.sphere 13 137 correction))
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toModelData η)
    (θ : BiHom 62 64 (S_0_0 : Syn)) (hc4 : C4At M D.toModelData L θ)
    (u : BiHom 124 134 (S_0_0 : Syn)) (hu : UChoice M D.toModelData L u) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15
      ((show BiHom 125 130 (S_0_0 : Syn) from sphereProduct η (sphereProduct θ θ)) -
        (show BiHom 125 130 (S_0_0 : Syn) from lambdaMultiply 3 (lambdaMultiply 3 (sphereProduct η u)))) := by
  have hfirst := prop78_detection_data_bridge_sphere_zero_weight_label_10_134 BHS.eInfty (L.U M) u hu.1
  have hu6 := D.comparisonCompatible.homotopy_lambda 10 134 6 u
  rw [hfirst] at hu6
  have hdelta := detects_sub_filtration D.sphereConvergence (10,134,128) hc4.1 hu6
  have heta := prop78_detection_data_bridge_eta_weight128_filtration_eleven I BHS SF h13 η hη _ hdelta
  have he : sphereProduct η ((show BiHom 124 128 (S_0_0 : Syn) from sphereProduct θ θ)-(show BiHom 124 128 (S_0_0 : Syn) from lambdaMultiply 6 u))=
      (show BiHom 125 130 (S_0_0 : Syn) from sphereProduct η (sphereProduct θ θ))-(show BiHom 125 130 (S_0_0 : Syn) from sphereProduct η (lambdaMultiply 6 u)) := by
    simp only [sphereProduct,Preadditive.comp_sub,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat]
  rw [he,prop78_detection_data_bridge_eta_lambda6_right D η u,←prop78_detection_data_bridge_lambda_three_3_136 D (sphereProduct η u)] at heta
  exact heta

private theorem prop78_detection_data_bridge_lambda_three_preserves_filtration_fifteen {D : Model H M Syn}
    (BHS : SyntheticInputs D) (a : BiHom 125 133 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (lambdaMultiply 3 a) := by
  have h := BHS.filtration_lambda .sphere 125 133 15 (by omega) (a≫D.nu.unitIso.inv)
  change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (a≫D.nu.unitIso.inv) ↔
    ∃ b : BiHom 125 140 (D.nu.functor.obj SphereSpectrum),lambdaMultiply 7 b=a≫D.nu.unitIso.inv at h
  obtain ⟨b,hb⟩ := h.mp (prop78_detection_data_bridge_map_filtration (D:=D) D.nu.unitIso.inv a ha)
  let c : BiHom 125 140 (S_0_0 : Syn) := b≫D.nu.unitIso.hom
  have hc : lambdaMultiply 7 c=a := by
    simpa only [c,lambdaMultiply,Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      congrArg (fun z=>z≫D.nu.unitIso.hom) hb
  apply (prop78_detection_data_bridge_lambda_10_iff_filtration_15 BHS _).mp
  apply (prop78_detection_data_bridge_vanishes_mod_lambda_iff_multiple 10 125 140 _).mpr
  exact ⟨c,by rw [←hc,prop78_detection_data_bridge_lambda_three_7_140 D c]⟩

private theorem prop78_detection_data_bridge_sphere_first_label_transport {D : Model H M Syn} (s t : ℤ)
    (x : E2 H SphereSpectrum s t) :
    D.sphereFirstQuotient s t
      (firstLabel D .sphere s t x ≫ XModLambdaN.map
        (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom) 1)=x := by
  let e : nuZero D .sphere ≅ (S_0_0 : Syn) :=
    SyntheticCategory.biShift_zero.app _ ≪≫ D.nu.unitIso
  let q := (D.quotientFunctoriality.functor 1).mapIso e
  let c : BiHom (t-s) t (XModLambdaN (nuZero D .sphere) 1) ≃+ E2 H SphereSpectrum s t :=
    Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z (XModLambdaN (nuZero D .sphere) 1) ≃+
      E2 H SphereSpectrum s t) (Int.add_zero t)) (D.firstQuotient SphereSpectrum 0 s t)
  change c ((firstLabel D .sphere s t x ≫ q.hom) ≫ q.inv)=x
  rw [Category.assoc,q.hom_inv_id]
  erw [Category.comp_id]
  have cast_symm (w₁ w₂ : ℤ) (h : w₁=w₂)
      (E : BiHom (t-s) w₁ (XModLambdaN (nuZero D .sphere) 1) ≃+ E2 H SphereSpectrum s t)
      (x : E2 H SphereSpectrum s t) :
      Eq.mp (congrArg (fun z => BiHom (t-s) z (XModLambdaN (nuZero D .sphere) 1)) h) (E.symm x) =
        (Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z (XModLambdaN (nuZero D .sphere) 1) ≃+
          E2 H SphereSpectrum s t) h) E).symm x := by
    subst w₂
    rfl
  have hx : firstLabel D .sphere s t x=c.symm x := by
    dsimp only [firstLabel,c,ClassicalObject.obj,nuZero]
    exact cast_symm (t+0) t (Int.add_zero t) (D.firstQuotient SphereSpectrum 0 s t) x
  rw [hx,c.apply_symm_apply]

private theorem prop78_detection_data_bridge_sphere_permanent_first_quotient_lift {D : Model H M Syn}
    (synthetic : SyntheticInputs D) (s t : ℤ) (x : E2 H SphereSpectrum s t)
    (hx : IsPermanentCycle (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (s,t) x) :
    ∃ a : BiHom (t-s) t (S_0_0 : Syn), D.sphereFirstQuotient s t (quotientClass 1 a)=x := by
  have hp : x∈PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := by
    exact hx
  obtain ⟨a,ha⟩ := (synthetic.permanent_lift .sphere s t x).mp hp
  let e := SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom
  refine ⟨a≫e,?_⟩
  have hc : quotientClass 1 (a≫e)=quotientClass 1 a≫XModLambdaN.map e 1 := by
    unfold quotientClass
    simp only [Category.assoc]
    exact congrArg (fun h => a≫h) (XModLambdaN.incl_naturality e 1)
  rw [hc,ha]
  exact prop78_detection_data_bridge_sphere_first_label_transport s t x

private theorem prop78_detection_data_bridge_detects_of_difference_in_next_filtration
    {H' : Syn} {unit : S_0_0 ⟶ H'} {F : SyntheticAdamsFamily Syn} {X : Syn}
    (c : TowerConvergence unit F X) (i : Tridegree)
    {x : (F.obj X).E₂ i} {a b : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a) (hb : FiltrationAtLeast unit (i.1+1) (b-a)) :
    Detects c i x b := by
  obtain ⟨e,he,a',ha',hga⟩ := ha
  let P := towerFiltration unit X
  let p := (i.2.1-i.1,i.2.2)
  have hmem : b-a∈(ModuleCat.subobjectModule (syntheticHomotopy X p)) (P.F (i.1+1) p) := by
    simpa only [P,p,FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply] using hb
  obtain ⟨z,hz⟩ := hmem
  let j := Subobject.ofLE (P.F (i.1+1) p) (P.F i.1 p) (P.mono i.1 p)
  refine ⟨e,he,a'+j z,?_,?_⟩
  · rw [map_add]
    have hj : (P.F i.1 p).arrow (j z)=(P.F (i.1+1) p).arrow z :=
      ConcreteCategory.congr_hom (Subobject.ofLE_arrow (P.mono i.1 p)) z
    rw [hj,ha',hz]
    abel
  · rw [map_add]
    have hj : P.toAssociatedGraded i.1 p (j z)=0 :=
      ConcreteCategory.congr_hom (cokernel.condition j) z
    rw [hj,add_zero]
    exact hga

private theorem prop78_detection_data_bridge_target_detection_lambda_three {D : Model H M Syn}
    (BHS : SyntheticInputs D) (x : E2 H SphereSpectrum 14 139)
    (hx : IsPermanentCycle (sequence D .sphere) (14,139) x)
    (c : BiHom 125 133 (S_0_0 : Syn))
    (hc : Detects D.sphereConvergence (14,139,133) (D.sphereE2 14 139 6 x) c) :
    Detects D.sphereConvergence (14,139,130) (D.sphereE2 14 139 9 x) (lambdaMultiply 3 c) := by
  obtain ⟨t,ht⟩ := prop78_detection_data_bridge_sphere_permanent_first_quotient_lift BHS 14 139 x hx
  have ht6 := D.comparisonCompatible.homotopy_lambda 14 139 6 t
  rw [ht] at ht6
  have hdiff := detects_sub_filtration D.sphereConvergence (14,139,133) hc ht6
  have hdiff3 := prop78_detection_data_bridge_lambda_three_preserves_filtration_fifteen BHS _ hdiff
  have hlin : lambdaMultiply 3 (c-(show BiHom 125 133 (S_0_0 : Syn) from lambdaMultiply 6 t))=
      (show BiHom 125 130 (S_0_0 : Syn) from lambdaMultiply 3 c)-
      (show BiHom 125 130 (S_0_0 : Syn) from lambdaMultiply 3 (lambdaMultiply 6 t)) := by
    simp only [lambdaMultiply,Preadditive.comp_sub,Nat.cast_ofNat,Int.reduceSub]
  rw [hlin,prop78_detection_data_bridge_lambda_three_6_139 D t] at hdiff3
  have ht9 := D.comparisonCompatible.homotopy_lambda 14 139 9 t
  rw [ht] at ht9
  exact prop78_detection_data_bridge_detects_of_difference_in_next_filtration D.sphereConvergence (14,139,130) ht9 hdiff3

private theorem prop78_detection_data_bridge_c4_c5_eta_target_detected {D : Model H M Syn}
    (I : KIP126.Computation.Route.Inputs D L G) (BHS : SyntheticInputs D) (SF : Derived.SphereFacts I.realization)
    (h13 : ClassicalInfinityGenerated 13 137 (I.realization.sphere 13 137 correction))
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toModelData η)
    (θ : BiHom 62 64 (S_0_0 : Syn)) (hc4 : C4At M D.toModelData L θ)
    (u : BiHom 124 134 (S_0_0 : Syn)) (hu : UChoice M D.toModelData L u)
    (hc5 : C5At M D.toModelData L η u) :
    Detects D.sphereConvergence (14,139,130) (D.sphereE2 14 139 9 (L.target M))
      (sphereProduct η (sphereProduct θ θ)) := by
  have hp := SF.t_permanent_cycle
  rw [(route_expression_labels I).2.2] at hp
  have hlow := prop78_detection_data_bridge_target_detection_lambda_three BHS (L.target M) hp _ hc5
  exact prop78_detection_data_bridge_detects_of_difference_in_next_filtration D.sphereConvergence (14,139,130) hlow
    (prop78_detection_data_bridge_theta_u_eta_filtration_error I BHS SF h13 η hη θ hc4 u hu)

private theorem prop78_detection_data_bridge_survives_twelve_not_boundary_eleven (X : C) (p : ℤ × ℤ)
    (x : E2 H X p.1 p.2)
    (hx : SurvivesTo (adamsTowerInternalSpectralSequence H.unit X) 12 p x) :
    x∉PageRepresentatives.boundaries H X 11 p := by
  obtain ⟨xr,hrep,hne⟩ := hx
  obtain ⟨hr,z,hz,hzr⟩ := hrep
  rintro ⟨b,hb⟩
  let P := (adamsTowerInternalSpectralSequence H.unit X).ssData p
  change (Subobject.underlying.obj (P.Z 10) : ModuleCat ℤ) at z
  change (Subobject.ofLE (P.Z 10) (P.Z 0) (P.Z_anti (by decide)) ≫ P.pageπ 0) z = x at hz
  change P.pageπ 10 z = xr at hzr
  let bz := (Subobject.ofLE (P.B 10) (P.Z 10) (P.B_le_Z 10)) b
  have he : (Subobject.ofLE (P.Z 10) (P.Z 0) (P.Z_anti (by decide)) ≫ P.pageπ 0) (z-bz)=0 := by
    rw [map_sub,hz]
    have hbz : (Subobject.ofLE (P.Z 10) (P.Z 0) (P.Z_anti (by decide)) ≫ P.pageπ 0) bz=x := by
      change (Subobject.ofLE (P.B 10) (P.Z 10) _ ≫
        Subobject.ofLE (P.Z 10) (P.Z 0) _ ≫ P.pageπ 0) b = x
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hb
    rw [hbz,sub_self]
  have hm := (subobject_cokernel_π_eq_zero_iff (P.B 0) (P.Z 0) (P.B_le_Z 0)
    ((Subobject.ofLE (P.Z 10) (P.Z 0) (P.Z_anti (by decide))) (z-bz))).mp he
  change (Subobject.ofLE (P.Z 10) (P.Z 0) _ ≫ (P.Z 0).arrow) (z-bz) ∈ _ at hm
  rw [Subobject.ofLE_arrow] at hm
  have hm' := (ModuleCat.subobjectModule P.V).monotone (P.B_mono (by decide : (0:WithTop ℕ)≤10)) hm
  have hb' : (P.Z 10).arrow bz ∈ (ModuleCat.subobjectModule P.V) (P.B 10) := by
    refine ⟨b,?_⟩
    exact (ConcreteCategory.congr_hom (Subobject.ofLE_arrow (P.B_le_Z 10)) b).symm
  have hz' := ((ModuleCat.subobjectModule P.V) (P.B 10)).add_mem hm' hb'
  rw [map_sub,sub_add_cancel] at hz'
  apply hne
  rw [← hzr]
  exact (subobject_cokernel_π_eq_zero_iff (P.B 10) (P.Z 10) (P.B_le_Z 10) z).mpr hz'

private theorem prop78_detection_data_bridge_sphere_label_to_nu {D : Model H M Syn} (s t : ℤ) (k : ℕ) (x : E2 H SphereSpectrum s t) :
    familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)=
      targetNuLabel D .sphere s t k x := by
  let nx : (D.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (D.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
    simpa only [ClassicalObject.obj,add_zero] using D.nuE2 .sphere 0 s t k x
  have hbase : familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)=
      targetNuLabel D .sphere s t k x := by
    have hc : familyPageMap D.family
        (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k) nx =
        D.sphereE2 s t k x := by
      convert D.comparisonCompatible.sphere_nu s t k x using 1 <;> simp [nx,ClassicalObject.obj] <;> rfl
    calc
      _ = familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k)
          (familyPageMap D.family (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 2 (s,t,t-k)
            nx) := congrArg (fun y => familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) y) hc.symm
      _ = familyPageMap D.family ((SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) ≫ D.nu.unitIso.inv)
          2 (s,t,t-k) nx :=
        ConcreteCategory.congr_hom (prop78_detection_data_bridge_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  exact hbase

private theorem prop78_detection_data_bridge_sphere_target_nine_nonzero_of_survives_twelve {D : Model H M Syn}
    (BHS : EInftyInput D) (x : E2 H SphereSpectrum 14 139)
    (hp : IsPermanentCycle (sequence D .sphere) (14,139) x)
    (hs : SurvivesTo (sequence D .sphere) 12 (14,139) x)
    (e : ((D.family.sphere).sequence.ssData (14,139,130)).eInfty)
    (he : HasInfinityRepresentative D.family.sphere 2 (14,139,130)
      (D.sphereE2 14 139 9 x) e) : e≠0 := by
  have hn := prop78_detection_data_bridge_family_infinity_representative_map D.nu.unitIso.inv (14,139,130) _ _ he
  have hl := prop78_detection_data_bridge_sphere_label_to_nu (D:=D) 14 139 9 x
  change familyPageMap D.family D.nu.unitIso.inv 2 (14,139,130) (D.sphereE2 14 139 9 x)=_ at hl
  rw [hl] at hn
  have hf := (BHS.labels.2 .sphere (14,139) 9 ⟨x,hp⟩ _).mp hn
  intro hz
  rw [hz,map_zero,map_zero] at hf
  have hb := (NestedQuotient.projection_eq_zero ⟨x,hp⟩).mp hf.symm
  exact prop78_detection_data_bridge_survives_twelve_not_boundary_eleven SphereSpectrum (14,139) x hs
    (PageRepresentatives.boundaries_monotone H SphereSpectrum (14,139) (by decide : (10:ℤ)≤11) hb)

private theorem prop78_detection_data_bridge_target_detected_not_filtration_fifteen {D : Model H M Syn}
    (BHS : EInftyInput D) (x : E2 H SphereSpectrum 14 139)
    (hp : IsPermanentCycle (sequence D .sphere) (14,139) x)
    (hs : SurvivesTo (sequence D .sphere) 12 (14,139) x)
    (a : BiHom 125 130 (S_0_0 : Syn))
    (ha : Detects D.sphereConvergence (14,139,130) (D.sphereE2 14 139 9 x) a) :
    ¬FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a := by
  intro hf
  have hz : Detects D.sphereConvergence (14,139,130) 0 0 :=
    ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) _,0,map_zero _,by simp only [map_zero]⟩
  have hza : Detects D.sphereConvergence (14,139,130) 0 a :=
    prop78_detection_data_bridge_detects_of_difference_in_next_filtration D.sphereConvergence (14,139,130) hz
      (by simpa only [sub_zero,SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hf)
  obtain ⟨e,he,he0⟩ := prop78_detection_data_bridge_detects_infinity_equal .sphere (14,139,130) a _ 0 ha hza
  exact prop78_detection_data_bridge_sphere_target_nine_nonzero_of_survives_twelve BHS x hp hs e he
    (he0.unique (HasInfinityRepresentative.zero _ 2 (by decide) _))

private theorem prop78_detection_data_finite_sphere_infinity_nonzero {D : Model H M Syn}
    (BHS : EInftyInput D) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (hx : x∈PageRepresentatives.cycles H SphereSpectrum q (s,t)) (hne : x≠0)
    (e : ((D.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-0)).eInfty)
    (he : HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-0)
      (D.quotientLabel q s t 0 x) e) : e≠0 := by
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hh := prop78_detection_data_bridge_family_infinity_representative_map g (s,t,t-0) _ _ he
  have hl := prop78_detection_data_bridge_sphere_quotient_label_to_nu (D:=D) q 0 s t x
  change familyPageMap D.family g 2 (s,t,t-0) (D.quotientLabel q s t 0 x)=_ at hl
  rw [hl] at hh
  let y : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-0)) (s,t) :=
    ⟨x,by simpa only [sub_zero,sub_add_cancel] using hx⟩
  have hp := (BHS.labels.1 .sphere q hq (s,t) 0 hq y _).mp hh
  intro he0
  rw [he0,map_zero,map_zero] at hp
  have hm := (NestedQuotient.projection_eq_zero y).mp hp.symm
  have hb : (1:ℤ)+t-(t-0)=1 := by omega
  change x∈PageRepresentatives.boundaries H SphereSpectrum (1+t-(t-0)) (s,t) at hm
  rw [hb,PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
  exact hne hm

private theorem prop78_detection_data_sphere_zero_weight_nonzero_detection_u {D : Model H M Syn}
    (BHS : EInftyInput D) (x : E2 H SphereSpectrum 10 134)
    (a : BiHom (134-10) 134 (S_0_0 : Syn))
    (ha : D.sphereFirstQuotient 10 134 (quotientClass 1 a)=x) (hne : x≠0) :
    SphereDetected D 10 134 0 x a := by
  have h0 : lambdaMultiply 0 a=a := by
    have hc := D.shiftCoherence.right_unit (134-10,134) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (134-10,134) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn (134-10) 134 : Syn) := by
      change (biShiftAddIso (134-10,134) (0,0) (134-10,134) (by simp)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [Nat.cast_zero,neg_zero,sub_zero,eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (134-10,134) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (134-10,134) (0,0)).hom.app (S_0_0 : Syn) ≫ a=a
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hd := D.comparisonCompatible.homotopy_lambda 10 134 0 a
  rw [h0,ha] at hd
  refine ⟨hd,?_⟩
  obtain ⟨e,he,_⟩ := hd
  refine ⟨e,he,?_⟩
  let f := XModLambdaN.incl (S_0_0 : Syn) 1
  have hf := prop78_detection_data_bridge_family_infinity_representative_map f (10,134,134-0) _ _ he
  have hcycle : x∈PageRepresentatives.cycles H SphereSpectrum 1 (10,134) := by
    rw [PageRepresentatives.cycles_one]
    exact Submodule.mem_top
  have hfn := prop78_detection_data_finite_sphere_infinity_nonzero BHS 1 (by decide) 10 134 x hcycle hne _ hf
  intro hz
  apply hfn
  rw [hz,map_zero]

private theorem prop78_detection_data_u_choice_exists {D : Model H M Syn} (I : KIP126.Computation.Route.Inputs D L G) (BHS : SyntheticInputs D)
    (SF : Derived.SphereFacts I.realization) : ∃u,UChoice M D.toModelData L u := by
  have hp := SF.u_permanent
  change NonzeroSurvival (sequence D .sphere) (10,134) (I.realization.sphere 10 134 U) at hp
  rw [(route_expression_labels I).2.1] at hp
  obtain ⟨z,hz,hzn⟩ := hp
  have hcycle : IsPermanentCycle (sequence D .sphere) (10,134) (L.U M) := ⟨z,hz⟩
  have hn : L.U M≠0 := by
    intro h0
    let P := (sequence D .sphere).ssData (10,134)
    have hz0 : (Subobject.ofLE (P.Z ⊤) (P.Z 0) (P.Z_anti le_top) ≫ P.pageπ 0) z=L.U M := hz
    have hh := P.infinity_projection_eq_of_page_projection_eq 0 z 0
      (by simpa only [map_zero] using hz0.trans h0)
    exact hzn (by simpa only [map_zero] using hh)
  obtain ⟨u,hu⟩ := prop78_detection_data_bridge_sphere_permanent_first_quotient_lift BHS 10 134 (L.U M) hcycle
  exact ⟨u,prop78_detection_data_sphere_zero_weight_nonzero_detection_u BHS.eInfty (L.U M) u hu hn⟩

private theorem prop78_detection_data_permanent_quotient_frame_of_page_six {D : Model H M Syn}
    (s t : ℤ) (k : ℕ) (hk : 4≤k) (x : E2 H SphereSpectrum s t)
    (hx : IsPermanentCycle (sequence D .sphere) (s,t) x)
    (a : (sequence D .sphere).Page 6 (s,t))
    (ha : RepresentsOnPage (sequence D .sphere) 6 (s,t) x a)
    (hall : ∀ y : (sequence D .sphere).Page 6 (s,t),y=0∨y=a) :
    ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t),x'.val=x ∧
      ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
        q=0∨q=NestedQuotient.projection _ _ x' := by
  let E := sequence D .sphere
  let P := E.ssData (s,t)
  obtain ⟨z,hz⟩ := hx
  change (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ) at z
  change PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) z=x at hz
  let x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t) := ⟨x,⟨z,hz⟩⟩
  let incl := Subobject.ofLE (P.Z ⊤) (P.Z 4) (P.Z_anti le_top)
  let val (q : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ)) := P.pageπ 4 (incl q)
  have rep : RepresentsOnPage E 6 (s,t) x (val z) := by
    refine ⟨by decide,incl z,?_,rfl⟩
    change PageRepresentatives.cycleMap H SphereSpectrum 4 (s,t) (incl z)=x
    exact (ConcreteCategory.congr_hom
      (PageRepresentatives.cycleMap_factor H SphereSpectrum (s,t) 4 ⊤ le_top) z).trans hz
  have hvz : val z=a := represents_unique (E:=E) (r:=6) (p:=(s,t)) (x:=x) rep ha
  have zero_of_page_zero (q : (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ))
      (hq : val q=0) : PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) q ∈
        PageRepresentatives.boundaries H SphereSpectrum (1+(k:ℤ)) (s,t) := by
    obtain ⟨b,hb⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (P.B 4) (P.Z 4) (P.B_le_Z 4)) (incl q)).mp hq
    have h5 : PageRepresentatives.cycleMap H SphereSpectrum ⊤ (s,t) q ∈
        PageRepresentatives.boundaries H SphereSpectrum 5 (s,t) := by
      refine ⟨b,?_⟩
      change PageRepresentatives.boundaryMap H SphereSpectrum 4 (s,t) b=_
      have hfactor : Subobject.ofLE (P.B 4) (P.Z 4) (P.B_le_Z 4) ≫
          PageRepresentatives.cycleMap H SphereSpectrum 4 (s,t)=
          PageRepresentatives.boundaryMap H SphereSpectrum 4 (s,t) := by
        dsimp only [PageRepresentatives.boundaryMap,PageRepresentatives.cycleMap,P,E,KIP126.Computation.Route.sequence,KIP126.Computation.Route.object]
        rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      rw [←hfactor,CategoryTheory.comp_apply]
      change PageRepresentatives.cycleMap H SphereSpectrum 4 (s,t) ((Subobject.ofLE (P.B 4) (P.Z 4) (P.B_le_Z 4)) b)=_
      exact (congrArg (fun w => PageRepresentatives.cycleMap H SphereSpectrum 4 (s,t) w) hb).trans (ConcreteCategory.congr_hom
        (PageRepresentatives.cycleMap_factor H SphereSpectrum (s,t) 4 ⊤ le_top) q)
    exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s,t) (by omega : (5:ℤ)≤1+k) h5
  refine ⟨x',rfl,?_⟩
  rintro ⟨y⟩
  obtain ⟨z',hz'⟩ := y.property
  change (Subobject.underlying.obj (P.Z ⊤) : ModuleCat ℤ) at z'
  rcases hall (val z') with h0|h1
  · left
    apply (NestedQuotient.projection_eq_zero y).mpr
    rw [←hz']
    exact zero_of_page_zero z' h0
  · right
    apply sub_eq_zero.mp
    change NestedQuotient.projection _ _ y-NestedQuotient.projection _ _ x'=0
    rw [←map_sub]
    apply (NestedQuotient.projection_eq_zero (y-x')).mpr
    change y.val-x∈_
    rw [←hz',←hz,←map_sub]
    exact zero_of_page_zero (z'-z) (by
      change P.pageπ 4 (incl (z'-z))=0
      rw [map_sub,map_sub]
      change val z'-val z=0
      rw [h1,hvz,sub_self])

private theorem prop78_detection_data_sphere_frame_of_permanent_quotient {D : Model H M Syn}
    (BHS : SyntheticInputs D)
    (s t : ℤ) (k : ℕ)
    (x : E2 H SphereSpectrum s t)
    (hq : ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t),x'.val=x ∧
      ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
        q=0∨q=NestedQuotient.projection _ _ x') :
    ∀ e : ((D.family.sphere).sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (s,t,t-k) (D.sphereE2 s t k x) e := by
  have family_map_data {X Y : Syn} (f : X ⟶ Y) (i : Tridegree) :
      familyPageMap D.family f 2 i = (D.family.functor.map f).toSSDataMorphism.pageMap i 0 := by
    let F := (D.family.functor.map f).toSSDataMorphism
    let PX := (D.family.functor.obj X).ssData i
    let PY := (D.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(2-(D.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(2-(D.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat ℤ) _ (PX.page 0) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page 0) _) = F.pageMap i 0
    have hX : nX=0 := by dsimp only [nX]; rw [D.family.firstPage X]; rfl
    have hY : nY=0 := by dsimp only [nY]; rw [D.family.firstPage Y]; rfl
    have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
        (n m : WithTop ℕ) (hn : n=0) (hm : m=0)
        (h1 : A 0=A n) (h2 : B n=B m) (h3 : B m=B 0) :
        eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j 0 := by
      subst n
      subst m
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY hX hY _ _ _
  have map_infinity {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
      (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
      (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
      HasInfinityRepresentative (D.family.obj Y) 2 i
        (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
    obtain ⟨hr,z,hz,he⟩ := hy
    change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
      (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
    let F := (D.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · rw [family_map_data]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
        (((D.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [←F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
        rw [he])
  obtain ⟨x',hx',hframe⟩ := hq
  intro e
  let i : Tridegree := (s,t,t-k)
  let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap i
  let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap i
  have hfg : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  have hback : f (g e)=e := ConcreteCategory.congr_hom hfg e
  let nuE := BHS.eInfty.presentation.nuWindow SphereSpectrum (s,t) (t-k) (by omega)
  have heqcut : 1+t-(t-(k:ℤ))=1+(k:ℤ) := by omega
  have hfq : nuE (g e)=0 ∨ nuE (g e)=NestedQuotient.projection _ _ x' := by
    have hh : ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+t-(t-(k:ℤ))) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
      rw [heqcut]
      exact hframe
    exact hh (nuE (g e))
  rcases hfq with h0|h1
  · left
    have hg0 : g e=0 := nuE.injective (h0.trans (map_zero nuE).symm)
    rw [←hback,hg0,map_zero]
  · right
    have hr := (BHS.eInfty.labels.2 .sphere (s,t) k x' (g e)).mpr h1
    have hh := map_infinity D.nu.unitIso.hom i _ _ hr
    have hlabel : familyPageMap D.family D.nu.unitIso.hom 2 i
        (targetNuLabel D .sphere s t k x'.val) = D.sphereE2 s t k x := by
      rw [hx']
      dsimp only [targetNuLabel]
      rw [family_map_data,family_map_data]
      dsimp only [i] at *
      change ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.pageMap (s,t,t-k) 0 ≫
        (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism.pageMap (s,t,t-k) 0) _ = _
      rw [←SSDataMorphism.pageMap_comp]
      have hp := D.comparisonCompatible.sphere_nu s t k x
      rw [family_map_data] at hp
      have hm : ((D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum))).toSSDataMorphism.comp
          (D.family.functor.map D.nu.unitIso.hom).toSSDataMorphism) =
          (D.family.functor.map (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom)).toSSDataMorphism := by
        change (D.family.functor.map _ ≫ D.family.functor.map _).toSSDataMorphism = _
        rw [←CategoryTheory.Functor.map_comp]
      rw [hm]
      exact hp
    change HasInfinityRepresentative D.family.sphere 2 i _ (f (g e)) at hh
    rw [hback,hlabel] at hh
    exact hh

private theorem prop78_detection_data_target_infinity_frame
    {I : KIP126.Computation.Route.Inputs D L G} (BHS : SyntheticInputs D)
    (SF : Derived.SphereFacts I.realization)
    (hframe6 : (∃ a : (sequence D .sphere).Page 6 (14,139),
      RepresentsOnPage (sequence D .sphere) 6 (14,139) (L.target M) a ∧
      ∀ y : (sequence D .sphere).Page 6 (14,139),y=0∨y=a) ∧
      ReachesPage (sequence D .sphere) 1000 (14,139) (L.target M)) (k : ℕ) (hk : 4≤k) :
    ∀ e : ((D.family.sphere).sequence.ssData (14,139,139-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (14,139,139-k)
        (D.sphereE2 14 139 k (L.target M)) e := by
  obtain ⟨⟨a,ha,hall⟩,_⟩ := hframe6
  have hp := SF.t_permanent_cycle
  rw [(route_expression_labels I).2.2] at hp
  exact prop78_detection_data_sphere_frame_of_permanent_quotient BHS 14 139 k (L.target M)
    (prop78_detection_data_permanent_quotient_frame_of_page_six 14 139 k hk (L.target M) hp a ha hall)

private theorem prop78_detection_data_stem125_weight133_filtration_twelve_to_fourteen {D : Model H M Syn}
    (BHS : SyntheticInputs D) (I : KIP126.Computation.Route.Inputs D L G) (SF : Derived.SphereFacts I.realization)
    (a : BiHom 125 133 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12 a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
  have permanentQuotient_zero_of_page_six_zero (s t b : ℤ) (hb : 5 ≤ b)
      (hpage : Subsingleton ((sequence D .sphere).Page 6 (s, t))) :
      Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
    set_option backward.isDefEq.respectTransparency false in
      let E := (sequence D .sphere).ssData (s, t)
      haveI : Subsingleton (E.page 4) := hpage
      have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
          PageRepresentatives.boundaries H SphereSpectrum 5 (s, t) := by
        rintro x ⟨z, hz⟩
        let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 4) (E.Z_anti le_top)) z
        have hzero : E.pageπ 4 zf = 0 := Subsingleton.elim _ _
        obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
          (Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4)) zf).mp hzero
        refine ⟨y, ?_⟩
        change PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) y = x
        have hfactor : Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4) ≫
            PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t) =
            PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) := by
          dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.Route.sequence, object]
          rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
        rw [← hfactor, CategoryTheory.comp_apply]
        apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t)) hy).trans
        exact (congrArg (fun f => f z)
          (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 4 ⊤ le_top)).trans hz
      have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
        rintro ⟨x⟩
        change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
        exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
      exact ⟨fun x y => (hall x).trans (hall y).symm⟩

  have hgap : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12 a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
    apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
      12 14 125 133 (by omega) ?_ a).mp
    intro j hj hj'
    have hpage : Subsingleton ((Computation.Route.sequence D .sphere).Page 6 (j,125+j)) := by
      interval_cases j
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 12 137
          (by omega) (by omega) SF.e4_stem125_af12
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 13 138
          (by omega) (by omega) SF.e5_stem125_af13
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(125+j)-133) (j,125+j)) :=
      permanentQuotient_zero_of_page_six_zero j (125+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,125+j) 133 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,133)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,133)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,125+j,133)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,125+j,133)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  exact hgap ha

private theorem prop78_detection_data_u_choice_eta_lambda_three_filtration_fourteen {D : Model H M Syn}
    (BHS : SyntheticInputs D) (I : KIP126.Computation.Route.Inputs D L G) (SF : Derived.SphereFacts I.realization)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toModelData η)
    (u : BiHom 124 134 (S_0_0 : Syn)) (hu : UChoice M D.toModelData L u) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (lambdaMultiply 3 (sphereProduct η u)) := by
  have hη0 : lambdaMultiply 0 η=η := by
    have hc := D.shiftCoherence.right_unit (1,2) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 1 2 : Syn) := by
      change (biShiftAddIso (1,2) (0,0) (1,2) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [Nat.cast_zero,neg_zero,sub_zero,eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (1,2) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn) ≫ η=η
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hηd := D.comparisonCompatible.homotopy_lambda 1 2 0 η
  rw [hη0,hη] at hηd
  have hp : Sphere.Internal.product H M (s:=1) (t:=2) (s':=10) (t':=134)
      (Sphere.Internal.hi H M 1) (L.U M)=0 := by
    have h := I.products ⟨1,2,10,134⟩ (by simp [Raw.products]) dataH1 U
    dsimp only at h
    rw [I.labels.h1,(route_expression_labels I).2.1] at h
    have hraw : mulAt dataH1 U=0 := by
      apply Subtype.ext
      change h1*((h0*h0)*(atom .x_124_8).val)=0
      rw [←mul_assoc,←mul_assoc,mul_comm h1 h0,h0_mul_h1_eq_zero,zero_mul,zero_mul]
    exact h.symm.trans (by rw [hraw,map_zero])
  have hfirst := prop78_detection_data_bridge_sphere_zero_weight_label_10_134 BHS.eInfty (L.U M) u hu.1
  have hdu := D.comparisonCompatible.homotopy_lambda 10 134 3 u
  rw [hfirst] at hdu
  have hd := D.multiplicationCompatible 1 2 10 134 0 3
    (Sphere.Internal.hi H M 1) (L.U M) η (lambdaMultiply 3 u) hηd hdu
  change Detects D.sphereConvergence (11,136,133)
    (D.sphereE2 11 136 3 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=10) (t':=134)
      (Sphere.Internal.hi H M 1) (L.U M))) (sphereProduct η (lambdaMultiply 3 u)) at hd
  rw [hp,map_zero,prop78_detection_data_bridge_eta_lambda3_right D η u] at hd
  exact prop78_detection_data_stem125_weight133_filtration_twelve_to_fourteen BHS I SF _
    (detects_zero_filtration D.sphereConvergence (11,136,133) hd)

private theorem prop78_detection_data_stem125_filtration_twelve_to_fourteen {D : Model H M Syn}
    (BHS : SyntheticInputs D) (I : KIP126.Computation.Route.Inputs D L G) (SF : Derived.SphereFacts I.realization)
    (a : BiHom 125 130 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12 a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
  have permanentQuotient_zero_of_page_six_zero (s t b : ℤ) (hb : 5 ≤ b)
      (hpage : Subsingleton ((sequence D .sphere).Page 6 (s, t))) :
      Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
    set_option backward.isDefEq.respectTransparency false in
      let E := (sequence D .sphere).ssData (s, t)
      haveI : Subsingleton (E.page 4) := hpage
      have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
          PageRepresentatives.boundaries H SphereSpectrum 5 (s, t) := by
        rintro x ⟨z, hz⟩
        let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 4) (E.Z_anti le_top)) z
        have hzero : E.pageπ 4 zf = 0 := Subsingleton.elim _ _
        obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
          (Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4)) zf).mp hzero
        refine ⟨y, ?_⟩
        change PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) y = x
        have hfactor : Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4) ≫
            PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t) =
            PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) := by
          dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, Computation.Route.sequence, object]
          rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
        rw [← hfactor, CategoryTheory.comp_apply]
        apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t)) hy).trans
        exact (congrArg (fun f => f z)
          (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 4 ⊤ le_top)).trans hz
      have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
        rintro ⟨x⟩
        change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
        exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
      exact ⟨fun x y => (hall x).trans (hall y).symm⟩

  have hgap : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 12 a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
    apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
      12 14 125 130 (by omega) ?_ a).mp
    intro j hj hj'
    have hpage : Subsingleton ((Computation.Route.sequence D .sphere).Page 6 (j,125+j)) := by
      interval_cases j
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 6 12 137
          (by omega) (by omega) SF.e4_stem125_af12
      · exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 13 138
          (by omega) (by omega) SF.e5_stem125_af13
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(125+j)-130) (j,125+j)) :=
      permanentQuotient_zero_of_page_six_zero j (125+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,125+j) 130 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,130)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,130)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,125+j,130)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,125+j,130)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←CategoryTheory.Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  exact hgap ha

private theorem prop78_detection_data_c4_eta_filtration_fourteen {D : Model H M Syn}
    (BHS : SyntheticInputs D) (I : KIP126.Computation.Route.Inputs D L G) (SF : Derived.SphereFacts I.realization)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toModelData η)
    (θ : BiHom 62 64 (S_0_0 : Syn)) (hc4 : C4At M D.toModelData L θ) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (sphereProduct η (sphereProduct θ θ)) := by
  have hη0 : lambdaMultiply 0 η=η := by
    have hc := D.shiftCoherence.right_unit (1,2) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 1 2 : Syn) := by
      change (biShiftAddIso (1,2) (0,0) (1,2) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [Nat.cast_zero,neg_zero,sub_zero,eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (1,2) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn) ≫ η=η
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hηd := D.comparisonCompatible.homotopy_lambda 1 2 0 η
  rw [hη0,hη] at hηd
  have hp : Sphere.Internal.product H M (s:=1) (t:=2) (s':=10) (t':=134)
      (Sphere.Internal.hi H M 1) (L.U M)=0 := by
    have h := I.products ⟨1,2,10,134⟩ (by simp [Raw.products]) dataH1 U
    dsimp only at h
    rw [I.labels.h1,(route_expression_labels I).2.1] at h
    have hraw : mulAt dataH1 U=0 := by
      apply Subtype.ext
      change h1*((h0*h0)*(atom .x_124_8).val)=0
      rw [←mul_assoc,←mul_assoc,mul_comm h1 h0,h0_mul_h1_eq_zero,zero_mul,zero_mul]
    exact h.symm.trans (by rw [hraw,map_zero])
  have hd := D.multiplicationCompatible 1 2 10 134 0 6
    (Sphere.Internal.hi H M 1) (L.U M) η (sphereProduct θ θ) hηd hc4.1
  change Detects D.sphereConvergence (11,136,130)
    (D.sphereE2 11 136 6 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=10) (t':=134)
      (Sphere.Internal.hi H M 1) (L.U M))) (sphereProduct η (sphereProduct θ θ)) at hd
  rw [hp,map_zero] at hd
  exact prop78_detection_data_stem125_filtration_twelve_to_fourteen BHS I SF _
    (detects_zero_filtration D.sphereConvergence (11,136,130) hd)

private theorem prop78_detection_data (I : KIP126.Computation.Route.Inputs D L G)
    (BHS : SyntheticInputs D) (SF : Derived.SphereFacts I.realization)
    (h13 : ClassicalInfinityGenerated 13 137 (I.realization.sphere 13 137 correction))
    (hframe6 : (∃ a : (sequence D .sphere).Page 6 (14,139),
      RepresentsOnPage (sequence D .sphere) 6 (14,139) (L.target M) a ∧
      ∀ y : (sequence D .sphere).Page 6 (14,139),y=0∨y=a) ∧
      ReachesPage (sequence D .sphere) 1000 (14,139) (L.target M)) :
    (∀ a : BiHom 125 130 (S_0_0 : Syn),VanishesModLambda 9 a ↔
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a) ∧
    (∀ a : BiHom 125 130 (S_0_0 : Syn),VanishesModLambda 10 a ↔
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) ∧
    (∃u,UChoice M D.toModelData L u) ∧
    (∀ (eta : BiHom 1 2 (S_0_0:Syn)),EtaChoice M D.toModelData eta →
      ∀theta : BiHom 62 64 (S_0_0:Syn),C4At M D.toModelData L theta →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (sphereProduct eta (sphereProduct theta theta))) ∧
    (∀ (eta : BiHom 1 2 (S_0_0:Syn)),EtaChoice M D.toModelData eta →
      ∀u : BiHom 124 134 (S_0_0:Syn),UChoice M D.toModelData L u →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 (lambdaMultiply 3 (sphereProduct eta u))) ∧
    (∀ e : ((D.family.sphere).sequence.ssData (14,139,133)).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 (14,139,133)
        (D.sphereE2 14 139 6 (L.target M)) e) ∧
    (∀ (eta : BiHom 1 2 (S_0_0:Syn)),EtaChoice M D.toModelData eta →
      ∀theta : BiHom 62 64 (S_0_0:Syn),C4At M D.toModelData L theta →
      ∀u : BiHom 124 134 (S_0_0:Syn),UChoice M D.toModelData L u →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15
        ((show BiHom 125 130 (S_0_0:Syn) from sphereProduct eta (sphereProduct theta theta))-
          (show BiHom 125 130 (S_0_0:Syn) from lambdaMultiply 3 (lambdaMultiply 3 (sphereProduct eta u))))) ∧
    (∀ a : BiHom 125 133 (S_0_0:Syn),FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (lambdaMultiply 3 a)) ∧
    (∀ (eta : BiHom 1 2 (S_0_0:Syn)),EtaChoice M D.toModelData eta →
      ∀theta : BiHom 62 64 (S_0_0:Syn),C4At M D.toModelData L theta →
      ∀u : BiHom 124 134 (S_0_0:Syn),UChoice M D.toModelData L u →
      C5At M D.toModelData L eta u →
      Detects D.sphereConvergence (14,139,130) (D.sphereE2 14 139 9 (L.target M))
        (sphereProduct eta (sphereProduct theta theta))) ∧
    (SurvivesTo (sequence D .sphere) 12 (14,139) (L.target M) →
      ∀ a : BiHom 125 130 (S_0_0:Syn),
      Detects D.sphereConvergence (14,139,130) (D.sphereE2 14 139 9 (L.target M)) a →
      ¬FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) := by
  classical
  /- BHS label agreement and the actual nu-unit map transport common infinity
  representatives to the synthetic sphere, including the zero case. -/
  /- Actual convergence gives either nonzero leading detection or membership
  in the next actual tower filtration. -/
  /- The two complete frames and the intervening finite-page gap yield the
  three branches, retaining an actual lambda preimage in the last branch. -/
  have hp := SF.t_permanent_cycle
  rw [(route_expression_labels I).2.2] at hp
  exact ⟨prop78_detection_data_bridge_lambda_9_iff_filtration_14 BHS,prop78_detection_data_bridge_lambda_10_iff_filtration_15 BHS,
    prop78_detection_data_u_choice_exists I BHS SF,prop78_detection_data_c4_eta_filtration_fourteen BHS I SF,
    prop78_detection_data_u_choice_eta_lambda_three_filtration_fourteen BHS I SF,prop78_detection_data_target_infinity_frame BHS SF hframe6 6 (by decide),
    prop78_detection_data_bridge_theta_u_eta_filtration_error I BHS SF h13,
    prop78_detection_data_bridge_lambda_three_preserves_filtration_fifteen BHS,
    prop78_detection_data_bridge_c4_c5_eta_target_detected I BHS SF h13,
    fun hs a ha=>prop78_detection_data_bridge_target_detected_not_filtration_fifteen BHS.eInfty (L.target M) hp hs a ha⟩
end
end KIP126.Main.Solution.Route

namespace KIP126.Main.Solution.Route
open KIP126.Core.SpectralSequence.FinitePageCalculus
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route KIP126.Algebra
open KIP126.LinE2 KIP126.Computation.Near126 KIP126.Computation.Route
noncomputable section
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
  {L : Labels H} {G : TmfLabels H} {η : BiHom 1 2 (S_0_0:Syn)}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem prop78_from_inputs_realization_additive {D : Model H M Syn} : D.recovery.realization.Additive := by
  classical
  letI := D.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts D.recovery.realization
  exact Functor.additive_of_preservesBinaryBiproducts _


private theorem prop78_from_inputs_realize_detector {D : Model H M Syn} {m wt : ℤ} (R : KIP126.Literature.Route.RealizationCoordinates D)
    (a : BiHom m wt (S_0_0 : Syn)) :
    KIP126.Literature.Route.realizeNu D R .sphere (a ≫ D.nu.unitIso.inv) ≫ D.auxiliary.detectorUnit =
      KIP126.Literature.Route.realizeNu D R .detector (a ≫ KIP126.Literature.Route.detectorMap D) := by
  classical
  have hn := D.recovery.nuRealizationIso.hom.naturality D.auxiliary.detectorUnit
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [KIP126.Literature.Route.realizeNu, KIP126.Literature.Route.detectorMap, ClassicalObject.obj, Functor.map_comp, Category.assoc]
  rw [← hn]


private theorem prop78_from_inputs_high125_detector_nonzero_parts {D : Model H M Syn}
    (TM : KIP126.Literature.Route.TmfInputs D G) (I : KIP126.Computation.Route.Inputs D L G)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (a : HomotopyGroup (C := C) 125 SphereSpectrum)
    (ha : TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (G.high125 M) a) : a ≫ D.auxiliary.detectorUnit ≠ 0 := by
  classical
  obtain ⟨_, b, hb, hnonzero⟩ := TM.high125_detected
  have heq : a = b := high125_detected_choice_unique I V S a b
    (by simpa only [high125_label I] using ha)
    (by simpa only [high125_label I] using hb)
  simpa only [heq] using hnonzero


private theorem prop78_from_inputs_theta_detector_zero_parts {D : Model H M Syn}
    (BHS : KIP126.Literature.Route.SyntheticInputs D)
    (RL : KIP126.Literature.Route.RealizationInput D)
    (CL : KIP126.Literature.Route.ClassicalInputs D η)
    (TM : KIP126.Literature.Route.TmfInputs D G)
    (theta : BiHom 62 64 (S_0_0 : Syn))
    (htheta : ThetaChoice M D.toModelData theta) :
    theta ≫ KIP126.Literature.Route.detectorMap D = 0 := by
  classical
  set_option backward.isDefEq.respectTransparency false in
    letI := prop78_from_inputs_realization_additive (D := D)
    let a : BiHom 62 64 (KIP126.Literature.Route.nuZero D .sphere) :=
      theta ≫ D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _
    have ha : quotientClass 1 a = KIP126.Literature.Route.firstLabel D .sphere 2 64 (Sphere.Internal.hiSquare H M 5) := by
      apply (D.firstQuotient SphereSpectrum 0 2 64).injective
      change (D.firstQuotient SphereSpectrum 0 2 64) (quotientClass 1 a) =
        (D.firstQuotient SphereSpectrum 0 2 64)
          ((D.firstQuotient SphereSpectrum 0 2 64).symm (Sphere.Internal.hiSquare H M 5))
      rw [AddEquiv.apply_symm_apply, ← htheta]
      change (D.firstQuotient SphereSpectrum 0 2 64) _ =
        (D.firstQuotient SphereSpectrum 0 2 64)
          (quotientClass 1 theta ≫ XModLambdaN.map
            (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) 1)
      apply congrArg (D.firstQuotient SphereSpectrum 0 2 64)
      simp only [a, quotientClass, Category.assoc, XModLambdaN.incl_naturality,
        D.quotientFunctoriality.map_comp]
    have hd := RL.detection.detection .sphere 2 64
      (Sphere.Internal.hiSquare H M 5) a CL.theta5_exists.1 ha
    have he : KIP126.Literature.Route.realizeNuZero D RL.coordinates .sphere a =
        KIP126.Literature.Route.realizeNu D RL.coordinates .sphere (theta ≫ D.nu.unitIso.inv) := by
      simp only [KIP126.Literature.Route.realizeNuZero, a, ClassicalObject.obj, Category.assoc, Iso.inv_hom_id_app,
        Functor.id_obj, Category.comp_id]
    rw [he] at hd
    have hz := TM.theta5_vanishes _ hd
    rw [prop78_from_inputs_realize_detector] at hz
    apply detector_realization_injective_62_64 BHS TM.low_filtration_63
    change D.recovery.realization.map (theta ≫ KIP126.Literature.Route.detectorMap D) = D.recovery.realization.map 0
    rw [Functor.map_zero]
    apply (cancel_epi (RL.coordinates.sphere 62 64).hom).mp
    apply (cancel_mono (D.recovery.nuRealizationIso.app D.auxiliary.detector).hom).mp
    dsimp only [KIP126.Literature.Route.realizeNu, ClassicalObject.obj] at hz
    erw [Limits.comp_zero, Limits.zero_comp, Category.assoc]
    exact hz




private theorem prop78_from_inputs (BHS : SyntheticInputs D) (RL : RealizationInput D)
    (CL : ClassicalInputs D η) (AF : SphereActionFiltrationCompatible D)
    (TM : TmfInputs D G) (BX : BXDistinguishedInput D η)
    (I : KIP126.Computation.Route.Inputs D L G) (V : SphereVanishingLine H)
    (S : ClassicalSphereSeparated H) :
    KIP126.Solution.Near126.OnlyD12.d12_dichotomy_and_condition_equivalence M D L η := by
  classical
  /- The synthetic tmf image used in the high-filtration contradiction.
  The product and unit are the ones bound by `A.algebra.detector`, on D's
  chosen completed tmf; no separate homotopy-ring model is selected. -/
  have eta_theta_square_detector_zero_parts {D : Model H M Syn}
      (BHS : KIP126.Literature.Route.SyntheticInputs D)
      (RL : KIP126.Literature.Route.RealizationInput D)
      (CL : KIP126.Literature.Route.ClassicalInputs D η)
      (TM : KIP126.Literature.Route.TmfInputs D G)
      (theta : BiHom 62 64 (S_0_0 : Syn))
      (htheta : ThetaChoice M D.toModelData theta) :
      sphereProduct η (sphereProduct theta theta) ≫
        KIP126.Literature.Route.detectorMap D = 0 := by
    have h := prop78_from_inputs_theta_detector_zero_parts BHS RL CL TM theta htheta
    dsimp only [sphereProduct]
    simp only [Smn] at h
    simp only [Smn, Category.assoc]
    rw [h]
    erw [Limits.comp_zero, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero]
  have detector_injective_fifteen_parts {D : Model H M Syn}
      (BHS : KIP126.Literature.Route.SyntheticInputs D)
      (RL : KIP126.Literature.Route.RealizationInput D)
      (TM : KIP126.Literature.Route.TmfInputs D G) (I : KIP126.Computation.Route.Inputs D L G)
      (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
      (a : BiHom 125 130 (S_0_0 : Syn))
      (ha : KIP126.Synthetic.SpectralSequence.FiltrationAtLeast
        (nuCoefficientUnit H.unit D.nu) 15 a)
      (hz : a ≫ KIP126.Literature.Route.detectorMap D = 0) : a = 0 := by
    set_option backward.isDefEq.respectTransparency false in
      letI := prop78_from_inputs_realization_additive (D := D)
      by_contra hne
      have hd := high125_weight130_nonzero_classical_detection I BHS RL V
        TM.high125_detected.1 a ha hne
      have hn := prop78_from_inputs_high125_detector_nonzero_parts TM I V S
        (KIP126.Literature.Route.realizeNu D RL.coordinates .sphere
          (a ≫ D.nu.unitIso.inv)) hd
      apply hn
      rw [prop78_from_inputs_realize_detector, hz]
      simp only [KIP126.Literature.Route.realizeNu, Functor.map_zero,
        Limits.comp_zero, Limits.zero_comp]
  have non_c4_branch_eta_filtration_fifteen {D : Model H M Syn}
      (I : KIP126.Computation.Route.Inputs D L G) (SF : Derived.SphereFacts I.realization)
      (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toModelData η)
      (θ : BiHom 62 64 (S_0_0 : Syn))
      (hbranch : SphereDetected D 13 137 9 (I.realization.sphere 13 137 correction)
          (sphereProduct θ θ) ∨
        ∃ a : BiHom 124 138 (S_0_0 : Syn), lambdaMultiply 10 a=sphereProduct θ θ) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 (sphereProduct η (sphereProduct θ θ)) := by
    have hη0 : lambdaMultiply 0 η=η := by
      have hc := D.shiftCoherence.right_unit (1,2) (S_0_0 : Syn)
      have he : (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn)=
          SyntheticCategory.biShift_zero.hom.app (Smn 1 2 : Syn) := by
        change (biShiftAddIso (1,2) (0,0) (1,2) (by decide)).hom.app _=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
          eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      dsimp only [lambdaMultiply,lambdaPow]
      simp only [Nat.cast_zero,neg_zero,sub_zero,eqToHom_refl,Category.id_comp]
      rw [←he]
      change (SyntheticCategory.biShift_comp (1,2) (0,0)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift_comp (1,2) (0,0)).hom.app (S_0_0 : Syn) ≫ η=η
      rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    have hηd := D.comparisonCompatible.homotopy_lambda 1 2 0 η
    rw [hη0,hη] at hηd
    rcases hbranch with h13 | ⟨a,ha⟩
    · have hp : Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137)
          (Sphere.Internal.hi H M 1) (I.realization.sphere 13 137 correction)=0 := by
        have h := I.products ⟨1,2,13,137⟩ (by simp [Raw.products]) dataH1 correction
        dsimp only at h
        rw [I.labels.h1] at h
        exact h.symm.trans SF.h1_correction_zero
      have hd := D.multiplicationCompatible 1 2 13 137 0 9
        (Sphere.Internal.hi H M 1) (I.realization.sphere 13 137 correction)
        η (sphereProduct θ θ) hηd h13.1
      change Detects D.sphereConvergence (14,139,130)
        (D.sphereE2 14 139 9 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137)
          (Sphere.Internal.hi H M 1) (I.realization.sphere 13 137 correction)))
        (sphereProduct η (sphereProduct θ θ)) at hd
      rw [hp,map_zero] at hd
      exact detects_zero_filtration D.sphereConvergence (14,139,130) hd
    · have had := D.comparisonCompatible.homotopy_lambda 14 138 10 a
      rw [ha] at had
      have hd := D.multiplicationCompatible 1 2 14 138 0 10
        (Sphere.Internal.hi H M 1) (D.sphereFirstQuotient 14 138 (quotientClass 1 a))
        η (sphereProduct θ θ) hηd had
      change Detects D.sphereConvergence (15,140,130) _ (sphereProduct η (sphereProduct θ θ)) at hd
      obtain ⟨e,he,a',ha',hgr⟩ := hd
      rw [←ha']
      have hm : ((towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)).F 15 (125,130)).arrow a'∈
          (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : Syn) (125,130)))
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)).F 15 (125,130)) := ⟨a',rfl⟩
      simpa only [FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply,SyntheticObject.obj,Int.reduceAdd,Int.reduceSub] using hm
  have theta_detection_step {D : Model H M Syn}
      (i : Tridegree) (x : (D.family.sphere).E₂ i)
      (hframe : ∀ e : ((D.family.sphere).sequence.ssData i).eInfty,
        e=0 ∨ HasInfinityRepresentative D.family.sphere 2 i x e)
      (a : BiHom (i.2.1-i.1) i.2.2 (S_0_0 : Syn))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) i.1 a) :
      DetectsNonzero D.sphereConvergence i x a ∨
        FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (i.1+1) a := by
    let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)
    have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0:Syn) (i.2.1-i.1,i.2.2)))
        (F.F i.1 (i.2.1-i.1,i.2.2)) := by
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
    obtain ⟨a',ha'⟩ := ham
    let q := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
    let e := (D.sphereConvergence.identification i).inv q
    have he : (D.sphereConvergence.identification i).hom e=q :=
      ConcreteCategory.congr_hom (D.sphereConvergence.identification i).inv_hom_id q
    by_cases he0 : e=0
    · right
      have hq : F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'=0 := by
        rw [he0,map_zero] at he
        exact he.symm
      have hmem := (subobject_cokernel_π_eq_zero_iff
        (F.F (i.1+1) (i.2.1-i.1,i.2.2)) (F.F i.1 (i.2.1-i.1,i.2.2))
        (F.mono i.1 (i.2.1-i.1,i.2.2)) a').mp hq
      rw [ha'] at hmem
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hmem
    · left
      have hr := (hframe e).resolve_left he0
      exact ⟨⟨e,hr,a',ha',he⟩,e,hr,he0⟩
  /- The two complete frames and the intervening finite-page gap yield the
  three branches, retaining an actual lambda preimage in the last branch. -/
  intro hη
  let SF := sphere_facts I V
  obtain ⟨h13,hcases⟩ := prop78_theta_data I BHS V
  obtain ⟨hc3,hdnp,hbx,hframe6⟩ := prop78_classical_data I SF
  obtain ⟨h9,h10,huex,h4f14,huf14,hframe,herr,hlambda,hdetect,hnonzero⟩ :=
    prop78_detection_data I BHS SF h13 hframe6
  obtain ⟨theta,htheta,hboundary,hcriterion⟩ := BX
  let a : BiHom 125 130 (S_0_0:Syn) := sphereProduct η (sphereProduct theta theta)
  have permanent_of_f15 (hf : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) :
      PermanentH6Square M := by
    have hz : a=0 := detector_injective_fifteen_parts BHS RL TM I V S _ hf
      (eta_theta_square_detector_zero_parts BHS RL CL TM theta htheta.2.1)
    apply hcriterion.mpr
    change lambdaAction 125 130 S_0_0 a=0
    rw [hz]
    simp only [lambdaAction,CategoryTheory.Limits.comp_zero]
  have dichotomy : (PermanentH6Square M ∧ ¬D12 M L) ∨
      (D12 M L ∧ ¬PermanentH6Square M) := by
    have hf14 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 a := by
      rcases hcases theta with h4|hbranch
      · exact h4f14 η hη theta h4
      · exact towerFiltrationSubmodule_antitone (nuCoefficientUnit H.unit D.nu) (S_0_0:Syn)
          (125,130) (by decide : (14:ℤ)≤15)
          (non_c4_branch_eta_filtration_fifteen I SF η hη theta hbranch)
    by_cases hf15 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a
    · have hp := permanent_of_f15 hf15
      exact Or.inl ⟨hp,fun hd=>(hdnp hd).1 hp⟩
    · have hd := hbx η theta htheta ((h9 a).mpr hf14) (fun h=>hf15 ((h10 a).mp h))
      exact Or.inr ⟨hd,(hdnp hd).1⟩
  refine ⟨dichotomy,?_,?_⟩
  · intro hd
    have impossible (hf : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) : False :=
      (hdnp hd).1 (permanent_of_f15 hf)
    have h4 : C4At M D.toModelData L theta := by
      rcases hcases theta with h4|hbranch
      · exact h4
      · exact False.elim (impossible
          (non_c4_branch_eta_filtration_fifteen I SF η hη theta hbranch))
    refine ⟨(hdnp hd).2,⟨theta,htheta.2.1,h4⟩,?_⟩
    obtain ⟨u,hu⟩ := huex
    let c : BiHom 125 133 (S_0_0:Syn) := lambdaMultiply 3 (sphereProduct η u)
    have hc14 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 14 c := huf14 η hη u hu
    rcases theta_detection_step (14,139,133) (D.sphereE2 14 139 6 (L.target M))
        hframe c hc14 with hdet|hc15
    · exact ⟨u,hu,hdet.1⟩
    · exfalso
      apply impossible
      have he := herr η hη theta h4 u hu
      have hl := hlambda c hc15
      change (show BiHom 125 130 (S_0_0:Syn) from a)-
        (show BiHom 125 130 (S_0_0:Syn) from lambdaMultiply 3 c) ∈
        towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu) (S_0_0:Syn) 15 (125,130) at he
      have hh := (towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu)
        (S_0_0:Syn) 15 (125,130)).add_mem he hl
      simpa only [sub_add_cancel,FiltrationAtLeast,Int.reduceAdd] using hh
  · rintro ⟨hc,⟨theta',htheta',h4'⟩,u,hu,h5⟩
    have h4 := prop78_choice_invariance I BHS RL CL AF theta theta' htheta.2.1 htheta' h4'
    have hn := hnonzero (hc3.mp hc) _ (hdetect η hη theta h4 u hu h5)
    exact hbx η theta htheta ((h9 a).mpr (h4f14 η hη theta h4))
      (fun h=>hn ((h10 a).mp h))

end
end KIP126.Main.Solution.Route


namespace KIP126.Main.Solution.Route
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Classical.Adams KIP126.Kervaire.Route
open KIP126.Synthetic.Context
open KIP126.Main.StageInput

/-- The existing Cnu calculation instantiated at the fixed C(M). -/
theorem cnu_d3 :
    KIP126.Computation.Route.Derived.CnuDifferential routeComputation.realization := by
  exact KIP126.Computation.Route.cnu_d3 routeComputation

/-- One-step λ injectivity with A and C from the SAME stage witness. -/
theorem lambda_injective_125_130 :
    LambdaInjectiveAt 125 130 (S_0_0 : KIP126.Def.standardRouteInput.Syn) := by
  exact KIP126.Computation.Route.lambda_injective_125_130 routeLiterature routeComputation

/-- The derived Section 7 finite/infinite facts use the delivered vanishing
line on this same model, rather than an unowned tail assumption. -/
theorem sphere_facts :
    KIP126.Computation.Route.Derived.SphereFacts routeComputation.realization := by
  exact KIP126.Computation.Route.sphere_facts routeComputation sphereVanishing

/-- The precise F15 detector injectivity used at all three occurrences
of the tmf argument in Proposition 7.8. -/
theorem detector_injective : DetectorInjectiveAt routeModel 125 130 15 := by
  exact KIP126.Computation.Route.detector_injective_125_130_filtration15
    routeLiterature routeComputation sphereVanishing sphereSeparated

/-- The Section 7 contradiction now consumes the selected Cnu target and
its incoming-page exclusion through the explicit same-witness chain. -/
theorem proposition_7_9 :
    KIP126.Solution.Near126.C3NotC5.c3_excludes_c5
      standardMilnorCooperations routeModel routeLabels routeEta := by
  intro _
  exact Section7.c3_excludes_c5

/-- Proposition 7.8 from this complete delivered input. The body must use
its A/C fields and prove the finite-page/tail/filtration steps in Main. -/
theorem proposition_7_8 (input : KIP126.Challenge2) :
    KIP126.Solution.Near126.OnlyD12.d12_dichotomy_and_condition_equivalence
      standardMilnorCooperations standardRouteModel input.computation.bindings.routeLabels
      KIP126.Def.standardRouteEta := by
  let lit := input.literature
  let B := lit.bindings.route
  let st := lit.results.route
    (KIP126.Main.Solution.Literature.route_moss lit)
    (KIP126.Main.Solution.Literature.eInfty_shift_natural lit)
  let BHS : KIP126.Literature.Route.SyntheticInputs standardRouteModel := st.synthetic.toInputs _ B.bhsCompletion
    B.completionApplicability B.completionComparison
    (KIP126.Interface.Solution.Literature.Route.realizationKernel_of_source _
      B.kernelSource st.realizationKernel B.kernelBinding)
  let RL : KIP126.Literature.Route.RealizationInput standardRouteModel := ⟨B.realization,
    KIP126.Interface.Solution.Literature.Route.realization_detection_of_completed_sources _
      B.realization B.bhsCompletion st.realization B.completionApplicability
      B.completionComparison B.realizationComparison⟩
  let CL := KIP126.Literature.Route.classicalInputsOfSource standardRouteModel KIP126.Def.standardRouteEta
    B.classicalSource st.classical B.classicalBinding B.synthetic_eta
  let TM := KIP126.Main.Solution.Computation.tmf_inputs_of_computation standardRouteModel
    input.computation.route lit.results.sphereVanishing KIP126.Def.standardSphereSeparated
    B.tmfSource st.tmf B.tmfBinding B.algebraBinding.classical_detection
  exact prop78_from_inputs BHS RL CL B.algebraBinding.action_filtration TM st.bx input.computation.route
    lit.results.sphereVanishing KIP126.Def.standardSphereSeparated

end KIP126.Main.Solution.Route
