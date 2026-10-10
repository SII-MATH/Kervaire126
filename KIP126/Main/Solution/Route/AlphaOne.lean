import KIP126.LinProgram.Model.BasisTable.FiniteCertificates
import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
import KIP126.Interface.Challenge.Computation.Delivery
import Batteries.Data.String.Lemmas
import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs
import Mathlib.CategoryTheory.Triangulated.Functor
import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
import KIP126.Def.Synthetic.Context.LambdaPowers.Proofs
import KIP126.Main.Solution.StageInput
import KIP126.Main.Solution.Computation.Lambda
import KIP126.Def.Kervaire.Route.Section7.AlphaOne
import KIP126.Def.Synthetic.Context.Coherence.Proofs
import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs
import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
import KIP126.Def.SpectralSequence.Computation.Proofs
import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs
import KIP126.Def.ClassicalAdams.PageRepresentatives.Order.Proofs
import KIP126.Def.Algebra.NestedQuotient.Proofs
import KIP126.Def.Synthetic.Detection.Proofs
import KIP126.Def.SpectralSequence.Permanence.Proofs
import KIP126.Def.SpectralSequence.Basic.Category.Proofs

/-! Main deductions in Proposition 7.8 and Lemma `lem:x_123_9`.
All source results, complete bases, products and staircase data are the
ones delivered by the sole correlated Challenge2 witness. These are proof
obligations, not added fields of M, A or C. -/
namespace KIP126.Main.Solution.Route.Section7
open KIP126.Core.SpectralSequence.FinitePageCalculus
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route KIP126.Main.StageInput
noncomputable section

section
open CategoryTheory.Limits KIP126.Core.Algebra KIP126.Computation.Route
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart
  adamsTowerSSData adamsTowerInternalD

variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
  {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
  {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}

/-- The low-filtration stem124 staircase, reconstructed from the complete
bases and differential records of the same computation input. The d2, d3
and d5 kernels are computed on their actual pages, including all incoming
boundaries needed to keep the differential targets nonzero. -/
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
  have hc5n : c5 ≠ 0 := represents_next_nonzero_of_incoming_zero_at
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
  have hy4ne := represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤3; omega)
    (by decide : (2:ℤ)≤3) hin3 hy4 hy3 (target3 y3 hy3)
  have hin4 : E.d 4 ((11,134)-E.diffDeg 4) = 0 := h74
  have hy5ne := represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤4; omega)
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
  obtain ⟨b,hb,hcases,h74⟩ := stem124_finite_pages_low124_s7_four I
  have h8 := stem124_finite_pages_low124_af8_three I
  have h9 := stem124_finite_pages_low124_af9_four I
  have h8four := adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 3 4 8 132
    (by omega) (by omega) h8
  exact ⟨stem124_finite_pages_low124_af6_six I h74, stem124_finite_pages_low124_s7_six I h8four h9.2.1, h8, h9.1⟩
end

section
open CategoryTheory.Limits KIP126.Classical.Adams.PageRepresentatives KIP126.Computation.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  {D : Model H M Syn} {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
/-- In weight128 the remaining classical incoming sources are in the vanishing
half-plane. Thus classical low-filtration E∞ vanishing also kills the full
synthetic associated grades, including possible finite-boundary quotients. -/
private theorem nu124_low_zero_permanent_quotient_zero_of_stable_boundaries
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



private theorem nu124_low_zero
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
    haveI := nu124_low_zero_permanent_quotient_zero_of_stable_boundaries SphereSpectrum (s,124+s)
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
    haveI := nu124_low_zero A I s hs10 hz
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
end

section
open CategoryTheory.Limits KIP126.Core.Algebra KIP126.Computation.Route
open KIP126.LinE2 KIP126.Computation.Near126
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart
  adamsTowerSSData adamsTowerInternalD

/-- Exhaustion of the four AF13 basis directions by actual page representatives.
The nonzero outgoing d3 and correction's nonzero infinite representative use
`sphere_facts` on this same input. The two incoming equations then remove
all other kernel directions, including every linear combination. -/
private theorem stem124_af13_exhaustion_af13_labels
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H} (I : KIP126.Computation.Route.Inputs D L G) :
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
/-- Full AF10 exhaustion from the complete five-element E2 basis. The d5
 target remains nonzero after all possible d2, d3 and d4 incoming maps are
 computed. Incoming boundaries and that nonzero d5 leave precisely U.
 U's nonzero infinite representative follows from its certified page-1000
 survival and the same vanishing line; the calculation proves full exhaustion. -/
private theorem stem124_af10_exhaustion
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H} (I : KIP126.Computation.Route.Inputs D L G) (V : SphereVanishingLine H) :
    KIP126.Kervaire.Route.Section7.ClassicalInfinityGenerated 10 134
      (I.realization.sphere 10 134 U) := by
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
    have hn3 : b ≠ 0 := represents_next_nonzero_of_incoming_zero_at
      (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) (by exact d2_13) hb (hrep2 x) hx
    exact represents_next_nonzero_of_incoming_zero_at
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

end

section
open CategoryTheory.Limits KIP126.Computation.Route KIP126.Algebra
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}

/-- Stabilized incoming boundaries identify the BHS permanent quotient with
the same complete classical infinity frame. -/
private theorem theta_quotient_frame
    (I : KIP126.Computation.Route.Inputs D L G) (s t : ℤ) (k : ℕ) (hst : t=s+124) (hsk : s-(k+2)≤4)
    (x : E2 H SphereSpectrum s t) (hx : ClassicalInfinityGenerated s t x) :
    ∃ x' : PageRepresentatives.permanentCycles H SphereSpectrum (s,t), x'.val=x ∧
      ∀ q : PageRepresentatives.PermanentQuotient H SphereSpectrum (1+(k:ℤ)) (s,t),
        q=0 ∨ q=NestedQuotient.projection _ _ x' := by
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

/-- BHS label agreement and the actual nu-unit map transport common infinity
representatives to the synthetic sphere, including the zero case. -/
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

/-- Actual convergence gives either nonzero leading detection or membership
in the next actual tower filtration. -/
private theorem theta_detection_step
    (i : Tridegree) (x : (D.family.sphere).E₂ i)
    (hframe : ∀ e : ((D.family.sphere).sequence.ssData i).eInfty,
      e=0 ∨ HasInfinityRepresentative D.family.sphere 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) i.1 a) :
    DetectsNonzero D.sphereConvergence i x a ∨
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (i.1+1) a := by
  classical
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)

  have ham : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0:Syn) (i.2.1-i.1,i.2.2)))
      (F.F i.1 (i.2.1-i.1,i.2.2)) := by
    classical
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
/-- The two complete frames and the intervening finite-page gap yield the
three branches, retaining an actual lambda preimage in the last branch. -/
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


open CategoryTheory.Limits KIP126.Algebra in
/-- On the last possible outgoing page of a finite quotient, a classical
nonzero differential remains nonzero. A zero target would give a common
infinite-cycle representative and hence a classical cycle one page later. -/
private theorem finite_last_nonzero_last_cycle_infinity_lift
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree)
    (r : ℤ) (hr : E.r₀ ≤ r) (p : Tridegree)
    (z : (Subobject.underlying.obj ((E.ssData p).Z ↑(r-E.r₀).toNat) : ModuleCat.{v} ℤ))
    (hz : E.d r p ((E.ssData p).pageπ ↑(r-E.r₀).toNat z) = 0)
    (hout : ∀ j : ℤ, r+1 ≤ j → E.d j p = 0) :
    ∃ zi : (Subobject.underlying.obj ((E.ssData p).Z ⊤) : ModuleCat.{v} ℤ),
      (Subobject.ofLE _ _ ((E.ssData p).Z_anti le_top)) zi = z := by
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
  have hn1 : (r+1-E.r₀).toNat=n+1 := by dsimp only [n]; omega
  have hZ : D.Z ⊤ = D.Z ↑(n+1) := by
    have hh := cycles_top_eq_of_d_eq_zero E (r+1) (by omega) p hout
    simpa only [hn1] using hh
  let zi := (Subobject.ofLE (D.Z ↑(n+1)) (D.Z ⊤) hZ.ge) zn
  refine ⟨zi,?_⟩
  dsimp only [zi]
  rw [←CategoryTheory.comp_apply,Subobject.ofLE_comp_ofLE]
  exact hnz



private theorem finite_last_nonzero_normalized_last_cycle_infinity
    (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree)
    (x : A.E₂ i) (xr : A.Page r i)
    (hx : KIP126.Synthetic.SpectralSequence.RepresentsOnPage A r i x xr)
    (hd : A.d r i xr = 0)
    (hout : ∀ j : ℤ, r+1 ≤ j → A.d j i = 0) :
    ∃ e, HasInfinityRepresentative A 2 i x e := by
  classical
  rcases A with ⟨⟨⟨r₀,S,deg,d⟩,dd,Zs,Bs⟩,hf,hdeg⟩
  dsimp only at hf
  subst r₀
  have hdg : deg=syntheticAdamsRawShift := funext hdeg
  subst deg
  let E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree :=
    ⟨⟨2,S,syntheticAdamsRawShift,d⟩,dd,Zs,Bs⟩
  obtain ⟨hr,z,hz,hzr⟩ := hx
  simp only [SyntheticAdamsSS.d,eqToHom_refl,Category.id_comp,Category.comp_id] at hd hout
  have hz0 : E.d r i ((E.ssData i).pageπ ↑(r-2).toNat z) = 0 := by
    rw [hzr]
    exact hd
  have ho : ∀ j : ℤ, r+1≤j → E.d j i=0 := hout
  obtain ⟨zi,hzi⟩ := finite_last_nonzero_last_cycle_infinity_lift E r hr i z hz0 ho
  refine ⟨(S i).pageπ ⊤ zi,by norm_num,zi,?_,rfl⟩
  change ((Subobject.ofLE _ _ ((S i).Z_anti le_top)) ≫ (S i).pageπ 0) zi=x
  rw [←hz,←hzi]
  rw [←CategoryTheory.comp_apply]
  dsimp only [E]
  rw [Subobject.ofLE_comp_ofLE_assoc]
  rfl


private theorem finite_last_nonzero_finite_quotient_rep_naturality {D : Model H M Syn}
    {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree)
    (x : (D.family.obj X).E₂ i) (xr : (D.family.obj X).Page r i)
    (hx : KIP126.Synthetic.SpectralSequence.RepresentsOnPage (D.family.obj X) r i x xr) :
    KIP126.Synthetic.SpectralSequence.RepresentsOnPage (D.family.obj Y) r i
      (familyPageMap D.family f 2 i x) (familyPageMap D.family f r i xr) := by
  classical
  have family_map_data {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
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

  obtain ⟨hr,z,hz,he⟩ := hx
  let F := (D.family.functor.map f).toSSDataMorphism
  let n : WithTop ℕ := ↑(r-2).toNat
  change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z n)
    (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=x at hz
  refine ⟨hr,F.cycleMap i n z,?_,?_⟩
  · rw [family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤n from bot_le)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · rw [family_map_data]
    exact (congrArg (fun a => a z) (F.pageπ_pageMap i n)).symm.trans
      (congrArg (fun q => F.pageMap i n q) he)



private theorem finite_last_nonzero_finite_quotient_d_naturality {D : Model H M Syn}
    {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ (D.family.obj Y).d r i =
      (D.family.obj X).d r i ≫ familyPageMap D.family f r (syntheticAdamsRawTarget r i) := by
  classical
  have h := (D.family.functor.map f).pageMap_comm_d r i
  dsimp only [familyPageMap,SyntheticAdamsSS.d,SyntheticAdamsFamily.obj]
  simp only [Category.assoc,eqToHom_trans_assoc,eqToHom_refl,Category.id_comp]
  erw [←Category.assoc (SpectralSequenceMorphism.pageMap (D.family.functor.map f) r i)
    ((D.family.functor.obj Y).d r i), h]
  simp only [Category.assoc,eqToHom_trans_assoc]
  have hi : i+(D.family.functor.obj X).diffDeg r=syntheticAdamsRawTarget r i := by
    simp only [D.family.differentialDegree,syntheticAdamsRawTarget]
  erw [←eqToHom_naturality_assoc (fun j => (D.family.functor.map f).pageMap r j) hi]
  simp only [eqToHom_trans]




private theorem finite_last_nonzero_quotient_family_map_data {D : Model H M Syn} {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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



private theorem finite_last_nonzero_quotient_family_map_comp {D : Model H M Syn} {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : ℤ) (i : Tridegree) :
    familyPageMap D.family (f ≫ g) r i =
      familyPageMap D.family f r i ≫ familyPageMap D.family g r i := by
  classical
  rw [finite_last_nonzero_quotient_family_map_data,finite_last_nonzero_quotient_family_map_data,finite_last_nonzero_quotient_family_map_data]
  rw [D.family.functor.map_comp]
  exact SSDataMorphism.pageMap_comp (D.family.functor.map f).toSSDataMorphism
    (D.family.functor.map g).toSSDataMorphism i _



private theorem finite_last_nonzero_quotient_hasDifferential_map {D : Model H M Syn} {X Y : Syn} (f : X ⟶ Y)
    (r : ℤ) (i j : Tridegree)
    (x : (D.family.obj X).E₂ i) (y : (D.family.obj X).E₂ j)
    (h : KIP126.Synthetic.SpectralSequence.HasDifferential (D.family.obj X) r i j x y) :
    KIP126.Synthetic.SpectralSequence.HasDifferential (D.family.obj Y) r i j
      (familyPageMap D.family f 2 i x) (familyPageMap D.family f 2 j y) := by
  classical
  obtain ⟨hdeg,xr,yr,hx,hy,hd⟩ := h
  refine ⟨hdeg,familyPageMap D.family f r i xr,familyPageMap D.family f r j yr,
    finite_last_nonzero_finite_quotient_rep_naturality f r i x xr hx,
    finite_last_nonzero_finite_quotient_rep_naturality f r j y yr hy,?_⟩
  have heq : familyPageMap D.family f r i ≫ (D.family.obj Y).d r i ≫
      eqToHom (congrArg ((D.family.obj Y).Page r) hdeg) =
      ((D.family.obj X).d r i ≫ eqToHom (congrArg ((D.family.obj X).Page r) hdeg)) ≫
        familyPageMap D.family f r j := by
    rw [←Category.assoc,finite_last_nonzero_finite_quotient_d_naturality,Category.assoc]
    subst j
    simp
  have hz := congrArg (fun a => a xr) heq
  simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply,hd] using hz



private theorem finite_last_nonzero_classical_to_finite_equation {D : Model H M Syn}
    (BHS : KIP126.Literature.Route.SyntheticInputs D)
    (q r k : ℕ) (hr : 2≤r) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum (s+r) (t+r-1))
    (h : KIP126.Core.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r
      (s,t) (s+r,t+r-1) x y) :
    KIP126.Synthetic.SpectralSequence.HasDifferential
      (D.family.quotient (S_0_0 : Syn) q) r
      (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ))
      (D.quotientLabel q s t k x)
      (D.quotientLabel q (s+r) (t+r-1) (k+(r-1)) y) := by
  classical
  let f : (SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj SphereSpectrum) ⟶
      (S_0_0 : Syn) :=
    SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom
  let nx : (D.family.obj ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj SphereSpectrum))).E₂ (s,t,t-k) := by
    simpa only [ClassicalObject.obj,add_zero] using D.nuE2 .sphere 0 s t k x
  let ny : (D.family.obj ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj SphereSpectrum))).E₂
      (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ)) := by
    simpa only [ClassicalObject.obj,add_zero] using D.nuE2 .sphere 0 (s+r) (t+r-1) (k+(r-1)) y
  have hnx : familyPageMap D.family f 2 (s,t,t-k) nx = D.sphereE2 s t k x := by
    convert D.comparisonCompatible.sphere_nu s t k x using 1 <;> simp [nx,f,ClassicalObject.obj] <;> rfl
  have hny : familyPageMap D.family f 2 (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ)) ny =
      D.sphereE2 (s+r) (t+r-1) (k+(r-1)) y := by
    convert D.comparisonCompatible.sphere_nu (s+r) (t+r-1) (k+(r-1)) y using 1 <;> simp [ny,f,ClassicalObject.obj] <;> rfl
  have hs := (BHS.differentials .sphere 0 s t r k hr x y).mp h
  have hx : familyPageMap D.family (f ≫ XModLambdaN.incl S_0_0 q) 2 (s,t,t-k)
      nx = D.quotientLabel q s t k x := by
    rw [finite_last_nonzero_quotient_family_map_comp]
    change familyPageMap D.family (XModLambdaN.incl S_0_0 q) 2 (s,t,t-k)
      (familyPageMap D.family f 2 (s,t,t-k) nx) = _
    rw [hnx]
    rfl
  have hy : familyPageMap D.family (f ≫ XModLambdaN.incl S_0_0 q) 2
      (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ))
      ny =
      D.quotientLabel q (s+r) (t+r-1) (k+(r-1)) y := by
    rw [finite_last_nonzero_quotient_family_map_comp]
    change familyPageMap D.family (XModLambdaN.incl S_0_0 q) 2 _
      (familyPageMap D.family f 2 _ ny) = _
    rw [hny]
    rfl
  have hs' : KIP126.Synthetic.SpectralSequence.HasDifferential
      (D.family.obj ((SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj SphereSpectrum))) r
      (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ))
      nx
      ny := by
    convert hs using 1 <;> simp [nx,ny,ClassicalObject.obj]
  have ht := finite_last_nonzero_quotient_hasDifferential_map (f ≫ XModLambdaN.incl S_0_0 q) r
    (s,t,t-k) (s+r,t+r-1,(t+r-1)-(k+(r-1):ℕ)) _ _ hs'
  rw [hx,hy] at ht
  exact ht



private theorem finite_last_nonzero_family_map_data {D : Model H M Syn} {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
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


private theorem finite_last_nonzero_family_page_comp {D : Model H M Syn} {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
  classical
  rw [finite_last_nonzero_family_map_data,finite_last_nonzero_family_map_data,finite_last_nonzero_family_map_data,Functor.map_comp]
  exact (SSDataMorphism.pageMap_comp _ _ _ _).symm


private theorem finite_last_nonzero_family_infinity_representative_map {D : Model H M Syn}
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
  · rw [finite_last_nonzero_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])



private theorem finite_last_nonzero_quotient_nu_infinity_cycles {D : Model H M Syn}
    (BHS : EInftyInput D) (q k : ℕ) (hk : k < q) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (e : ((D.family.nuQuotient D.nu SphereSpectrum q).sequence.ssData (s,t,t-k)).eInfty)
    (hx : HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum q) 2 (s,t,t-k)
      (finiteTargetLabel D .sphere q s t k x) e) :
    x ∈ PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-k) (s,t) := by
  classical
  let P := BHS.presentation
  let Zq := PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t)
  let Z1 := PageRepresentatives.cycles H SphereSpectrum ((k+1:ℕ)-t+(t-k)) (s,t)
  let Bk := PageRepresentatives.boundaries H SphereSpectrum (1+t-(t-k)) (s,t)
  have hq : 0 < q := by omega
  have hsurj : Function.Surjective (NestedQuotient.projection Zq Bk) := by rintro ⟨a⟩; exact ⟨a,rfl⟩
  obtain ⟨x',hx'⟩ := hsurj (P.finiteWindow SphereSpectrum q hq (s,t) (t-k) (by constructor <;> omega) e)
  have hrep' : HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum q) 2 (s,t,t-k)
      (finiteTargetLabel D .sphere q s t k x'.val) e :=
    (BHS.labels.1 .sphere q hq (s,t) k hk x' e).mpr hx'.symm
  let rho := (D.quotientTower (D.nu.functor.obj SphereSpectrum)).rho (k+1) q (by omega)
  let ek := ((D.family.functor.map rho).eInftyMap (s,t,t-k)) e
  have restrict (y : E2 H SphereSpectrum s t)
      (hy : HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum q) 2 (s,t,t-k)
        (finiteTargetLabel D .sphere q s t k y) e) :
      HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum (k+1)) 2 (s,t,t-k)
        (finiteTargetLabel D .sphere (k+1) s t k y) ek := by
    have hh := finite_last_nonzero_family_infinity_representative_map rho (s,t,t-k) _ _ hy
    have hlabel : familyPageMap D.family rho 2 (s,t,t-k) (finiteTargetLabel D .sphere q s t k y)=
        finiteTargetLabel D .sphere (k+1) s t k y := by
      change familyPageMap D.family rho 2 (s,t,t-k)
        (familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (targetNuLabel D .sphere s t k y)) =
        familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) (k+1)) 2 (s,t,t-k)
          (targetNuLabel D .sphere s t k y)
      rw [←CategoryTheory.comp_apply,finite_last_nonzero_family_page_comp]
      dsimp only [rho]
      rw [FiniteLambdaQuotientTower.rho_quotient]
    exact hlabel ▸ hh
  have hz1 : Z1 = ⊤ := by
    dsimp only [Z1]
    have hindex : ((k+1:ℕ):ℤ)-t+(t-k)=1 := by omega
    rw [hindex,PageRepresentatives.cycles_one]
  let y : Z1 := ⟨x,by rw [hz1]; trivial⟩
  let y' : Z1 := ⟨x'.val,by rw [hz1]; trivial⟩
  have hy := (BHS.labels.1 .sphere (k+1) (by omega) (s,t) k (by omega) y ek).mp (restrict x hx)
  have hy' := (BHS.labels.1 .sphere (k+1) (by omega) (s,t) k (by omega) y' ek).mp (restrict x'.val hrep')
  have heq : NestedQuotient.projection Z1 Bk y=NestedQuotient.projection Z1 Bk y' := hy.symm.trans hy'
  have hd : x-x'.val ∈ Bk := by
    apply (NestedQuotient.projection_eq_zero (y-y')).mp
    rw [map_sub,heq,sub_self]
  have hz : x-x'.val ∈ Zq := PageRepresentatives.boundaries_le_cycles H SphereSpectrum (s,t) _ _ hd
  have hh := Zq.add_mem hz x'.property
  have hindex : (q:ℤ)-t+(t-k)=(q:ℤ)-k := by omega
  simpa only [sub_add_cancel,Zq,hindex] using hh


private theorem finite_last_nonzero_sphere_quotient_label_to_nu {D : Model H M Syn} (q k : ℕ) (s t : ℤ)
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
        ConcreteCategory.congr_hom (finite_last_nonzero_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have hlabel : familyPageMap D.family f 2 (s,t,t-k) (D.quotientLabel q s t k x)=
      finiteTargetLabel D .sphere q s t k x := by
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D.nu.unitIso.inv q)
          2 (s,t,t-k) (D.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (finite_last_nonzero_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)) (D.sphereE2 s t k x)
      _ = familyPageMap D.family (D.nu.unitIso.inv ≫ XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q)
          2 (s,t,t-k) (D.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
      _ = familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)) :=
        (ConcreteCategory.congr_hom (finite_last_nonzero_family_page_comp (D:=D) D.nu.unitIso.inv (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D.sphereE2 s t k x)).symm
      _ = finiteTargetLabel D .sphere q s t k x := congrArg
        (fun y => familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
  exact hlabel


private theorem finite_last_nonzero_nonzero_differential_not_cycle
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum (s+r) (t+r-1))
    (h : KIP126.Core.SpectralSequence.HasNonzeroDifferential
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r
      (s,t) (s+r,t+r-1) x y) :
    x ∉ PageRepresentatives.cycles H SphereSpectrum r (s,t) := by
  classical
  intro hx
  have hc : PageRepresentatives.IsCycle H SphereSpectrum ((r:ℤ)+1-1) (s,t) x := by
    refine ⟨by omega, ?_⟩
    simpa only [add_sub_cancel_right] using hx
  obtain ⟨xnext,hnext⟩ := (PageRepresentatives.isCycle_iff_represents H SphereSpectrum
    ((r:ℤ)+1) (by omega) (s,t) x).mp hc
  obtain ⟨hdeg,xr,yr,hxr,hyr,hd,hn⟩ := h
  have hz := represents_d_zero_of_later (by change (2:ℤ)≤r; omega)
    (by omega : (r:ℤ)<(r:ℤ)+1) hxr ⟨xnext,hnext⟩
  apply hn
  rw [←hd]
  change (eqToHom (congrArg ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r) hdeg))
    ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d r (s,t) xr) = 0
  rw [hz,map_zero]


private theorem finite_last_nonzero
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    (BHS : KIP126.Literature.Route.SyntheticInputs D)
    (q r k : ℕ) (hr : 2≤r) (hqr : q=k+r) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum (s+r) (t+r-1))
    (h : KIP126.Core.SpectralSequence.HasNonzeroDifferential
      (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r
      (s,t) (s+r,t+r-1) x y) :
    FiniteNonzeroDifferential D q r s t (s+r) (t+r-1) k (k+(r-1)) x y := by
  classical
  let A := D.family.quotient (S_0_0 : Syn) q
  let N := D.family.nuQuotient D.nu SphereSpectrum q
  let f := XModLambdaN.map D.nu.unitIso.inv q
  obtain ⟨hdeg,xr,yr,hx,hy,hd⟩ := finite_last_nonzero_classical_to_finite_equation BHS q r k hr s t x y h.toHasDifferential
  refine ⟨hdeg,xr,yr,hx,hy,hd,?_⟩
  intro hyr
  have hz : A.d r (s,t,t-k) xr=0 := by
    have hi := (ModuleCat.mono_iff_injective
      (eqToHom (congrArg (A.Page r) hdeg))).mp inferInstance
    apply hi
    change (A.d r (s,t,t-k) ≫ eqToHom (congrArg (A.Page r) hdeg)) xr = _
    rw [hd,hyr,map_zero]
  let nxr := familyPageMap D.family f r (s,t,t-k) xr
  have hnx : KIP126.Synthetic.SpectralSequence.RepresentsOnPage N r (s,t,t-k)
      (finiteTargetLabel D .sphere q s t k x) nxr := by
    have hh := finite_last_nonzero_finite_quotient_rep_naturality (D:=D) f r (s,t,t-k) (D.quotientLabel q s t k x) xr hx
    rw [finite_last_nonzero_sphere_quotient_label_to_nu] at hh
    exact hh
  have hnz : N.d r (s,t,t-k) nxr=0 := by
    have hh := congrArg (fun a => a xr) (finite_last_nonzero_finite_quotient_d_naturality (D:=D) f r (s,t,t-k))
    change N.d r (s,t,t-k) nxr =
      familyPageMap D.family f r (syntheticAdamsRawTarget r (s,t,t-k)) (A.d r (s,t,t-k) xr) at hh
    simpa only [hz,map_zero] using hh
  have hout : ∀ j : ℤ, (r:ℤ)+1 ≤ j → N.d j (s,t,t-k)=0 := by
    intro j hj
    have hv := BHS.finite_quotient_page_vanishing .sphere q (by omega)
      j (s+j) (t+(j-1)) (t-k) (by omega) (Or.inr (by omega))
    have ht : syntheticAdamsRawTarget j (s,t,t-k)=(s+j,t+(j-1),t-k) := by
      simp [syntheticAdamsRawTarget,syntheticAdamsRawShift]
    haveI : Subsingleton (N.Page j (syntheticAdamsRawTarget j (s,t,t-k))) := by
      rw [ht]
      exact hv
    ext z
    exact Subsingleton.elim _ _
  obtain ⟨e,he⟩ := finite_last_nonzero_normalized_last_cycle_infinity N r (s,t,t-k) _ nxr hnx hnz hout
  have hc := finite_last_nonzero_quotient_nu_infinity_cycles BHS.eInfty q k (by omega) s t x e he
  have hidx : (q:ℤ)-k=(r:ℤ) := by omega
  rw [hidx] at hc
  exact finite_last_nonzero_nonzero_differential_not_cycle r hr s t x y h hc


end

section AlphaH0FiniteWindow
open CategoryTheory.Limits KIP126.Core.Algebra KIP126.Computation.Route
open KIP126.Classical.Adams.PageRepresentatives KIP126.Algebra
open KIP126.LinE2 KIP126.Computation.Near126
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : Model H M' Syn}
    {L' : Labels H} {G : TmfLabels H}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem stem123_middle_certificate_h324_0 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (13,137) (16,139) (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
    exact List.mem_of_getElem? (i := 324) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (13,137) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h366_1 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 14, 138, [1], 16, 139, [1, 2], "S0_AdamsE2_ss", 3072⟩ (by
    exact List.mem_of_getElem? (i := 366) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h367_2 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 14, 138, [0, 1], 16, 139, [2], "S0_AdamsE2_ss", 3073⟩ (by
    exact List.mem_of_getElem? (i := 367) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h654_3 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (15,138) (18,140) (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 15, 138, [2], 18, 140, [2], "proofs.db/log", 462481⟩ (by
    exact List.mem_of_getElem? (i := 654) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (15,138) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 138 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h656_4 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 7 (11,134) (18,140) (I.realization.basis .sphere 11 134 0 + I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 18 140 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 7, 11, 134, [0, 1, 3], 18, 140, [1], "proofs.db/log", 2671068⟩ (by
    exact List.mem_of_getElem? (i := 656) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 7 (11,134) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 134 [0, 1, 3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h250_5 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 5 (10,134) (15,138) (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 5, 10, 134, [3], 15, 138, [1], "S0_AdamsE2_ss", 2694⟩ (by
    exact List.mem_of_getElem? (i := 250) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 5 (10,134) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h277_6 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 4 (11,135) (15,138) (I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 15 138 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0], "S0_AdamsE2_ss", 2781⟩ (by
    exact List.mem_of_getElem? (i := 277) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 4 (11,135) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h339_7 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (14,137) (17,139) (I.realization.basis .sphere 14 137 1) (I.realization.basis .sphere 17 139 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 14, 137, [1], 17, 139, [1], "S0_AdamsE2_ss", 2912⟩ (by
    exact List.mem_of_getElem? (i := 339) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h340_8 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (14,137) (17,139) (I.realization.basis .sphere 14 137 0) (I.realization.basis .sphere 17 139 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 14, 137, [0], 17, 139, [0], "S0_AdamsE2_ss", 2913⟩ (by
    exact List.mem_of_getElem? (i := 340) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h304_9 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 2 (12,136) (14,137) (I.realization.basis .sphere 12 136 2) (I.realization.basis .sphere 14 137 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2], "S0_AdamsE2_ss", 2849⟩ (by
    exact List.mem_of_getElem? (i := 304) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (12,136) (14,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 137 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h319_10 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (13,136) (16,138) (I.realization.basis .sphere 13 136 1) (I.realization.basis .sphere 16 138 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 13, 136, [1], 16, 138, [1], "S0_AdamsE2_ss", 2843⟩ (by
    exact List.mem_of_getElem? (i := 319) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (13,136) (16,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 136 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 138 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h320_11 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (13,136) (16,138) (I.realization.basis .sphere 13 136 0) (I.realization.basis .sphere 16 138 0 + I.realization.basis .sphere 16 138 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 13, 136, [0], 16, 138, [0, 2], "S0_AdamsE2_ss", 2844⟩ (by
    exact List.mem_of_getElem? (i := 320) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (13,136) (16,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 138 [0, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h278_12 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 2 (11,135) (13,136) (I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 13 136 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 11, 135, [2], 13, 136, [2], "S0_AdamsE2_ss", 2782⟩ (by
    exact List.mem_of_getElem? (i := 278) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (11,135) (13,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 136 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h297_13 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) (I.realization.basis .sphere 9 133 1 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 9, 133, [1, 2], 12, 135, [0], "S0_AdamsE2_ss", 2775⟩ (by
    exact List.mem_of_getElem? (i := 297) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h298_14 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) (I.realization.basis .sphere 9 133 0 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 1 + I.realization.basis .sphere 12 135 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 9, 133, [0, 2], 12, 135, [1, 2], "S0_AdamsE2_ss", 2776⟩ (by
    exact List.mem_of_getElem? (i := 298) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [0, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_certificate_h299_15 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 5 (7,131) (12,135) (I.realization.basis .sphere 7 131 1) (I.realization.basis .sphere 12 135 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 5, 7, 131, [1], 12, 135, [2], "S0_AdamsE2_ss", 2777⟩ (by
    exact List.mem_of_getElem? (i := 299) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 5 (7,131) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_low_pages
    (I : KIP126.Computation.Route.Inputs D' L' G) :
    Subsingleton ((sequence D' .sphere).Page 6 (12,135)) ∧
    Subsingleton ((sequence D' .sphere).Page 4 (13,136)) ∧
    Subsingleton ((sequence D' .sphere).Page 4 (14,137)) := by
  classical
  let E := sequence D' .sphere
  obtain ⟨e16_139,he16_139⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
  change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 139 i.val at he16_139
  obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.realization.basis .sphere 18 140 i.val at he18_140
  obtain ⟨e15_138,he15_138⟩ := I.basis ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = I.realization.basis .sphere 15 138 i.val at he15_138
  obtain ⟨e14_137,he14_137⟩ := I.basis ⟨.sphere, 14, 137, ["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀i : Fin 3, e14_137.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 137 i.val at he14_137
  obtain ⟨e13_136,he13_136⟩ := I.basis ⟨.sphere, 13, 136, ["418,1", "417,1", "0,2,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  change E.Page 2 (13,136) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e13_136
  change ∀i : Fin 3, e13_136.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 136 i.val at he13_136
  obtain ⟨e12_135,he12_135⟩ := I.basis ⟨.sphere, 12, 135, ["408,1", "0,1,386,1", "0,2,69,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  change E.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e12_135
  change ∀i : Fin 3, e12_135.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 135 i.val at he12_135
  obtain ⟨e17_139,he17_139⟩ := I.basis ⟨.sphere, 17, 139, ["13,3,76,1", "0,1,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 237) (by rfl))
  change E.Page 2 (17,139) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e17_139
  change ∀i : Fin 2, e17_139.symm (Finsupp.single i 1) = I.realization.basis .sphere 17 139 i.val at he17_139
  obtain ⟨e16_138,he16_138⟩ := I.basis ⟨.sphere, 16, 138, ["437,1", "23,1,189,1", "0,1,424,1"]⟩ (by
    exact List.mem_of_getElem? (i := 229) (by rfl))
  change E.Page 2 (16,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_138
  change ∀i : Fin 3, e16_138.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 138 i.val at he16_138
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := stem123_middle_certificate_h324_0 I
  have h366 : HasDifferential E 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := stem123_middle_certificate_h366_1 I
  have h367 : HasDifferential E 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := stem123_middle_certificate_h367_2 I
  have h654 : HasDifferential E 3 (15,138) (18,140) (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := stem123_middle_certificate_h654_3 I
  have h656 : HasDifferential E 7 (11,134) (18,140) (I.realization.basis .sphere 11 134 0 + I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 18 140 1) := stem123_middle_certificate_h656_4 I
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := stem123_middle_certificate_h250_5 I
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 15 138 0) := stem123_middle_certificate_h277_6 I
  have h339 : HasDifferential E 3 (14,137) (17,139) (I.realization.basis .sphere 14 137 1) (I.realization.basis .sphere 17 139 1) := stem123_middle_certificate_h339_7 I
  have h340 : HasDifferential E 3 (14,137) (17,139) (I.realization.basis .sphere 14 137 0) (I.realization.basis .sphere 17 139 0) := stem123_middle_certificate_h340_8 I
  have h304 : HasDifferential E 2 (12,136) (14,137) (I.realization.basis .sphere 12 136 2) (I.realization.basis .sphere 14 137 2) := stem123_middle_certificate_h304_9 I
  have h319 : HasDifferential E 3 (13,136) (16,138) (I.realization.basis .sphere 13 136 1) (I.realization.basis .sphere 16 138 1) := stem123_middle_certificate_h319_10 I
  have h320 : HasDifferential E 3 (13,136) (16,138) (I.realization.basis .sphere 13 136 0) (I.realization.basis .sphere 16 138 0 + I.realization.basis .sphere 16 138 2) := stem123_middle_certificate_h320_11 I
  have h278 : HasDifferential E 2 (11,135) (13,136) (I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 13 136 2) := stem123_middle_certificate_h278_12 I
  have h297 : HasDifferential E 3 (9,133) (12,135) (I.realization.basis .sphere 9 133 1 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 0) := stem123_middle_certificate_h297_13 I
  have h298 : HasDifferential E 3 (9,133) (12,135) (I.realization.basis .sphere 9 133 0 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 1 + I.realization.basis .sphere 12 135 2) := stem123_middle_certificate_h298_14 I
  have h299 : HasDifferential E 5 (7,131) (12,135) (I.realization.basis .sphere 7 131 1) (I.realization.basis .sphere 12 135 2) := stem123_middle_certificate_h299_15 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have d2_16 : E.d 2 (16,139)=0 := by
    obtain ⟨_,_,y0,_,hy0,_⟩ := h324
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2;omega)
      (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
    have d12 : E.d 2 (16,139) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2)=0 := by
      have hd := h366.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d2 : E.d 2 (16,139) (I.realization.basis .sphere 16 139 2)=0 := by
      have hd := h367.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d1 : E.d 2 (16,139) (I.realization.basis .sphere 16 139 1)=0 := by
      simpa only [map_add,d2,add_zero] using d12
    ext a
    change E.d 2 (16,139) a=0
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e16_139
      (fun i => e16_139.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    fin_cases i <;> simp only [apply_ite,map_zero,he16_139,d0,d1,d2,ite_self]
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have hsub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  have e2_map_zero {p : ℤ × ℤ} {N : ℕ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin N →₀ F2))
      (h : ∀ i, E.d 2 p (e.symm (Finsupp.single i 1))=0) : E.d 2 p=0 := by
    ext a
    change E.d 2 p a=0
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e
      (fun i => e.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [apply_ite,map_zero,h,ite_self]
  have d2_15 : E.d 2 (15,138)=0 := by
    obtain ⟨_,_,b0,_,hb0,_⟩ := h277
    obtain ⟨_,_,b1,_,hb1,_⟩ := h250
    obtain ⟨_,b2,_,hb2,_,_⟩ := h654
    apply e2_map_zero e15_138
    intro i
    fin_cases i
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨b0,hb0⟩
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<5) (hrep2 _) ⟨b1,hb1⟩
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b2,hb2⟩
  have d2_14 : E.d 2 (14,137)=0 := by
    obtain ⟨_,b0,_,hb0,_,_⟩ := h340
    obtain ⟨_,b1,_,hb1,_,_⟩ := h339
    apply e2_map_zero e14_137
    intro i
    fin_cases i
    · rw [he14_137]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b0,hb0⟩
    · rw [he14_137]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b1,hb1⟩
    · rw [he14_137]
      have hd := h304.eq_on_page_two.2
      change E.d 2 (12,136) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (12,136)) _
  have source14 : Subsingleton (E.Page 4 (14,137)) := by
    apply fourth_zero_of_three_basis (by change (2:ℤ)≤2; omega) e14_137 (I.realization.basis .sphere 17 139 0) (I.realization.basis .sphere 17 139 1)
    · rw [he14_137]
      exact h340
    · rw [he14_137]
      exact h339
    · rw [he14_137]
      exact differential_target_later_zero (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) h304
    · exact d2_15
    all_goals intro hz; have hh := congrArg e17_139 hz
    all_goals simp only [map_add,show I.realization.basis .sphere 17 139 0=e17_139.symm (Finsupp.single 0 1) from (he17_139 0).symm,
      show I.realization.basis .sphere 17 139 1=e17_139.symm (Finsupp.single 1 1) from (he17_139 1).symm,
      LinearEquiv.apply_symm_apply,map_zero] at hh
    · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 1) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
  have source13 : Subsingleton (E.Page 4 (13,136)) := by
    apply fourth_zero_of_three_basis (by change (2:ℤ)≤2; omega) e13_136 (I.realization.basis .sphere 16 138 0+I.realization.basis .sphere 16 138 2)
      (I.realization.basis .sphere 16 138 1)
    · rw [he13_136]
      exact h320
    · rw [he13_136]
      exact h319
    · rw [he13_136]
      exact differential_target_later_zero (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) h278
    · exact d2_14
    all_goals intro hz; have hh := congrArg e16_138 hz
    all_goals simp only [map_add,show I.realization.basis .sphere 16 138 0=e16_138.symm (Finsupp.single 0 1) from (he16_138 0).symm,
      show I.realization.basis .sphere 16 138 1=e16_138.symm (Finsupp.single 1 1) from (he16_138 1).symm,
      show I.realization.basis .sphere 16 138 2=e16_138.symm (Finsupp.single 2 1) from (he16_138 2).symm,
      LinearEquiv.apply_symm_apply,map_zero] at hh
    · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
  have source12 : Subsingleton (E.Page 6 (12,135)) := by
    have z0 := differential_target_later_zero (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h297
    have z12 := differential_target_later_zero (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h298
    have z2 := differential_target_later_zero (by change (2:ℤ)≤5;omega) (by decide : (5:ℤ)<6) h299
    have z1 : RepresentsOnPage E 6 (12,135) (I.realization.basis .sphere 12 135 1) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using hsub z12 z2
    have hv (i : Fin 3) : RepresentsOnPage E 6 (12,135) (e12_135.symm (Finsupp.single i 1)) 0 := by
      fin_cases i
      · simpa only [he12_135] using z0
      · simpa only [he12_135] using z1
      · simpa only [he12_135] using z2
    have all (a : E.Page 6 (12,135)) : a=0 := by
      obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤6) e12_135 (fun _ => 0) hv a
      simpa only [ite_self,Finset.sum_const_zero] using hc
    exact ⟨fun x y => (all x).trans (all y).symm⟩
  exact ⟨source12,source13,source14⟩

private theorem stem123_middle_nonzero7_target_page_four_nonzero_d2_16
    (I : KIP126.Computation.Route.Inputs D' L' G) : (sequence D' .sphere).d 2 (16,139)=0  := by
  classical
  let E := sequence D' .sphere
  obtain ⟨e16_139,he16_139⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
  change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 139 i.val at he16_139
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := stem123_middle_certificate_h324_0 I
  have h366 : HasDifferential E 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := stem123_middle_certificate_h366_1 I
  have h367 : HasDifferential E 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := stem123_middle_certificate_h367_2 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _

  obtain ⟨_,_,y0,_,hy0,_⟩ := h324
  have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2;omega)
    (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
  have d12 : E.d 2 (16,139) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2)=0 := by
    have hd := h366.eq_on_page_two.2
    change E.d 2 (14,138) _ = _ at hd
    rw [←hd]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
  have d2 : E.d 2 (16,139) (I.realization.basis .sphere 16 139 2)=0 := by
    have hd := h367.eq_on_page_two.2
    change E.d 2 (14,138) _ = _ at hd
    rw [←hd]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
  have d1 : E.d 2 (16,139) (I.realization.basis .sphere 16 139 1)=0 := by
    simpa only [map_add,d2,add_zero] using d12
  ext a
  change E.d 2 (16,139) a=0
  obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e16_139
    (fun i => e16_139.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
  rw [hc,map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  fin_cases i <;> simp only [apply_ite,map_zero,he16_139,d0,d1,d2,ite_self]

private theorem stem123_middle_nonzero7_target_page_four_nonzero_bne
    (I : KIP126.Computation.Route.Inputs D' L' G) : I.realization.basis .sphere 18 140 1 ≠ 0  := by
  classical
  let E := sequence D' .sphere
  obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.realization.basis .sphere 18 140 i.val at he18_140

  rw [show I.realization.basis .sphere 18 140 1=e18_140.symm (Finsupp.single 1 1) from (he18_140 1).symm]
  intro h
  have hh := congrArg e18_140 h
  simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
  have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
  norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'

private theorem stem123_middle_nonzero7_target_page_four_nonzero_bdne
    (I : KIP126.Computation.Route.Inputs D' L' G) : I.realization.basis .sphere 18 140 1-I.realization.basis .sphere 18 140 2 ≠ 0  := by
  classical
  let E := sequence D' .sphere
  obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.realization.basis .sphere 18 140 i.val at he18_140

  intro h
  have hh := congrArg e18_140 h
  simp only [map_sub,
    show I.realization.basis .sphere 18 140 1=e18_140.symm (Finsupp.single 1 1) from (he18_140 1).symm,
    show I.realization.basis .sphere 18 140 2=e18_140.symm (Finsupp.single 2 1) from (he18_140 2).symm,
    LinearEquiv.apply_symm_apply,map_zero] at hh
  have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
  norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'

private theorem stem123_middle_nonzero7_target_page_four_nonzero_third_image (I : KIP126.Computation.Route.Inputs D' L' G) :
    ∃ b : (sequence D' .sphere).Page 3 (18,140),
    RepresentsOnPage (sequence D' .sphere) 3 (18,140)
      (I.realization.basis .sphere 18 140 2) b ∧
    (∀ v : (sequence D' .sphere).Page 3 (15,138),
      (sequence D' .sphere).d 3 (15,138) v=0 ∨ (sequence D' .sphere).d 3 (15,138) v=b) := by

  classical
  let E := sequence D' .sphere
  obtain ⟨e15_138,he15_138⟩ := I.basis ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = I.realization.basis .sphere 15 138 i.val at he15_138
  have h654 : HasDifferential E 3 (15,138) (18,140) (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := stem123_middle_certificate_h654_3 I
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := stem123_middle_certificate_h250_5 I
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 15 138 0) := stem123_middle_certificate_h277_6 I
  obtain ⟨_,s0,t0,hs0,ht0,_⟩ := h277
  obtain ⟨_,s1,t1,hs1,ht1,_⟩ := h250
  obtain ⟨_,a2,b2,ha2,hb2,hd2⟩ := h654
  change E.d 3 (15,138) a2=b2 at hd2
  obtain ⟨a0,ha0⟩ := represents_before (E := E) (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ht0
  obtain ⟨a1,ha1⟩ := represents_before (E := E) (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) ht1
  have d0 : E.d 3 (15,138) a0=0 := represents_d_zero_of_later (by change (2:ℤ)≤3;omega)
    (by decide : (3:ℤ)<4) ha0 ⟨t0,ht0⟩
  have d1 : E.d 3 (15,138) a1=0 := represents_d_zero_of_later (by change (2:ℤ)≤3;omega)
    (by decide : (3:ℤ)<5) ha1 ⟨t1,ht1⟩
  have image3 (v : E.Page 3 (15,138)) : E.d 3 (15,138) v=0 ∨ E.d 3 (15,138) v=b2 := by
    let vv : Fin 3 → E.Page 3 (15,138) := ![a0,a1,a2]
    have hv (i : Fin 3) : RepresentsOnPage E 3 (15,138) (e15_138.symm (Finsupp.single i 1)) (vv i) := by
      fin_cases i
      · change RepresentsOnPage E 3 (15,138) _ a0
        rw [he15_138]
        exact ha0
      · change RepresentsOnPage E 3 (15,138) _ a1
        rw [he15_138]
        exact ha1
      · change RepresentsOnPage E 3 (15,138) _ a2
        rw [he15_138]
        exact ha2
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e15_138 vv hv v
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hc
    change v=(if c 0=0 then 0 else a0)+((if c 1=0 then 0 else a1)+(if c 2=0 then 0 else a2)) at hc
    rw [hc]
    simp only [map_add,apply_ite,map_zero,d0,d1,hd2,ite_self,zero_add]
    by_cases hc2 : c 2=0
    · exact Or.inl (by simp only [hc2,ite_true])
    · exact Or.inr (by simp only [hc2,ite_false])
  exact ⟨b2,hb2,image3⟩

private theorem stem123_middle_nonzero7_target_page_four_nonzero (I : KIP126.Computation.Route.Inputs D' L' G)
    {y4 : (sequence D' .sphere).Page 4 (18,140)}
    (hy4 : RepresentsOnPage (sequence D' .sphere) 4 (18,140)
      (I.realization.basis .sphere 18 140 1) y4) : y4 ≠ 0 := by
  classical
  let E := sequence D' .sphere
  have d2_16 : E.d 2 (16,139)=0 := stem123_middle_nonzero7_target_page_four_nonzero_d2_16 I
  obtain ⟨b2,hb2,image3⟩ := stem123_middle_nonzero7_target_page_four_nonzero_third_image I
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hy4
  have bne : I.realization.basis .sphere 18 140 1 ≠ 0  := stem123_middle_nonzero7_target_page_four_nonzero_bne I
  have bdne : I.realization.basis .sphere 18 140 1-I.realization.basis .sphere 18 140 2 ≠ 0  := stem123_middle_nonzero7_target_page_four_nonzero_bdne I
  have y3ne : y3≠0 := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 2) (p := (18,140)) (by change (2:ℤ)≤2;omega)
    (by decide) d2_16 hy3 (represents_two_self _) bne
  have y3diff : y3-b2≠0 := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 2) (p := (18,140)) (by change (2:ℤ)≤2;omega)
    (by decide) d2_16 (represents_sub_tail hy3 hb2) (represents_two_self _) bdne

  apply represents_next_nonzero_of_incoming_two_cases_at
    (r := 3) (p := (18,140)) (q := (15,138)) (by rfl)
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) hy4 hy3 ?_ y3ne y3diff
  intro v
  change E.d 3 (15,138) v=0 ∨ E.d 3 (15,138) v=b2
  exact image3 v


private theorem stem123_middle_nonzero7
    (I : KIP126.Computation.Route.Inputs D' L' G) :
    HasNonzeroDifferential (sequence D' .sphere) 7 (11,134) (18,140)
      (I.realization.basis .sphere 11 134 0 + I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 18 140 1) := by
  classical
  let E := sequence D' .sphere
  have h656 : HasDifferential E 7 (11,134) (18,140) (I.realization.basis .sphere 11 134 0 + I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 18 140 1) := stem123_middle_certificate_h656_4 I
  obtain ⟨source12,source13,source14⟩ := stem123_middle_low_pages I
  obtain ⟨hdeg,x7,y7,hx7,hy7,hd7⟩ := h656
  obtain ⟨y4,hy4⟩ := represents_before (E := E) (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤7) hy7
  have y4ne : y4≠0 := stem123_middle_nonzero7_target_page_four_nonzero I hy4
  have incoming4 : E.d 4 (14,137)=0 := by
    ext v
    change E.d 4 (14,137) v=0
    rw [source14.elim v 0,map_zero]
  have incoming5 : E.d 5 (13,136)=0 := by
    have hz := adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 5 13 136
      (by decide) (by decide) source13
    ext v
    change E.d 5 (13,136) v=0
    rw [hz.elim v 0,map_zero]
  have incoming6 : E.d 6 (12,135)=0 := by
    ext v
    change E.d 6 (12,135) v=0
    rw [source12.elim v 0,map_zero]
  obtain ⟨y5,hy5⟩ := represents_before (E := E) (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤7) hy7
  obtain ⟨y6,hy6⟩ := represents_before (E := E) (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤7) hy7
  have y5ne := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 4) (p := (18,140)) (by change (2:ℤ)≤4;omega) (by decide) incoming4 hy5 hy4 y4ne
  have y6ne := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 5) (p := (18,140)) (by change (2:ℤ)≤5;omega) (by decide) incoming5 hy6 hy5 y5ne
  have y7ne := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 6) (p := (18,140)) (by change (2:ℤ)≤6;omega) (by decide) incoming6 hy7 hy6 y6ne
  exact ⟨hdeg,x7,y7,hx7,hy7,hd7,y7ne⟩

private theorem stem123_middle_nonzero3
    (I : KIP126.Computation.Route.Inputs D' L' G) :
    HasNonzeroDifferential (sequence D' .sphere) 3 (15,138) (18,140)
      (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := by
  classical
  let E := sequence D' .sphere
  obtain ⟨e16_139,he16_139⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
  change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 139 i.val at he16_139
  obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.realization.basis .sphere 18 140 i.val at he18_140
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := stem123_middle_certificate_h324_0 I
  have h366 : HasDifferential E 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := stem123_middle_certificate_h366_1 I
  have h367 : HasDifferential E 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := stem123_middle_certificate_h367_2 I
  have h654 : HasDifferential E 3 (15,138) (18,140) (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := stem123_middle_certificate_h654_3 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have d2_16 : E.d 2 (16,139)=0 := by
    obtain ⟨_,_,y0,_,hy0,_⟩ := h324
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2;omega)
      (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
    have d12 : E.d 2 (16,139) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2)=0 := by
      have hd := h366.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d2 : E.d 2 (16,139) (I.realization.basis .sphere 16 139 2)=0 := by
      have hd := h367.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d1 : E.d 2 (16,139) (I.realization.basis .sphere 16 139 1)=0 := by
      simpa only [map_add,d2,add_zero] using d12
    ext a
    change E.d 2 (16,139) a=0
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e16_139
      (fun i => e16_139.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    fin_cases i <;> simp only [apply_ite,map_zero,he16_139,d0,d1,d2,ite_self]
  obtain ⟨_,a2,b2,ha2,hb2,hd2⟩ := h654
  change E.d 3 (15,138) a2=b2 at hd2
  have b2base : I.realization.basis .sphere 18 140 2 ≠ 0 := by
    intro h
    rw [show I.realization.basis .sphere 18 140 2=e18_140.symm (Finsupp.single 2 1) from (he18_140 2).symm] at h
    have hh := congrArg e18_140 h
    simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
    have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
    norm_num [Finsupp.single_apply] at hh'
  have b2ne : b2≠0 := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 2) (p := (18,140))
    (by change (2:ℤ)≤2;omega) (by decide) d2_16 hb2 (hrep2 _) b2base
  exact ⟨by rfl,a2,b2,ha2,hb2,hd2,b2ne⟩

private theorem stem123_middle_certificate
    (I : KIP126.Computation.Route.Inputs D' L' G) :
    Subsingleton ((sequence D' .sphere).Page 6 (12,135)) ∧
    Subsingleton ((sequence D' .sphere).Page 4 (13,136)) ∧
    Subsingleton ((sequence D' .sphere).Page 4 (14,137)) ∧
    HasNonzeroDifferential (sequence D' .sphere) 7 (11,134) (18,140)
      (I.realization.basis .sphere 11 134 0 + I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 18 140 1) ∧
    HasNonzeroDifferential (sequence D' .sphere) 3 (15,138) (18,140)
      (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := by
  obtain ⟨source12,source13,source14⟩ := stem123_middle_low_pages I
  exact ⟨source12,source13,source14,stem123_middle_nonzero7 I,stem123_middle_nonzero3 I⟩


private theorem stem123_weight130_finite_quotients_h368_0 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (13,137) (16,139)
    (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,13,137,[2],16,139,[0],"S0_AdamsE2_ss",3074⟩ (by
    exact List.mem_of_getElem? (i := 368) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (13,137) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h366_1 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 2 (14,138) (16,139)
    (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,14,138,[1],16,139,[1, 2],"S0_AdamsE2_ss",3072⟩ (by
    exact List.mem_of_getElem? (i := 366) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h367_2 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 2 (14,138) (16,139)
    (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,14,138,[0, 1],16,139,[2],"S0_AdamsE2_ss",3073⟩ (by
    exact List.mem_of_getElem? (i := 367) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h245_3 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 2 (10,133) (12,134)
    (I.realization.basis .sphere 10 133 1) (I.realization.basis .sphere 12 134 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,133,[1],12,134,[2],"S0_AdamsE2_ss",2625⟩ (by
    exact List.mem_of_getElem? (i := 245) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (10,133) (12,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h294_4 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 2 (10,133) (12,134)
    (I.realization.basis .sphere 10 133 0) (I.realization.basis .sphere 12 134 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,133,[0],12,134,[2],"S0_AdamsE2_ss",2682⟩ (by
    exact List.mem_of_getElem? (i := 294) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (10,133) (12,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h244_5 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (7,131) (10,133)
    (I.realization.basis .sphere 7 131 0) (I.realization.basis .sphere 10 133 0 + I.realization.basis .sphere 10 133 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,7,131,[0],10,133,[0, 1],"S0_AdamsE2_ss",2624⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (7,131) (10,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0, 1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h243_6 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 2 (8,132) (10,133)
    (I.realization.basis .sphere 8 132 0) (I.realization.basis .sphere 10 133 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,132,[0],10,133,[2],"S0_AdamsE2_ss",2623⟩ (by
    exact List.mem_of_getElem? (i := 243) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (8,132) (10,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h351_7 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 4 (11,135) (15,138)
    (I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 15 138 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,11,135,[1, 2],15,138,[0],"S0_AdamsE2_ss",3000⟩ (by
    exact List.mem_of_getElem? (i := 351) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 4 (11,135) (15,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h352_8 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 5 (10,134) (15,138)
    (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,5,10,134,[3],15,138,[1],"S0_AdamsE2_ss",3001⟩ (by
    exact List.mem_of_getElem? (i := 352) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 5 (10,134) (15,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h272_9 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (11,134) (14,136)
    (I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 14 136 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,11,134,[1, 3],14,136,[0],"S0_AdamsE2_ss",2688⟩ (by
    exact List.mem_of_getElem? (i := 272) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (11,134) (14,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 134 [1, 3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 136 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h273_10 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 2 (11,134) (13,135)
    (I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 13 135 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,11,134,[3],13,135,[2],"S0_AdamsE2_ss",2689⟩ (by
    exact List.mem_of_getElem? (i := 273) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (11,134) (13,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 135 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h270_11 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 5 (6,130) (11,134)
    (I.realization.basis .sphere 6 130 0) (I.realization.basis .sphere 11 134 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,5,6,130,[0],11,134,[2],"S0_AdamsE2_ss",2686⟩ (by
    exact List.mem_of_getElem? (i := 270) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 5 (6,130) (11,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 134 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h269_12 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 2 (9,133) (11,134)
    (I.realization.basis .sphere 9 133 1) (I.realization.basis .sphere 11 134 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,9,133,[1],11,134,[4],"S0_AdamsE2_ss",2685⟩ (by
    exact List.mem_of_getElem? (i := 269) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (9,133) (11,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 134 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h297_13 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (9,133) (12,135)
    (I.realization.basis .sphere 9 133 1 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,133,[1, 2],12,135,[0],"S0_AdamsE2_ss",2775⟩ (by
    exact List.mem_of_getElem? (i := 297) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h298_14 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 3 (9,133) (12,135)
    (I.realization.basis .sphere 9 133 0 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 1 + I.realization.basis .sphere 12 135 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,133,[0, 2],12,135,[1, 2],"S0_AdamsE2_ss",2776⟩ (by
    exact List.mem_of_getElem? (i := 298) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [0, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_h299_15 (I : KIP126.Computation.Route.Inputs D' L' G) : HasDifferential (sequence D' .sphere) 5 (7,131) (12,135)
    (I.realization.basis .sphere 7 131 1) (I.realization.basis .sphere 12 135 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,5,7,131,[1],12,135,[2],"S0_AdamsE2_ss",2777⟩ (by
    exact List.mem_of_getElem? (i := 299) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 5 (7,131) (12,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_boundary_of_zero_representative
    {r : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
    (hx : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x 0) :
    x ∈ boundaries H SphereSpectrum (r-1) p := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData p
  obtain ⟨hr,z,hz,hzero⟩ := hx
  change (Subobject.ofLE (P.Z ↑(r-2).toNat) (P.Z 0) _ ≫ P.pageπ 0) z=x at hz
  change P.pageπ ↑(r-2).toNat z=0 at hzero
  obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
    (Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _)) z).mp hzero
  have hrindex : r-1-1=r-2 := by omega
  change ∃ y, boundaryMap H SphereSpectrum ↑(r-1-1).toNat p y=x
  rw [hrindex]
  refine ⟨y,?_⟩
  have hf : Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _) ≫
      cycleMap H SphereSpectrum ↑(r-2).toNat p = boundaryMap H SphereSpectrum ↑(r-2).toNat p := by
    dsimp only [boundaryMap,cycleMap,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
  rw [←hf,CategoryTheory.comp_apply,hy]
  exact hz



private theorem stem123_weight130_finite_quotients_cycle_quotient_zero_of_page
    (r c b : ℤ) (p : ℤ×ℤ) (hr : 2≤r) (hc : r≤c+1) (hb : r-1≤b)
    (hz : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r p)) :
    Subsingleton (CycleQuotient H SphereSpectrum c b p) := by
  classical
  have hall (x : cycles H SphereSpectrum c p) : NestedQuotient.projection _ (boundaries H SphereSpectrum b p) x=0 := by
    obtain ⟨x',hx'⟩ := (isCycle_iff_represents H SphereSpectrum (c+1) (by omega) p x.val).mp ⟨by omega,by simpa using x.property⟩
    obtain ⟨xr,hxr⟩ := represents_before hr hc hx'
    rw [hz.elim xr 0] at hxr
    exact (NestedQuotient.projection_eq_zero x).mpr
      (boundaries_monotone H SphereSpectrum p hb (stem123_weight130_finite_quotients_boundary_of_zero_representative hxr))
  have hz' (x : CycleQuotient H SphereSpectrum c b p) : x=0 := by
    obtain ⟨x⟩ := x
    exact hall x
  exact ⟨fun x y=>(hz' x).trans (hz' y).symm⟩



private theorem stem123_weight130_finite_quotients_cycle_differential_zero
    {r c : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
    {a : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r p}
    (hr : 2≤r) (hc : r≤c)
    (hx : x∈cycles H SphereSpectrum c p)
    (ha : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x a) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d r p a=0 := by
  classical
  obtain ⟨y,hy⟩ := (isCycle_iff_represents H SphereSpectrum (c+1) (by omega) p x).mp
    ⟨by omega,by simpa using hx⟩
  exact represents_d_zero_of_later hr (by omega : r<c+1) ha ⟨y,hy⟩



private theorem stem123_weight130_finite_quotients_nonzero_differential_not_cycle
    {r c : ℤ} {p q : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2} {y : E2 H SphereSpectrum q.1 q.2}
    (hr : 2≤r) (hc : r≤c)
    (hd : HasNonzeroDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p q x y) :
    x∉cycles H SphereSpectrum c p := by
  classical
  intro hx
  obtain ⟨rfl,a,b,ha,hb,hd,hne⟩ := hd
  simp only [eqToHom_refl,Category.comp_id] at hd
  exact hne (hd.symm.trans (stem123_weight130_finite_quotients_cycle_differential_zero hr hc hx ha))



private theorem stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
    {c b : ℤ} {p : ℤ×ℤ}
    (h : cycles H SphereSpectrum c p ≤ boundaries H SphereSpectrum b p) :
    Subsingleton (CycleQuotient H SphereSpectrum c b p) := by
  classical
  have hz (x : CycleQuotient H SphereSpectrum c b p) : x=0 := by
    obtain ⟨x⟩ := x
    exact (NestedQuotient.projection_eq_zero x).mpr (h x.property)
  exact ⟨fun x y=>(hz x).trans (hz y).symm⟩



private theorem stem123_weight130_finite_quotients_basis_mem_submodule
    {V : Type v} [AddCommGroup V] [Module ℤ V] {N : ℕ}
    (e : V ≃ₗ[ℤ] (Fin N →₀ F2)) (B : Submodule ℤ V)
    (h : ∀ i, e.symm (Finsupp.single i 1)∈B) (x : V) : x∈B := by
  classical
  have all (f : Fin N →₀ F2) : e.symm f∈B := by
    induction f using Finsupp.induction with
    | zero => simpa only [map_zero] using B.zero_mem
    | @single_add i a f hi ha ih =>
      rw [map_add]
      apply B.add_mem _ ih
      fin_cases a
      · change e.symm (Finsupp.single i (0:F2))∈B
        simpa only [Finsupp.single_zero,map_zero] using B.zero_mem
      · change e.symm (Finsupp.single i (1:F2))∈B
        exact h i
  simpa only [LinearEquiv.symm_apply_apply] using all (e x)



private theorem stem123_weight130_finite_quotients_stem123_af16_quotient (I : KIP126.Computation.Route.Inputs D' L' G) :
    Subsingleton (CycleQuotient H SphereSpectrum 2 10 (16,139)) := by
  classical
  let E := sequence D' .sphere
  have h368 : HasDifferential E 3 (13,137) (16,139)
      (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := stem123_weight130_finite_quotients_h368_0 I
  have h366 : HasDifferential E 2 (14,138) (16,139)
      (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := stem123_weight130_finite_quotients_h366_1 I
  have h367 : HasDifferential E 2 (14,138) (16,139)
      (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := stem123_weight130_finite_quotients_h367_2 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,16,139,["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 139 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 16 139 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 16 139 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 16 139 2 := he 2
  let B := boundaries H SphereSpectrum 10 (16,139)
  have b0 : I.realization.basis .sphere 16 139 0∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=11)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤3;omega) (by decide) h368)
  have b2 : I.realization.basis .sphere 16 139 2∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=11)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h367)
  have b12 : I.realization.basis .sphere 16 139 1+I.realization.basis .sphere 16 139 2∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=11)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h366)
  have b1 : I.realization.basis .sphere 16 139 1∈B := by
    simpa only [add_sub_cancel_right] using B.sub_mem b12 b2
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x hx
  apply stem123_weight130_finite_quotients_basis_mem_submodule e B _ x
  intro i
  fin_cases i
  · simpa only [he] using b0
  · simpa only [he] using b1
  · simpa only [he] using b2



private theorem stem123_weight130_finite_quotients_stem123_af10_quotient (I : KIP126.Computation.Route.Inputs D' L' G) :
    Subsingleton (CycleQuotient H SphereSpectrum 8 4 (10,133)) := by
  classical
  let E := sequence D' .sphere
  have h245 : HasDifferential E 2 (10,133) (12,134)
      (I.realization.basis .sphere 10 133 1) (I.realization.basis .sphere 12 134 2) := stem123_weight130_finite_quotients_h245_3 I
  have h294 : HasDifferential E 2 (10,133) (12,134)
      (I.realization.basis .sphere 10 133 0) (I.realization.basis .sphere 12 134 2) := stem123_weight130_finite_quotients_h294_4 I
  have h244 : HasDifferential E 3 (7,131) (10,133)
      (I.realization.basis .sphere 7 131 0) (I.realization.basis .sphere 10 133 0 + I.realization.basis .sphere 10 133 1) := stem123_weight130_finite_quotients_h244_5 I
  have h243 : HasDifferential E 2 (8,132) (10,133)
      (I.realization.basis .sphere 8 132 0) (I.realization.basis .sphere 10 133 2) := stem123_weight130_finite_quotients_h243_6 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,133,["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 133 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 10 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 10 133 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 10 133 2 := he 2
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,134,["18,1,188,1", "0,1,371,1", "0,1,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  change E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 134 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 12 134 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 12 134 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 12 134 2 := hf 2
  let B := boundaries H SphereSpectrum 4 (10,133)
  have b01 : I.realization.basis .sphere 10 133 0+I.realization.basis .sphere 10 133 1∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=5) (p:=(10,133))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤3;omega) (by decide) h244)
  have z2 : RepresentsOnPage E 5 (10,133) (I.realization.basis .sphere 10 133 2) 0 :=
      differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h243
  have b2 : I.realization.basis .sphere 10 133 2∈B := stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=5) (p:=(10,133)) z2
  have rep2 (x : E.Page 2 (10,133)) : RepresentsOnPage E 2 (10,133) x x := by
    haveI : Epi ((E.ssData (10,133)).pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective ((E.ssData (10,133)).pageπ 0)).mp inferInstance x
    exact ⟨by decide,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl,rfl⟩
  have hd0 : E.d 2 (10,133) (I.realization.basis .sphere 10 133 0)=I.realization.basis .sphere 12 134 2 := h294.eq_on_page_two.2
  have hd1 : E.d 2 (10,133) (I.realization.basis .sphere 10 133 1)=I.realization.basis .sphere 12 134 2 := h245.eq_on_page_two.2
  have hd2 : E.d 2 (10,133) (I.realization.basis .sphere 10 133 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z2⟩
  have ne : I.realization.basis .sphere 12 134 2≠0 := by
    intro hh
    rw [show I.realization.basis .sphere 12 134 2=f.symm (Finsupp.single 2 1) from (hf 2).symm] at hh
    have hh' := congrArg (fun x=>f x 2) hh
    norm_num [Finsupp.single_apply] at hh'
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x hx
  have hd : E.d 2 (10,133) x=0 := stem123_weight130_finite_quotients_cycle_differential_zero  (r:=2) (c:=8) (p:=(10,133)) (x:=x) (by decide) (by decide) hx (rep2 x)
  have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2) := by
    ext i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact b2
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact b01
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact B.add_mem b01 b2



private theorem stem123_weight130_finite_quotients_stem123_af15_quotient (I : KIP126.Computation.Route.Inputs D' L' G)
    (h3 : HasNonzeroDifferential (sequence D' .sphere) 3 (15,138) (18,140)
      (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2)) :
    Subsingleton (CycleQuotient H SphereSpectrum 3 9 (15,138)) := by
  classical
  let E := sequence D' .sphere
  have h351 : HasDifferential E 4 (11,135) (15,138)
      (I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 15 138 0) := stem123_weight130_finite_quotients_h351_7 I
  have h352 : HasDifferential E 5 (10,134) (15,138)
      (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := stem123_weight130_finite_quotients_h352_8 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,15,138,["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 15 138 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 15 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 15 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 15 138 2 := he 2
  let B := boundaries H SphereSpectrum 9 (15,138)
  let C := cycles H SphereSpectrum 3 (15,138)
  have b0 : I.realization.basis .sphere 15 138 0∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=10)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤4;omega) (by decide) h351)
  have b1 : I.realization.basis .sphere 15 138 1∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=10)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤5;omega) (by decide) h352)
  have c0 : I.realization.basis .sphere 15 138 0∈C := boundaries_le_cycles H SphereSpectrum (15,138) 9 3 b0
  have c1 : I.realization.basis .sphere 15 138 1∈C := boundaries_le_cycles H SphereSpectrum (15,138) 9 3 b1
  have bad : I.realization.basis .sphere 15 138 2∉C := stem123_weight130_finite_quotients_nonzero_differential_not_cycle (by decide) (by decide) h3
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x hx
  have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2) := by
    ext i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0' at hxe
  generalize hc1 : e x 1=c1' at hxe
  generalize hc2 : e x 2=c2' at hxe
  fin_cases c0' <;> fin_cases c1' <;> fin_cases c2'
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (C.zero_mem)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact b1
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (c1)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact b0
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (c0)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact B.add_mem b0 b1
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,add_zero,zero_add] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (C.add_mem c0 c1)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh



private theorem stem123_weight130_finite_quotients_stem123_af11_quotient (I : KIP126.Computation.Route.Inputs D' L' G)
    (h7 : HasNonzeroDifferential (sequence D' .sphere) 7 (11,134) (18,140)
      (I.realization.basis .sphere 11 134 0 + I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3)
      (I.realization.basis .sphere 18 140 1)) :
    Subsingleton (CycleQuotient H SphereSpectrum 7 5 (11,134)) := by
  classical
  let E := sequence D' .sphere
  have h272 : HasDifferential E 3 (11,134) (14,136)
      (I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 14 136 0) := stem123_weight130_finite_quotients_h272_9 I
  have h273 : HasDifferential E 2 (11,134) (13,135)
      (I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 13 135 2) := stem123_weight130_finite_quotients_h273_10 I
  have h270 : HasDifferential E 5 (6,130) (11,134)
      (I.realization.basis .sphere 6 130 0) (I.realization.basis .sphere 11 134 2) := stem123_weight130_finite_quotients_h270_11 I
  have h269 : HasDifferential E 2 (9,133) (11,134)
      (I.realization.basis .sphere 9 133 1) (I.realization.basis .sphere 11 134 4) := stem123_weight130_finite_quotients_h269_12 I
  have h297 : HasDifferential E 3 (9,133) (12,135)
      (I.realization.basis .sphere 9 133 1 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 0) := stem123_weight130_finite_quotients_h297_13 I
  have h298 : HasDifferential E 3 (9,133) (12,135)
      (I.realization.basis .sphere 9 133 0 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 1 + I.realization.basis .sphere 12 135 2) := stem123_weight130_finite_quotients_h298_14 I
  have h299 : HasDifferential E 5 (7,131) (12,135)
      (I.realization.basis .sphere 7 131 1) (I.realization.basis .sphere 12 135 2) := stem123_weight130_finite_quotients_h299_15 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,11,134,["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl))
  change E.Page 2 (11,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 134 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 11 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 11 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 11 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 11 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 11 134 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,13,135,["407,1", "1,2,351,1", "0,2,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 206) (by rfl))
  change E.Page 2 (13,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 135 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 13 135 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 13 135 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 13 135 2 := hf 2
  obtain ⟨a,ha⟩ := I.basis ⟨.sphere,12,135,["408,1", "0,1,386,1", "0,2,69,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  change E.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at a
  change ∀ i : Fin 3, a.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 135 i.val at ha
  have ha0 : a.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 12 135 0 := ha 0
  have ha1 : a.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 12 135 1 := ha 1
  have ha2 : a.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 12 135 2 := ha 2
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,14,136,["0,1,407,1"]⟩ (by
    exact List.mem_of_getElem? (i := 214) (by rfl))
  change E.Page 2 (14,136) ≃ₗ[ℤ] (Fin 1 →₀ F2) at g
  change ∀ i : Fin 1, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 136 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 14 136 0 := hg 0
  have rep2 {p : ℤ×ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    haveI : Epi ((E.ssData p).pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective ((E.ssData p).pageπ 0)).mp inferInstance x
    exact ⟨by decide,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl,rfl⟩
  have incoming : E.d 2 (12,135)=0 := by
    have z0 := differential_target_later_zero (E:=E) (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h297
    have z12 := differential_target_later_zero (E:=E) (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h298
    have z2 := differential_target_later_zero (E:=E) (by change (2:ℤ)≤5;omega) (by decide : (5:ℤ)<6) h299
    have z1 : RepresentsOnPage E 6 (12,135) (I.realization.basis .sphere 12 135 1) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using represents_sub_tail (E:=E) z12 z2
    have hd (i : Fin 3) : E.d 2 (12,135) (a.symm (Finsupp.single i 1))=0 := by
      rw [ha i]
      fin_cases i
      · exact represents_d_zero_of_later (E:=E) (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z0⟩
      · exact represents_d_zero_of_later (E:=E) (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z1⟩
      · exact represents_d_zero_of_later (E:=E) (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z2⟩
    ext x
    exact stem123_weight130_finite_quotients_basis_mem_submodule a (LinearMap.ker (E.d 2 (12,135)).hom) hd x
  have hnA : HasNonzeroDifferential E 3 (11,134) (14,136)
      (I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 14 136 0) := by
    obtain ⟨hdeg,a3,b3,ha3,hb3,hd3⟩ := h272
    refine ⟨hdeg,a3,b3,ha3,hb3,hd3,?_⟩
    apply represents_next_nonzero_of_incoming_zero_at (E:=E) (r:=2) (p:=(14,136))
      (by change (2:ℤ)≤2;omega) (by decide) incoming hb3 (rep2 _)
    intro hh
    rw [show I.realization.basis .sphere 14 136 0=g.symm (Finsupp.single 0 1) from (hg 0).symm] at hh
    have h := congrArg (fun x=>g x 0) hh
    norm_num [Finsupp.single_apply] at h
  let B := boundaries H SphereSpectrum 5 (11,134)
  let C := cycles H SphereSpectrum 7 (11,134)
  have z2 : RepresentsOnPage E 6 (11,134) (I.realization.basis .sphere 11 134 2) 0 :=
    differential_target_later_zero (E:=E) (by change (2:ℤ)≤5;omega) (by decide) h270
  have z4 : RepresentsOnPage E 6 (11,134) (I.realization.basis .sphere 11 134 4) 0 :=
    differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h269
  have b2 : I.realization.basis .sphere 11 134 2∈B := stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=6) (p:=(11,134)) z2
  have b4 : I.realization.basis .sphere 11 134 4∈B := stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=6) (p:=(11,134)) z4
  have c2 : I.realization.basis .sphere 11 134 2∈C := boundaries_le_cycles H SphereSpectrum (11,134) 5 7 b2
  have c4 : I.realization.basis .sphere 11 134 4∈C := boundaries_le_cycles H SphereSpectrum (11,134) 5 7 b4
  have badA : I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3∉C :=
    stem123_weight130_finite_quotients_nonzero_differential_not_cycle  (p:=(11,134)) (c:=7) (by decide) (by decide) hnA
  have badW : I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3∉C :=
    stem123_weight130_finite_quotients_nonzero_differential_not_cycle  (p:=(11,134)) (c:=7) (by decide) (by decide) h7
  have bad0 : I.realization.basis .sphere 11 134 0∉C := by
    intro hx
    apply stem123_weight130_finite_quotients_nonzero_differential_not_cycle  (p:=(11,134)) (c:=3) (by decide) (by decide) hnA
    obtain ⟨_,a7,_,ha7,_,_,_⟩ := h7
    have hw := (isCycle_iff_represents H SphereSpectrum 7 (by decide) (11,134) _).mpr ⟨a7,ha7⟩
    have hw3 := cycles_antitone H SphereSpectrum (11,134) (by decide : (3:ℤ)≤7-1) hw.2
    have hx3 := cycles_antitone H SphereSpectrum (11,134) (by decide : (3:ℤ)≤7) hx
    have hh := (cycles H SphereSpectrum 3 (11,134)).sub_mem hw3 hx3
    convert hh using 1 <;> first | rfl | abel
  have hd3 : E.d 2 (11,134) (I.realization.basis .sphere 11 134 3)=I.realization.basis .sphere 13 135 2 := h273.eq_on_page_two.2
  have hdA : E.d 2 (11,134) (I.realization.basis .sphere 11 134 1)+E.d 2 (11,134) (I.realization.basis .sphere 11 134 3)=0 := by
    obtain ⟨_,a3,_,ha3,_,_⟩ := h272
    simpa only [map_add] using represents_d_zero_of_later (E:=E) (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (rep2 _) ⟨a3,ha3⟩
  have hd1 : E.d 2 (11,134) (I.realization.basis .sphere 11 134 1)= -I.realization.basis .sphere 13 135 2 := by
    rw [hd3] at hdA
    exact eq_neg_of_add_eq_zero_left hdA
  have hd0 : E.d 2 (11,134) (I.realization.basis .sphere 11 134 0)=0 := by
    obtain ⟨_,a7,_,ha7,_,_,_⟩ := h7
    have hd := represents_d_zero_of_later (E:=E) (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<7) (rep2 _) ⟨a7,ha7⟩
    simpa only [map_add,add_assoc,hdA,add_zero] using hd
  have hd2 : E.d 2 (11,134) (I.realization.basis .sphere 11 134 2)=0 := represents_d_zero_of_later (E:=E)
    (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z2⟩
  have hd4 : E.d 2 (11,134) (I.realization.basis .sphere 11 134 4)=0 := represents_d_zero_of_later (E:=E)
    (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z4⟩
  have ne : I.realization.basis .sphere 13 135 2≠0 := by
    intro hh
    rw [show I.realization.basis .sphere 13 135 2=f.symm (Finsupp.single 2 1) from (hf 2).symm] at hh
    have h := congrArg (fun x=>f x 2) hh
    norm_num [Finsupp.single_apply] at h
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x hx
  have hd : E.d 2 (11,134) x=0 := stem123_weight130_finite_quotients_cycle_differential_zero  (r:=2) (c:=7) (p:=(11,134)) (x:=x) (by decide) (by decide) hx (rep2 x)
  have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4) := by
    ext i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=v0 at hxe
  generalize hc1 : e x 1=v1 at hxe
  generalize hc2 : e x 2=v2 at hxe
  generalize hc3 : e x 3=v3 at hxe
  generalize hc4 : e x 4=v4 at hxe
  fin_cases v0 <;> fin_cases v1 <;> fin_cases v2 <;> fin_cases v3 <;> fin_cases v4
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    rw [hxe]
    exact b4
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    rw [hxe]
    exact b2
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    rw [hxe]
    exact B.add_mem b2 b4
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply badA
    have hh := C.sub_mem hx (C.zero_mem)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3)-(0) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3) := by abel
    change ((I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3)-(0) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply badA
    have hh := C.sub_mem hx (c4)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3) := by abel
    change ((I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply badA
    have hh := C.sub_mem hx (c2)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 3)-(I.realization.basis .sphere 11 134 2) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3) := by abel
    change ((I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 3)-(I.realization.basis .sphere 11 134 2) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply badA
    have hh := C.sub_mem hx (C.add_mem c2 c4)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 3+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3) := by abel
    change ((I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 3+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply bad0
    have hh := C.sub_mem hx (C.zero_mem)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 0)-(0) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 0) := by abel
    change ((I.realization.basis .sphere 11 134 0)-(0) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply bad0
    have hh := C.sub_mem hx (c4)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 0) := by abel
    change ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply bad0
    have hh := C.sub_mem hx (c2)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 2)-(I.realization.basis .sphere 11 134 2) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 0) := by abel
    change ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 2)-(I.realization.basis .sphere 11 134 2) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply bad0
    have hh := C.sub_mem hx (C.add_mem c2 c4)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 0) := by abel
    change ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply badW
    have hh := C.sub_mem hx (C.zero_mem)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3)-(0) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3) := by abel
    change ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3)-(0) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply badW
    have hh := C.sub_mem hx (c4)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3) := by abel
    change ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply badW
    have hh := C.sub_mem hx (c2)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 3)-(I.realization.basis .sphere 11 134 2) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3) := by abel
    change ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 3)-(I.realization.basis .sphere 11 134 2) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply badW
    have hh := C.sub_mem hx (C.add_mem c2 c4)
    rw [hxe] at hh
    have cancel : ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 3+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 3) := by abel
    change ((I.realization.basis .sphere 11 134 0+I.realization.basis .sphere 11 134 1+I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 3+I.realization.basis .sphere 11 134 4)-(I.realization.basis .sphere 11 134 2+I.realization.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh


private theorem stem123_weight130_finite_quotients (I : KIP126.Computation.Route.Inputs D' L' G) :
    ∀ s : ℤ, 10≤s → s≤16 → Subsingleton
      (CycleQuotient H SphereSpectrum (18-s) (s-6) (s,s+123)) := by
  classical
  intro s hs hs'
  obtain ⟨p12,p13,p14,d7,d3⟩ := stem123_middle_certificate I
  interval_cases s
  · exact stem123_weight130_finite_quotients_stem123_af10_quotient I
  · exact stem123_weight130_finite_quotients_stem123_af11_quotient I d7
  · exact stem123_weight130_finite_quotients_cycle_quotient_zero_of_page 6 6 6 (12,135) (by decide) (by decide) (by decide) p12
  · exact stem123_weight130_finite_quotients_cycle_quotient_zero_of_page 4 5 7 (13,136) (by decide) (by decide) (by decide) p13
  · exact stem123_weight130_finite_quotients_cycle_quotient_zero_of_page 4 4 8 (14,137) (by decide) (by decide) (by decide) p14
  · exact stem123_weight130_finite_quotients_stem123_af15_quotient I d3
  · exact stem123_weight130_finite_quotients_stem123_af16_quotient I
end AlphaH0FiniteWindow


section AlphaH0Filtration
open CategoryTheory.Limits KIP126.Computation.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : Model H M' Syn}
    {L' : Labels H} {G : TmfLabels H}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] adamsTowerSSData adamsTowerInternalD
private theorem alpha_h0_filtration_from_finite_window (I : KIP126.Computation.Route.Inputs D' L' G)
    (BHS : SyntheticInputs D') (algebra : AlgebraData D') (binding : AlgebraBinding D' algebra)
    (h0 : BiHom 0 1 (S_0_0 : Syn)) (x : E2 H SphereSpectrum 9 132)
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11))
    (ha : FiniteDetected D' 11 (by decide) 9 132 0 x a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 17
      (lambdaMultiply 3 (sphereAction h0 a)) := by
  have alpha_h0_initial_filtration
      (algebra : AlgebraData D') (binding : AlgebraBinding D' algebra)
      (h0 : BiHom 0 1 (S_0_0 : Syn))
      (x : E2 H SphereSpectrum 9 132)
      (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11))
      (ha : FiniteDetected D' 11 (by decide) 9 132 0 x a) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 10
        (lambdaMultiply 3 (sphereAction h0 a)) := by
    have hlam : lambdaMultiply 0 h0=h0 := by
      have hc := D'.shiftCoherence.right_unit (0,1) (S_0_0 : Syn)
      have he : (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : Syn)=
          SyntheticCategory.biShift_zero.hom.app (Smn 0 1 : Syn) := by
        change (biShiftAddIso (0,1) (0,0) (0,1) (by decide)).hom.app _=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
          eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      dsimp only [lambdaMultiply,lambdaPow]
      simp only [Nat.cast_zero,neg_zero,sub_zero,eqToHom_refl,Category.id_comp]
      rw [←he]
      change (SyntheticCategory.biShift_comp (0,1) (0,0)).inv.app (S_0_0 : Syn) ≫
        (SyntheticCategory.biShift_comp (0,1) (0,0)).hom.app (S_0_0 : Syn) ≫ h0=h0
      rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    have hh := D'.comparisonCompatible.homotopy_lambda 1 1 0 h0
    rw [hlam] at hh
    obtain ⟨_,_,h,hval,_⟩ := hh
    have hf0 : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 1 h0 := by
      have hm : ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn)).F 1 (0,1)).arrow h ∈
          ModuleCat.subobjectModule _ ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn)).F 1 (0,1)) := ⟨h,rfl⟩
      change ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (S_0_0 : Syn)).F 1 (0,1)).arrow h=h0 at hval
      rw [hval] at hm
      simpa only [towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm
    obtain ⟨_,_,a',ha',_⟩ := ha.1
    have hfa : FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 9 a := by
      have hm : ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0 : Syn) 11)).F 9 (123,132)).arrow a' ∈
          ModuleCat.subobjectModule _ ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0 : Syn) 11)).F 9 (123,132)) := ⟨a',rfl⟩
      change ((towerFiltration (nuCoefficientUnit H.unit D'.nu) (XModLambdaN (S_0_0 : Syn) 11)).F 9 (123,132)).arrow a'=a at ha'
      rw [ha'] at hm
      simpa only [towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm
    have hf := binding.action_filtration (.quotient 11 .sphere) 0 1 123 132 1 9 h0 a hf0 hfa
    obtain ⟨z,hz⟩ := hf
    refine ⟨lambdaMultiply 3 z,?_⟩
    change lambdaMultiply 3 z ≫ adamsTowerMap (nuCoefficientUnit H.unit D'.nu) _ 0 10 _ = _
    change z ≫ adamsTowerMap (nuCoefficientUnit H.unit D'.nu) _ 0 10 _ = sphereAction h0 a at hz
    dsimp only [lambdaMultiply]
    simp only [Category.assoc,hz]
  have alpha_filtration_gap
      (BHS : SyntheticInputs D')
      (hfinite : ∀ s : ℤ, 10≤s → s≤16 → Subsingleton
        (PageRepresentatives.CycleQuotient H SphereSpectrum (18-s) (s-6) (s,s+123)))
      (a : BiHom 123 130 (XModLambdaN (S_0_0 : Syn) 11)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 10 a ↔
        FiltrationAtLeast (nuCoefficientUnit H.unit D'.nu) 17 a := by
    apply (D'.quotientConvergence 11 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
      10 17 123 130 (by decide)
    intro j hj hj'
    haveI : Subsingleton (PageRepresentatives.CycleQuotient H SphereSpectrum
        (11-(123+j)+130) (1+(123+j)-130) (j,123+j)) := by
      rw [show (11:ℤ)-(123+j)+130=18-j by omega,
        show (1:ℤ)+(123+j)-130=j-6 by omega,add_comm 123 j]
      exact hfinite j hj (by omega)
    let e := BHS.eInfty.presentation.finiteWindow SphereSpectrum 11 (by decide) (j,123+j) 130
      (by constructor <;> omega)
    haveI : Subsingleton (((D'.family.nuQuotient D'.nu SphereSpectrum 11).sequence.ssData (j,123+j,130)).eInfty) :=
      e.injective.subsingleton
    let hn := ModuleCat.isZero_of_subsingleton
      (((D'.family.nuQuotient D'.nu SphereSpectrum 11).sequence.ssData (j,123+j,130)).eInfty)
    let f := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.hom 11)).eInftyMap (j,123+j,130)
    let g := (D'.family.functor.map (XModLambdaN.map D'.nu.unitIso.inv 11)).eInftyMap (j,123+j,130)
    have hfg : g ≫ f=𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
        ←D'.quotientFunctoriality.map_comp,D'.nu.unitIso.inv_hom_id,
        D'.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
  exact (alpha_filtration_gap BHS (stem123_weight130_finite_quotients I) _).mp
    (alpha_h0_initial_filtration algebra binding h0 x a ha)
end AlphaH0Filtration


-- Keep type unification from expanding the full CSV relation ideal.
attribute [local irreducible] KIP126.LinE2.homogeneousPart
section AlphaOneStaircaseProof
open CategoryTheory
open KIP126.LinE2 KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Challenge2 KIP126.Computation.LinProofs KIP126.Computation.Route
set_option maxRecDepth 10000
set_option maxRecDepth 100000 in
private theorem full_basis_three_unique :
    (∀ r ∈ basisRows, r.s=14 → r.t=138 → r.index=2 → r.monomial="23,1,190,1") ∧
    (∀ r ∈ basisRows, r.s=15 → r.t=139 → r.index=1 → r.monomial="3,2,287,1") ∧
    (∀ r ∈ basisRows, r.s=15 → r.t=139 → r.index=3 → r.monomial="0,1,439,1") := by
  classical
  have h := KIP126.LinE2.BasisCertificates.ThreeCoordinates.three_coordinates

  exact h

private theorem full_staircase_high_cycles_full_staircase_af14 {literature : LiteratureInterface}
    (c : ComputationInterface literature) :
    ∃ x : E2At 14 138, HasCoordinates x [2] ∧
      ReachesPage sphereAdamsData 1000 (14,138)
        (c.bindings.routeRealization.sphere 14 138 x) := by
  classical
  let row : Raw.StaircaseRow := ⟨3005, some 14, some 138, some "2", none, some 9000⟩
  have hl : StaircaseData.lookup 23 61 = some row := by decide
  have hd : State.decode row = some (.reaches 1000 14 138 [2]) := by
    have hs : "2".splitOn "," = ["2"] := by
      simp +decide [String.splitOn, String.splitOnAux]
    have hp : State.parseCoordinates "2" = some [2] := by
      simp only [State.parseCoordinates, show "2".isEmpty = false from rfl,
        Bool.false_eq_true, ↓reduceIte, hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList] <;> first | decide | exact (List.mergeSort_of_pairwise (by decide)).symm
    change (State.parseCoordinates "2").bind (fun x => some (State.Claim.reaches 1000 14 138 x)) = _
    rw [hp]
    rfl
  obtain ⟨claim,hclaim,h⟩ := c.results.sphereStaircase.rows_sound 23 61 row hl
  rw [hd] at hclaim
  cases Option.some.inj hclaim
  obtain ⟨ht,x,hx,h⟩ := h
  refine ⟨x,hx,?_⟩
  rw [c.results.route_presentation 14 138 ht x]
  exact h


private theorem full_staircase_high_cycles_full_staircase_af15 {literature : LiteratureInterface}
    (c : ComputationInterface literature) :
    ∃ x : E2At 15 139, HasCoordinates x [1,3] ∧
      ReachesPage sphereAdamsData 1000 (15,139)
        (c.bindings.routeRealization.sphere 15 139 x) := by
  classical
  let row : Raw.StaircaseRow := ⟨3076, some 15, some 139, some "1,3", none, some 9000⟩
  have hl : StaircaseData.lookup 24 4 = some row := by decide
  have hd : State.decode row = some (.reaches 1000 15 139 [1,3]) := by
    have hs : "1,3".splitOn "," = ["1", "3"] := by
      simp +decide [String.splitOn, String.splitOnAux]
    have hp : State.parseCoordinates "1,3" = some [1,3] := by
      simp only [State.parseCoordinates, show "1,3".isEmpty = false from rfl,
        Bool.false_eq_true, ↓reduceIte, hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList] <;> first | decide | exact (List.mergeSort_of_pairwise (by decide)).symm
    change (State.parseCoordinates "1,3").bind (fun x => some (State.Claim.reaches 1000 15 139 x)) = _
    rw [hp]
    rfl
  obtain ⟨claim,hclaim,h⟩ := c.results.sphereStaircase.rows_sound 24 4 row hl
  rw [hd] at hclaim
  cases Option.some.inj hclaim
  obtain ⟨ht,x,hx,h⟩ := h
  refine ⟨x,hx,?_⟩
  rw [c.results.route_presentation 15 139 ht x]
  exact h



private theorem full_staircase_high_cycles_af14_coordinates_to_basis {literature : LiteratureInterface}
    (c : ComputationInterface literature)
    (hu : ∀ r ∈ basisRows, r.s = 14 → r.t = 138 → r.index = 2 → r.monomial = "23,1,190,1")
    (x : E2At 14 138) (hx : HasCoordinates x [2]) :
    c.bindings.routeRealization.sphere 14 138 x = c.route.realization.basis .sphere 14 138 2 := by
  classical
  obtain ⟨rows,hi,hr,hx⟩ := hx
  have hl : rows.length = 1 := by simpa using congrArg List.length hi
  obtain ⟨r,rfl⟩ := List.length_eq_one_iff.mp hl
  have hi' : r.index = 2 := by simpa using hi
  have hrs := hr r (by simp)
  have hm := hu r hrs.1 hrs.2.1 hrs.2.2 hi'
  have hv : x.val = projection (monomialOfString "23,1,190,1") := by
    simpa [basisValue,hm] using hx
  have hc := c.route.csv ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
    exact List.mem_of_getElem? (i := 216) (by rfl)) rfl
  obtain ⟨y,hy,he⟩ := hc (2 : Fin 5)
  change y.val = projection (monomialOfString "23,1,190,1") at hy
  have hxy : x = y := Subtype.ext (hv.trans hy.symm)
  rw [hxy]
  exact he


private theorem full_staircase_high_cycles_af15_coordinates_to_basis {literature : LiteratureInterface}
    (c : ComputationInterface literature)
    (hu1 : ∀ r ∈ basisRows, r.s = 15 → r.t = 139 → r.index = 1 → r.monomial = "3,2,287,1")
    (hu3 : ∀ r ∈ basisRows, r.s = 15 → r.t = 139 → r.index = 3 → r.monomial = "0,1,439,1")
    (x : E2At 15 139) (hx : HasCoordinates x [1,3]) :
    c.bindings.routeRealization.sphere 15 139 x = c.route.realization.basis .sphere 15 139 1 +
      c.route.realization.basis .sphere 15 139 3 := by
  classical
  obtain ⟨rows,hi,hr,hx⟩ := hx
  have hl : rows.length = 2 := by simpa using congrArg List.length hi
  obtain ⟨r1,r3,rfl⟩ := List.length_eq_two.mp hl
  have hi' : r1.index = 1 ∧ r3.index = 3 := by simpa using hi
  have hr1 := hr r1 (by simp)
  have hr3 := hr r3 (by simp)
  have hm1 := hu1 r1 hr1.1 hr1.2.1 hr1.2.2 hi'.1
  have hm3 := hu3 r3 hr3.1 hr3.2.1 hr3.2.2 hi'.2
  have hv : x.val = projection (monomialOfString "3,2,287,1") + projection (monomialOfString "0,1,439,1") := by
    simpa [basisValue,hm1,hm3] using hx
  have hc := c.route.csv ⟨.sphere,15,139,["448,1", "3,2,287,1", "0,1,440,1", "0,1,439,1"]⟩ (by
    exact List.mem_of_getElem? (i := 223) (by rfl)) rfl
  obtain ⟨y1,hy1,he1⟩ := hc (1 : Fin 4)
  obtain ⟨y3,hy3,he3⟩ := hc (3 : Fin 4)
  change y1.val = projection (monomialOfString "3,2,287,1") at hy1
  change y3.val = projection (monomialOfString "0,1,439,1") at hy3
  have hxy : x = y1+y3 := by
    apply Subtype.ext
    exact hv.trans (congrArg₂ (· + ·) hy1.symm hy3.symm)
  rw [hxy,map_add]
  exact congrArg₂ (· + ·) he1 he3


private theorem full_staircase_high_cycles {literature : LiteratureInterface}
    (c : ComputationInterface literature)
    (V : SphereVanishingLine standardFoundation.hf2) :
    IsPermanentCycle (sequence standardRouteModel .sphere) (14,138)
      (c.route.realization.basis .sphere 14 138 2) ∧
    IsPermanentCycle (sequence standardRouteModel .sphere) (15,139)
      (c.route.realization.basis .sphere 15 139 1 + c.route.realization.basis .sphere 15 139 3) := by
  classical
  obtain ⟨hu14,hu15a,hu15b⟩ := full_basis_three_unique
  obtain ⟨x14,hx14,hp14⟩ := full_staircase_high_cycles_full_staircase_af14 c
  obtain ⟨x15,hx15,hp15⟩ := full_staircase_high_cycles_full_staircase_af15 c
  rw [full_staircase_high_cycles_af14_coordinates_to_basis c hu14 x14 hx14] at hp14
  rw [full_staircase_high_cycles_af15_coordinates_to_basis c hu15a hu15b x15 hx15] at hp15
  constructor
  · exact permanent_cycle_of_reaches1000 V 14 138 (by norm_num) (by norm_num) _ hp14
  · exact permanent_cycle_of_reaches1000 V 15 139 (by norm_num) (by norm_num) _ hp15

end AlphaOneStaircaseProof

section AlphaOneExistenceProof
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Algebra
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] adamsTowerSSData adamsTowerInternalD
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}

open KIP126.Literature.Route
open CategoryTheory.Pretriangulated KIP126.LinE2 KIP126.Core.Algebra
open KIP126.Computation.Route KIP126.Computation.Near126
open PageRepresentatives
private theorem alpha_all_finite_frames_h366_0 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139)
    (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,14,138,[1],16,139,[1, 2],"S0_AdamsE2_ss",3072⟩ (by
    exact List.mem_of_getElem? (i := 366) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_h367_1 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139)
    (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,14,138,[0, 1],16,139,[2],"S0_AdamsE2_ss",3073⟩ (by
    exact List.mem_of_getElem? (i := 367) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_h308_2 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,137) (14,138)
    (I.realization.basis .sphere 12 137 1) (I.realization.basis .sphere 14 138 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,12,137,[1],14,138,[4],"S0_AdamsE2_ss",2921⟩ (by
    exact List.mem_of_getElem? (i := 308) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,137) (14,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_h309_3 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,137) (14,138)
    (I.realization.basis .sphere 12 137 0) (I.realization.basis .sphere 14 138 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,12,137,[0],14,138,[3],"S0_AdamsE2_ss",2922⟩ (by
    exact List.mem_of_getElem? (i := 309) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,137) (14,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_h382_4 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (15,139) (17,140)
    (I.realization.basis .sphere 15 139 3) (I.realization.basis .sphere 17 140 2 + I.realization.basis .sphere 17 140 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,15,139,[3],17,140,[2, 3],"S0_AdamsE2_ss",3141⟩ (by
    exact List.mem_of_getElem? (i := 382) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (15,139) (17,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 139 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 140 [2, 3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_h383_5 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (15,139) (17,140)
    (I.realization.basis .sphere 15 139 2 + I.realization.basis .sphere 15 139 3) (I.realization.basis .sphere 17 140 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,15,139,[2, 3],17,140,[3],"S0_AdamsE2_ss",3142⟩ (by
    exact List.mem_of_getElem? (i := 383) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (15,139) (17,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 139 [2, 3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 140 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_h282_6 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 4 (11,136) (15,139)
    (I.realization.basis .sphere 11 136 0) (I.realization.basis .sphere 15 139 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,11,136,[0],15,139,[0],"S0_AdamsE2_ss",2853⟩ (by
    exact List.mem_of_getElem? (i := 282) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (11,136) (15,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 139 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem alpha_all_finite_frames_h321_7 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,136) (13,137)
    (I.realization.basis .sphere 11 136 4) (I.realization.basis .sphere 13 137 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2914⟩ (by
    exact List.mem_of_getElem? (i := 321) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,136) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem alpha_all_finite_frames_h322_8 (I : KIP126.Computation.Route.Inputs D L G) : HasDifferential (sequence D .sphere) 3 (10,135) (13,137)
    (I.realization.basis .sphere 10 135 0) (I.realization.basis .sphere 13 137 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2915⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (10,135) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  exact h

private theorem alpha_all_finite_frames_boundary_of_zero_representative {H : Mod2EilenbergMacLane (C:=C)}
    {r : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
    (hx : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x 0) :
    x ∈ boundaries H SphereSpectrum (r-1) p := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData p
  obtain ⟨hr,z,hz,hzero⟩ := hx
  change (Subobject.ofLE (P.Z ↑(r-2).toNat) (P.Z 0) _ ≫ P.pageπ 0) z=x at hz
  change P.pageπ ↑(r-2).toNat z=0 at hzero
  obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
    (Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _)) z).mp hzero
  have hrindex : r-1-1=r-2 := by omega
  change ∃ y, boundaryMap H SphereSpectrum ↑(r-1-1).toNat p y=x
  rw [hrindex]
  refine ⟨y,?_⟩
  have hf : Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _) ≫
      cycleMap H SphereSpectrum ↑(r-2).toNat p = boundaryMap H SphereSpectrum ↑(r-2).toNat p := by
    dsimp only [boundaryMap,cycleMap,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
  rw [←hf,CategoryTheory.comp_apply,hy]
  exact hz


private theorem alpha_all_finite_frames_cycle_differential_zero {H : Mod2EilenbergMacLane (C:=C)}
    {r c : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
    {a : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r p}
    (hr : 2≤r) (hc : r≤c)
    (hx : x∈cycles H SphereSpectrum c p)
    (ha : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x a) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d r p a=0 := by
  classical
  obtain ⟨y,hy⟩ := (isCycle_iff_represents H SphereSpectrum (c+1) (by omega) p x).mp
    ⟨by omega,by simpa using hx⟩
  exact represents_d_zero_of_later hr (by omega : r<c+1) ha ⟨y,hy⟩


private theorem alpha_all_finite_frames_cycle_quotient_frame_of_boundary {H : Mod2EilenbergMacLane (C:=C)}
    {c b : ℤ} {p : ℤ×ℤ} (v : E2 H SphereSpectrum p.1 p.2)
    (hv : v∈cycles H SphereSpectrum c p)
    (h : ∀ z, z∈cycles H SphereSpectrum c p → z∈boundaries H SphereSpectrum b p ∨ z-v∈boundaries H SphereSpectrum b p) :
    ∀ q : CycleQuotient H SphereSpectrum c b p,
      q=0 ∨ q=NestedQuotient.projection _ _ ⟨v,hv⟩ := by
  classical
  rintro ⟨z⟩
  rcases h z.val z.property with hz|hz
  · exact Or.inl ((NestedQuotient.projection_eq_zero z).mpr hz)
  · right
    apply sub_eq_zero.mp
    change NestedQuotient.projection _ _ z-NestedQuotient.projection _ _ ⟨v,hv⟩=0
    rw [←map_sub]
    exact (NestedQuotient.projection_eq_zero (z-⟨v,hv⟩)).mpr hz


private theorem alpha_all_finite_frames_rep_two {H : Mod2EilenbergMacLane (C:=C)} (p : ℤ×ℤ) (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 p) :
    RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) 2 p x x := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  haveI : Epi ((E.ssData p).pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective ((E.ssData p).pageπ 0)).mp inferInstance x
  exact ⟨by decide,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl,rfl⟩


private theorem alpha_all_finite_frames_alpha_finite_frame_14 {D : Model H M Syn} (I : KIP126.Computation.Route.Inputs D L G)
    (hc : (I.realization.basis .sphere 14 138 2)∈cycles H SphereSpectrum 4 (14,138)) :
    ∀ q : CycleQuotient H SphereSpectrum 4 8 (14,138),
      q=0 ∨ q=NestedQuotient.projection _ _ ⟨(I.realization.basis .sphere 14 138 2),hc⟩ := by
  classical
  let E := sequence D .sphere
  have h366 : HasDifferential E 2 (14,138) (16,139)
      (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := alpha_all_finite_frames_h366_0 I
  have h367 : HasDifferential E 2 (14,138) (16,139)
      (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := alpha_all_finite_frames_h367_1 I
  have h308 : HasDifferential E 2 (12,137) (14,138)
      (I.realization.basis .sphere 12 137 1) (I.realization.basis .sphere 14 138 4) := alpha_all_finite_frames_h308_2 I
  have h309 : HasDifferential E 2 (12,137) (14,138)
      (I.realization.basis .sphere 12 137 0) (I.realization.basis .sphere 14 138 3) := alpha_all_finite_frames_h309_3 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
    exact List.mem_of_getElem? (i := 216) (by rfl))
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 138 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 14 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 14 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 14 138 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 14 138 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 14 138 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,16,139,["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 139 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 16 139 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 16 139 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 16 139 2 := hf 2
  let B := boundaries H SphereSpectrum 8 (14,138)
  have b3 : I.realization.basis .sphere 14 138 3∈B := by
    exact alpha_all_finite_frames_boundary_of_zero_representative (H:=H) (r:=9) (p:=(14,138))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h309)
  have hd3 : E.d 2 (14,138) (I.realization.basis .sphere 14 138 3)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide)
      (boundaries_le_cycles H SphereSpectrum (14,138) 8 4 b3) (alpha_all_finite_frames_rep_two (14,138) _)
  have b4 : I.realization.basis .sphere 14 138 4∈B := by
    exact alpha_all_finite_frames_boundary_of_zero_representative (H:=H) (r:=9) (p:=(14,138))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h308)
  have hd4 : E.d 2 (14,138) (I.realization.basis .sphere 14 138 4)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide)
      (boundaries_le_cycles H SphereSpectrum (14,138) 8 4 b4) (alpha_all_finite_frames_rep_two (14,138) _)
  have hd2 : E.d 2 (14,138) (I.realization.basis .sphere 14 138 2)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide) hc (alpha_all_finite_frames_rep_two (14,138) _)
  have hd1 : E.d 2 (14,138) (I.realization.basis .sphere 14 138 1)=I.realization.basis .sphere 16 139 1+I.realization.basis .sphere 16 139 2 := h366.eq_on_page_two.2
  have hd0 : E.d 2 (14,138) (I.realization.basis .sphere 14 138 0)=-I.realization.basis .sphere 16 139 1 := by
    have hh := h367.eq_on_page_two.2
    change E.d 2 (14,138) (I.realization.basis .sphere 14 138 0+I.realization.basis .sphere 14 138 1)=I.realization.basis .sphere 16 139 2 at hh
    rw [map_add,hd1] at hh
    have haux : ((show E.Page 2 (16,139) from E.d 2 (14,138) (I.realization.basis .sphere 14 138 0))+I.realization.basis .sphere 16 139 1)+I.realization.basis .sphere 16 139 2=0+I.realization.basis .sphere 16 139 2 := by
      simpa only [add_assoc,zero_add] using hh
    exact eq_neg_of_add_eq_zero_left (add_right_cancel haux)
  apply alpha_all_finite_frames_cycle_quotient_frame_of_boundary _ hc
  intro x hx
  have hd : E.d 2 (14,138) x=0 := alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=4) (p:=(14,138)) (by decide) (by decide) hx (alpha_all_finite_frames_rep_two (14,138) x)
  have heq : e x=Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) + Finsupp.single 4 (e x 4) := by
    ext i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) + Finsupp.single 4 (e x 4)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  generalize hc4 : e x 4=c4 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    left
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    left
    rw [hxe]
    exact b4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    left
    rw [hxe]
    exact b3
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    left
    rw [hxe]
    exact B.add_mem b3 b4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((I.realization.basis .sphere 14 138 2)-(I.realization.basis .sphere 14 138 2) : E.Page 2 (14,138))=0 := by abel
    rw [hcanc]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((I.realization.basis .sphere 14 138 2 + I.realization.basis .sphere 14 138 4)-(I.realization.basis .sphere 14 138 2) : E.Page 2 (14,138))=I.realization.basis .sphere 14 138 4 := by abel
    rw [hcanc]
    exact b4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((I.realization.basis .sphere 14 138 2 + I.realization.basis .sphere 14 138 3)-(I.realization.basis .sphere 14 138 2) : E.Page 2 (14,138))=I.realization.basis .sphere 14 138 3 := by abel
    rw [hcanc]
    exact b3
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((I.realization.basis .sphere 14 138 2 + I.realization.basis .sphere 14 138 3 + I.realization.basis .sphere 14 138 4)-(I.realization.basis .sphere 14 138 2) : E.Page 2 (14,138))=I.realization.basis .sphere 14 138 3 + I.realization.basis .sphere 14 138 4 := by abel
    rw [hcanc]
    exact B.add_mem b3 b4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 1) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh


private theorem alpha_all_finite_frames_alpha_finite_frame_15 {D : Model H M Syn} (I : KIP126.Computation.Route.Inputs D L G)
    (hc : (I.realization.basis .sphere 15 139 1 + I.realization.basis .sphere 15 139 3)∈cycles H SphereSpectrum 3 (15,139)) :
    ∀ q : CycleQuotient H SphereSpectrum 3 9 (15,139),
      q=0 ∨ q=NestedQuotient.projection _ _ ⟨(I.realization.basis .sphere 15 139 1 + I.realization.basis .sphere 15 139 3),hc⟩ := by
  classical
  let E := sequence D .sphere
  have h382 : HasDifferential E 2 (15,139) (17,140)
      (I.realization.basis .sphere 15 139 3) (I.realization.basis .sphere 17 140 2 + I.realization.basis .sphere 17 140 3) := alpha_all_finite_frames_h382_4 I
  have h383 : HasDifferential E 2 (15,139) (17,140)
      (I.realization.basis .sphere 15 139 2 + I.realization.basis .sphere 15 139 3) (I.realization.basis .sphere 17 140 3) := alpha_all_finite_frames_h383_5 I
  have h282 : HasDifferential E 4 (11,136) (15,139)
      (I.realization.basis .sphere 11 136 0) (I.realization.basis .sphere 15 139 0) := alpha_all_finite_frames_h282_6 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,15,139,["448,1", "3,2,287,1", "0,1,440,1", "0,1,439,1"]⟩ (by
    exact List.mem_of_getElem? (i := 223) (by rfl))
  change E.Page 2 (15,139) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 15 139 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.realization.basis .sphere 15 139 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.realization.basis .sphere 15 139 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.realization.basis .sphere 15 139 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.realization.basis .sphere 15 139 3 := he 3
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,17,140,["8,1,280,1", "3,1,359,1", "0,2,438,1", "0,4,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 238) (by rfl))
  change E.Page 2 (17,140) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 17 140 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = I.realization.basis .sphere 17 140 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = I.realization.basis .sphere 17 140 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = I.realization.basis .sphere 17 140 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = I.realization.basis .sphere 17 140 3 := hf 3
  let B := boundaries H SphereSpectrum 9 (15,139)
  have b0 : I.realization.basis .sphere 15 139 0∈B := by
    exact alpha_all_finite_frames_boundary_of_zero_representative (H:=H) (r:=10) (p:=(15,139))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤4;omega) (by decide) h282)
  have hd0 : E.d 2 (15,139) (I.realization.basis .sphere 15 139 0)=0 :=
    alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=3) (p:=(15,139)) (by decide) (by decide)
      (boundaries_le_cycles H SphereSpectrum (15,139) 9 3 b0) (alpha_all_finite_frames_rep_two (15,139) _)
  have hd3 : E.d 2 (15,139) (I.realization.basis .sphere 15 139 3)=I.realization.basis .sphere 17 140 2+I.realization.basis .sphere 17 140 3 := h382.eq_on_page_two.2
  have hd1 : E.d 2 (15,139) (I.realization.basis .sphere 15 139 1)=-(I.realization.basis .sphere 17 140 2+I.realization.basis .sphere 17 140 3) := by
    have hh : E.d 2 (15,139) (I.realization.basis .sphere 15 139 1 + I.realization.basis .sphere 15 139 3)=0 :=
      alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=3) (p:=(15,139)) (by decide) (by decide) hc (alpha_all_finite_frames_rep_two (15,139) _)
    rw [map_add,hd3] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hd2 : E.d 2 (15,139) (I.realization.basis .sphere 15 139 2)=-I.realization.basis .sphere 17 140 2 := by
    have hh := h383.eq_on_page_two.2
    change E.d 2 (15,139) (I.realization.basis .sphere 15 139 2+I.realization.basis .sphere 15 139 3)=I.realization.basis .sphere 17 140 3 at hh
    rw [map_add,hd3] at hh
    have haux : ((show E.Page 2 (17,140) from E.d 2 (15,139) (I.realization.basis .sphere 15 139 2))+I.realization.basis .sphere 17 140 2)+I.realization.basis .sphere 17 140 3=0+I.realization.basis .sphere 17 140 3 := by
      simpa only [add_assoc,zero_add] using hh
    exact eq_neg_of_add_eq_zero_left (add_right_cancel haux)
  apply alpha_all_finite_frames_cycle_quotient_frame_of_boundary _ hc
  intro x hx
  have hd : E.d 2 (15,139) x=0 := alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=2) (c:=3) (p:=(15,139)) (by decide) (by decide) hx (alpha_all_finite_frames_rep_two (15,139) x)
  have heq : e x=Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) := by
    ext i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    left
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((I.realization.basis .sphere 15 139 1 + I.realization.basis .sphere 15 139 3)-(I.realization.basis .sphere 15 139 1 + I.realization.basis .sphere 15 139 3) : E.Page 2 (15,139))=0 := by abel
    rw [hcanc]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    left
    rw [hxe]
    exact b0
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    right
    rw [hxe]
    have hcanc : ((I.realization.basis .sphere 15 139 0 + I.realization.basis .sphere 15 139 1 + I.realization.basis .sphere 15 139 3)-(I.realization.basis .sphere 15 139 1 + I.realization.basis .sphere 15 139 3) : E.Page 2 (15,139))=I.realization.basis .sphere 15 139 0 := by abel
    rw [hcanc]
    exact b0
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 3) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,map_zero,he0,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd3,add_zero,zero_add] at hd
    have hh := congrArg (fun z=>f z 2) hd
    norm_num [map_add,map_neg,map_zero,←hf0,←hf1,←hf2,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff] at hh


private theorem alpha_all_finite_frames_alpha_finite_frame_13 {D : Model H M Syn} (I : KIP126.Computation.Route.Inputs D L G) (facts : Derived.SphereFacts I.realization) :
    ∃ c : cycles H SphereSpectrum 5 (13,137), c.val=I.realization.sphere 13 137 correction ∧
      ∀ q : CycleQuotient H SphereSpectrum 5 7 (13,137),
        q=0 ∨ q=NestedQuotient.projection _ _ c := by
  classical
  have af13_labels (I : KIP126.Computation.Route.Inputs D L G) :
      I.realization.sphere 13 137 correction = I.realization.basis .sphere 13 137 1 ∧
      I.realization.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12)) = I.realization.basis .sphere 13 137 2 := by
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
  let E := sequence D .sphere
  let A := E.ssData (13,137)
  obtain ⟨hl1,hl2⟩ := af13_labels I
  obtain ⟨z,hz,hzn⟩ := facts.correction_permanent
  change (Subobject.ofLE (A.Z ⊤) (A.Z 0) (A.Z_anti le_top) ≫ A.pageπ 0) z = _ at hz
  change A.pageπ ⊤ z ≠ 0 at hzn
  have h321 : HasDifferential E 2 (11,136) (13,137)
      (I.realization.basis .sphere 11 136 4) (I.realization.basis .sphere 13 137 3) := alpha_all_finite_frames_h321_7 I
  have h322 : HasDifferential E 3 (10,135) (13,137)
      (I.realization.basis .sphere 10 135 0) (I.realization.basis .sphere 13 137 0) := alpha_all_finite_frames_h322_8 I
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

  let v := I.realization.basis .sphere 13 137 1
  have hvc : v∈cycles H SphereSpectrum 5 (13,137) := by
    apply permanentCycles_le_cycles H SphereSpectrum (13,137) 5
    change ∃ q, cycleMap H SphereSpectrum ⊤ (13,137) q=v
    exact ⟨z,hz.trans hl1⟩
  refine ⟨⟨v,hvc⟩,hl1.symm,?_⟩
  apply alpha_all_finite_frames_cycle_quotient_frame_of_boundary (H:=H) (p:=(13,137)) (c:=5) (b:=7) v hvc
  let B := boundaries H SphereSpectrum 7 (13,137)
  have b0 : I.realization.basis .sphere 13 137 0∈B := by
    apply alpha_all_finite_frames_boundary_of_zero_representative (H:=H) (r:=8) (p:=(13,137))
    exact differential_target_later_zero (E:=E) (r:=3) (t:=8) (p:=(10,135)) (q:=(13,137)) (by change (2:ℤ)≤3;omega) (by decide)
      ⟨rfl,incoming,a,hincoming,ha,hda⟩
  have lift_boundary {y : E.Page 2 (13,137)} (hy : RepresentsOnPage E 3 (13,137) y 0) : y∈B := by
    exact boundaries_monotone H SphereSpectrum (13,137) (by decide : (2:ℤ)≤7)
      (alpha_all_finite_frames_boundary_of_zero_representative (H:=H) (r:=3) (p:=(13,137)) hy)
  intro x hx
  obtain ⟨xr,hxr⟩ := (isCycle_iff_represents H SphereSpectrum 3 (by decide) (13,137) x).mp
    ⟨by decide,cycles_antitone H SphereSpectrum (13,137) (by decide : (2:ℤ)≤5) hx⟩
  have hxzero : E.d 3 (13,137) xr=0 :=
    alpha_all_finite_frames_cycle_differential_zero (H:=H) (r:=3) (c:=5) (p:=(13,137)) (by decide) (by decide) hx hxr
  rcases hkernel xr hxzero with hq|hq|hq|hq
  · left
    rw [hq] at hxr
    exact lift_boundary hxr
  · left
    have hh := represents_sub_tail hxr ha
    rw [hq,sub_self] at hh
    have hm := B.add_mem (lift_boundary hh) b0
    simpa only [sub_add_cancel] using hm
  · right
    have hh := represents_sub_tail hxr hb
    rw [hq,sub_self] at hh
    exact lift_boundary hh
  · right
    have hh := represents_sub_tail (represents_sub_tail hxr hb) ha
    rw [hq,add_sub_cancel_right,sub_self] at hh
    have hm := B.add_mem (lift_boundary hh) b0
    simpa only [sub_add_cancel] using hm


private theorem alpha_all_finite_frames
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}
    (I : KIP126.Computation.Route.Inputs D L G) (facts : Derived.SphereFacts I.realization)
    (h14 : I.realization.basis .sphere 14 138 2∈cycles H SphereSpectrum 4 (14,138))
    (h15 : I.realization.basis .sphere 15 139 1+I.realization.basis .sphere 15 139 3∈cycles H SphereSpectrum 3 (15,139)) :
    (∃ c : cycles H SphereSpectrum 5 (13,137), c.val=I.realization.sphere 13 137 correction ∧
      ∀ q : CycleQuotient H SphereSpectrum 5 7 (13,137), q=0 ∨ q=NestedQuotient.projection _ _ c) ∧
    (∀ q : CycleQuotient H SphereSpectrum 4 8 (14,138), q=0 ∨
      q=NestedQuotient.projection _ _ ⟨I.realization.basis .sphere 14 138 2,h14⟩) ∧
    (∀ q : CycleQuotient H SphereSpectrum 3 9 (15,139), q=0 ∨
      q=NestedQuotient.projection _ _ ⟨I.realization.basis .sphere 15 139 1+I.realization.basis .sphere 15 139 3,h15⟩) := by
  classical
  exact ⟨alpha_all_finite_frames_alpha_finite_frame_13 I facts,alpha_all_finite_frames_alpha_finite_frame_14 I h14,alpha_all_finite_frames_alpha_finite_frame_15 I h15⟩

private theorem alpha_exists_from_finite_frames_family_map_data {D : Model H M Syn} {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
  classical
  let F := (D.family.functor.map f).toSSDataMorphism
  let PX := (D.family.functor.obj X).ssData i
  let PY := (D.family.functor.obj Y).ssData i
  let nX : WithTop ℕ := ↑(r-(D.family.functor.obj X).r₀).toNat
  let nY : WithTop ℕ := ↑(r-(D.family.functor.obj Y).r₀).toNat
  change (@eqToHom (ModuleCat.{v} ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
    (F.pageMap i nX ≫ @eqToHom (ModuleCat.{v} ℤ) _ (PY.page nX) (PY.page nY) _) ≫
    @eqToHom (ModuleCat.{v} ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
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


private theorem alpha_exists_from_finite_frames_family_page_comp {D : Model H M Syn} {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
  classical
  rw [alpha_exists_from_finite_frames_family_map_data,alpha_exists_from_finite_frames_family_map_data,alpha_exists_from_finite_frames_family_map_data,Functor.map_comp]
  exact (SSDataMorphism.pageMap_comp _ _ _ _).symm


private theorem alpha_exists_from_finite_frames_family_infinity_representative_map {D : Model H M Syn}
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
  · rw [alpha_exists_from_finite_frames_family_map_data]
    have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
      (((D.family.obj Y).sequence.ssData i).pageπ 0)
    dsimp only [SyntheticAdamsFamily.obj] at h
    rw [←F.pageπ_pageMap] at h
    exact (congrArg (fun a => a z) h).symm.trans (by
      simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
  · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
      change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
      rw [he])


private theorem alpha_exists_from_finite_frames_sphere_quotient_label_to_nu {D : Model H M Syn} (q k : ℕ) (s t : ℤ)
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
        ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) D.nu.unitIso.inv 2 (s,t,t-k)) nx
      _ = targetNuLabel D .sphere s t k x := by
        simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
        dsimp only [targetNuLabel]
        congr 1
  have hlabel : familyPageMap D.family f 2 (s,t,t-k) (D.quotientLabel q s t k x)=
      finiteTargetLabel D .sphere q s t k x := by
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) q ≫ XModLambdaN.map D.nu.unitIso.inv q)
          2 (s,t,t-k) (D.sphereE2 s t k x) :=
        ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) q) (XModLambdaN.map D.nu.unitIso.inv q) 2 (s,t,t-k)) (D.sphereE2 s t k x)
      _ = familyPageMap D.family (D.nu.unitIso.inv ≫ XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q)
          2 (s,t,t-k) (D.sphereE2 s t k x) := by rw [XModLambdaN.incl_naturality]; rfl
      _ = familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)
          (familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k) (D.sphereE2 s t k x)) :=
        (ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) D.nu.unitIso.inv (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k)) (D.sphereE2 s t k x)).symm
      _ = finiteTargetLabel D .sphere q s t k x := congrArg
        (fun y => familyPageMap D.family (XModLambdaN.incl (D.nu.functor.obj SphereSpectrum) q) 2 (s,t,t-k) y) hbase
  exact hlabel


private theorem alpha_exists_from_finite_frames_detection_exists_of_infinity {D : Model H M Syn}
    {X : Syn} (c : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family X)
    (i : Tridegree) (x : (D.family.obj X).E₂ i)
    (e : ((D.family.obj X).sequence.ssData i).eInfty)
    (hx : HasInfinityRepresentative (D.family.obj X) 2 i x e) (hne : e≠0) :
    ∃ a : BiHom (i.2.1-i.1) i.2.2 X, DetectsNonzero c i x a := by
  classical
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) X
  haveI : Epi (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2))).mp
    inferInstance ((c.identification i).hom e)
  exact ⟨(F.F i.1 (i.2.1-i.1,i.2.2)).arrow a,⟨e,hx,a,rfl,ha.symm⟩,e,hx,hne⟩


private theorem alpha_exists_from_finite_frames_finite_sphere_detection_exists {D : Model H M Syn}
    (BHS : EInftyInput D) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (hx : x∈PageRepresentatives.cycles H SphereSpectrum q (s,t)) (hne : x≠0) :
    ∃ a : BiHom (t-s) (t-0) (XModLambdaN (S_0_0 : Syn) q), FiniteDetected D q hq s t 0 x a := by
  classical
  let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-0)
    (by constructor <;> omega)
  let y : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-0)) (s,t) :=
    ⟨x,by simpa only [sub_zero,sub_add_cancel] using hx⟩
  let e := P.symm (NestedQuotient.projection _ _ y)
  have he : HasInfinityRepresentative (D.family.nuQuotient D.nu SphereSpectrum q) 2 (s,t,t-0)
      (finiteTargetLabel D .sphere q s t 0 x) e := by
    apply (BHS.labels.1 .sphere q hq (s,t) 0 hq y e).mpr
    exact P.apply_symm_apply _
  have en : e≠0 := by
    intro hz
    have hp := congrArg P hz
    change P (P.symm _)=P 0 at hp
    rw [P.apply_symm_apply,map_zero] at hp
    have hm := (NestedQuotient.projection_eq_zero y).mp hp
    have hb : (1:ℤ)+t-(t-0)=1 := by omega
    change x∈PageRepresentatives.boundaries H SphereSpectrum (1+t-(t-0)) (s,t) at hm
    rw [hb,PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
    exact hne hm
  let f := XModLambdaN.map D.nu.unitIso.hom q
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.inv_hom_id,D.quotientFunctoriality.map_id]
  have hfg : f≫g=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.hom_inv_id,D.quotientFunctoriality.map_id]
  let e' := (D.family.functor.map f).eInftyMap (s,t,t-0) e
  have hel : familyPageMap D.family f 2 (s,t,t-0) (finiteTargetLabel D .sphere q s t 0 x)=D.quotientLabel q s t 0 x := by
    rw [←alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) q 0 s t x]
    calc
      _ = familyPageMap D.family (g≫f) 2 (s,t,t-0) (D.quotientLabel q s t 0 x) :=
        ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) g f 2 (s,t,t-0)) _
      _ = D.quotientLabel q s t 0 x := by
        rw [hgf,alpha_exists_from_finite_frames_family_map_data,CategoryTheory.Functor.map_id]
        exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
          (D.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData (s,t,t-0) ↑(2-2:ℤ).toNat) _
  have he' : HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-0)
      (D.quotientLabel q s t 0 x) e' := by
    have hh := alpha_exists_from_finite_frames_family_infinity_representative_map f (s,t,t-0) _ _ he
    rw [hel] at hh
    exact hh
  have en' : e'≠0 := by
    intro hz
    apply en
    have hh := congrArg (fun a=>(D.family.functor.map g).eInftyMap (s,t,t-0) a) hz
    change ((D.family.functor.map f).eInftyMap (s,t,t-0) ≫ (D.family.functor.map g).eInftyMap (s,t,t-0)) e=_ at hh
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hfg,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at hh
    simpa only [ConcreteCategory.id_apply,map_zero] using hh
  exact alpha_exists_from_finite_frames_detection_exists_of_infinity (D:=D) (D.quotientConvergence q hq) (s,t,t-0) _ e' he' en'


private theorem alpha_exists_from_finite_frames_detected_map {D : Model H M Syn}
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
  refine ⟨(D.family.functor.map f).eInftyMap i e,alpha_exists_from_finite_frames_family_infinity_representative_map f i x e he,k a',?_,?_⟩
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


private theorem alpha_exists_from_finite_frames_finite_sphere_infinity_nonzero {D : Model H M Syn}
    (BHS : EInftyInput D) (q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (hx : x∈PageRepresentatives.cycles H SphereSpectrum q (s,t)) (hne : x≠0)
    (e : ((D.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-0)).eInfty)
    (he : HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-0)
      (D.quotientLabel q s t 0 x) e) : e≠0 := by
  classical
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hh := alpha_exists_from_finite_frames_family_infinity_representative_map g (s,t,t-0) _ _ he
  have hl := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) q 0 s t x
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


private theorem alpha_exists_from_finite_frames_finite_sphere_detected_rho {D : Model H M Syn}
    (BHS : EInftyInput D) (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (hx : x∈PageRepresentatives.cycles H SphereSpectrum i (s,t)) (hne : x≠0)
    (a : BiHom (t-s) (t-0) (XModLambdaN (S_0_0 : Syn) j))
    (ha : FiniteDetected D j hj s t 0 x a) :
    FiniteDetected D i hi s t 0 x (a≫(D.quotientTower S_0_0).rho i j hij) := by
  classical
  let rho := (D.quotientTower S_0_0).rho i j hij
  have hl : familyPageMap D.family rho 2 (s,t,t-0) (D.quotientLabel j s t 0 x)=D.quotientLabel i s t 0 x := by
    change familyPageMap D.family rho 2 (s,t,t-0)
      (familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) j) 2 (s,t,t-0) (D.sphereE2 s t 0 x))=_
    calc
      _ = familyPageMap D.family (XModLambdaN.incl (S_0_0 : Syn) j≫rho) 2 (s,t,t-0) (D.sphereE2 s t 0 x) :=
        ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) (XModLambdaN.incl (S_0_0 : Syn) j) rho 2 (s,t,t-0)) _
      _ = D.quotientLabel i s t 0 x := by
        dsimp only [rho]
        rw [FiniteLambdaQuotientTower.rho_quotient]
        rfl
  have hd := alpha_exists_from_finite_frames_detected_map (D:=D) (.quotient j .sphere) (.quotient i .sphere) rho (s,t,t-0) _ a ha.1
  have hd' : Detects (D.quotientConvergence i hi) (s,t,t-0)
      (D.quotientLabel i s t 0 x) (a≫rho) := hl ▸ hd
  refine ⟨hd',?_⟩
  obtain ⟨e,he,_⟩ := hd'
  exact ⟨e,he,alpha_exists_from_finite_frames_finite_sphere_infinity_nonzero BHS i hi s t x hx hne e he⟩


private theorem alpha_exists_from_finite_frames_alpha_one_detected_pair {D : Model H M Syn}
    (BHS : EInftyInput D) (V : E2 H SphereSpectrum 9 132)
    (hV : SurvivesTo (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) 12 (9,132) V) :
    ∃ a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11),
      FiniteDetected D 11 (by decide) 9 132 0 V a ∧
      FiniteDetected D 9 (by decide) 9 132 0 V (a≫(D.quotientTower S_0_0).rho 9 11 (by decide)) := by
  classical
  obtain ⟨v,hv,hvn⟩ := hV
  have hc : V∈PageRepresentatives.cycles H SphereSpectrum 11 (9,132) :=
    ((PageRepresentatives.isCycle_iff_represents H SphereSpectrum 12 (by decide) (9,132) V).mpr ⟨v,hv⟩).2
  have hn : V≠0 := by
    intro h0
    rw [h0] at hv
    obtain ⟨_,z,hz,hzv⟩ := hv
    let P := (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).ssData (9,132)
    have hm := (subobject_cokernel_π_eq_zero_iff (P.B 0) (P.Z 0) (P.B_le_Z 0)
      ((Subobject.ofLE (P.Z 10) (P.Z 0) (P.Z_anti (by decide))) z)).mp hz
    apply hvn
    rw [←hzv]
    apply (subobject_cokernel_π_eq_zero_iff (P.B 10) (P.Z 10) (P.B_le_Z 10) z).mpr
    change (Subobject.ofLE (P.Z 10) (P.Z 0) _ ≫ (P.Z 0).arrow) z ∈ _ at hm
    rw [Subobject.ofLE_arrow] at hm
    exact (ModuleCat.subobjectModule P.V).monotone (P.B_mono (by decide : (0:WithTop ℕ)≤10)) hm
  obtain ⟨a,ha⟩ := alpha_exists_from_finite_frames_finite_sphere_detection_exists BHS 11 (by decide) 9 132 V hc hn
  refine ⟨a,ha,?_⟩
  apply alpha_exists_from_finite_frames_finite_sphere_detected_rho BHS 9 11 (by decide) (by decide) (by decide) 9 132 V _ hn a ha
  exact PageRepresentatives.cycles_antitone H SphereSpectrum (9,132) (by decide : (9:ℤ)≤11) hc


private theorem alpha_exists_from_finite_frames_finite_detection_peel {D : Model H M Syn}
    (q : ℕ) (hq : 0<q) (i : Tridegree)
    (x : (D.family.quotient (S_0_0 : Syn) q).E₂ i)
    (hframe : ∀ e : ((D.family.quotient (S_0_0 : Syn) q).sequence.ssData i).eInfty,
      e=0 ∨ HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 i x e)
    (c : BiHom (i.2.1-i.1) i.2.2 (XModLambdaN (S_0_0 : Syn) q))
    (hc : Detects (D.quotientConvergence q hq) i x c)
    (a : BiHom (i.2.1-i.1) i.2.2 (XModLambdaN (S_0_0 : Syn) q))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) i.1 a) :
    ∃ b : Bool, FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (i.1+1)
      (a-(if b then c else 0)) := by
  classical
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (XModLambdaN (S_0_0 : Syn) q)
  have ham : a ∈ (ModuleCat.subobjectModule
      (syntheticHomotopy (XModLambdaN (S_0_0 : Syn) q) (i.2.1-i.1,i.2.2)))
      (F.F i.1 (i.2.1-i.1,i.2.2)) := by
    simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
  obtain ⟨a',ha'⟩ := ham
  let gr := F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a'
  let e := ((D.quotientConvergence q hq).identification i).inv gr
  have he : ((D.quotientConvergence q hq).identification i).hom e=gr :=
    ConcreteCategory.congr_hom ((D.quotientConvergence q hq).identification i).inv_hom_id gr
  rcases hframe e with he0|hex
  · refine ⟨false,?_⟩
    simp only [Bool.false_eq_true,↓reduceIte,sub_zero]
    have hzero : Detects (D.quotientConvergence q hq) i 0 a := by
      refine ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) i,a',ha',?_⟩
      rw [he0] at he
      exact he
    exact detects_zero_filtration (D.quotientConvergence q hq) i hzero
  · refine ⟨true,?_⟩
    simp only [↓reduceIte]
    have hax : Detects (D.quotientConvergence q hq) i x a := ⟨e,hex,a',ha',he⟩
    exact detects_sub_filtration (D.quotientConvergence q hq) i hax hc


private theorem alpha_exists_from_finite_frames_sphere_lift_finite_detection {D : Model H M Syn}
    (q : ℕ) (hq : 0<q) (k : ℕ) (s t : ℤ)
    (x : E2 H SphereSpectrum s t) (c : BiHom (t-s) t (S_0_0 : Syn))
    (hc : D.sphereFirstQuotient s t (quotientClass 1 c)=x) :
    Detects (D.quotientConvergence q hq) (s,t,t-k) (D.quotientLabel q s t k x)
      (lambdaMultiply k (quotientClass q c)) := by
  classical
  have h := D.comparisonCompatible.homotopy_lambda s t k c
  rw [hc] at h
  have hh := alpha_exists_from_finite_frames_detected_map (D:=D) .sphere (.quotient q .sphere)
    (XModLambdaN.incl (S_0_0 : Syn) q) (s,t,t-k) _ (lambdaMultiply k c) h
  change Detects (D.quotientConvergence q hq) (s,t,t-k) (D.quotientLabel q s t k x)
    (lambdaMultiply k c≫XModLambdaN.incl (S_0_0 : Syn) q) at hh
  have hcomm : lambdaMultiply k c≫XModLambdaN.incl (S_0_0 : Syn) q =
      lambdaMultiply k (quotientClass q c) := by
    simp only [lambdaMultiply,quotientClass,Category.assoc]
  rw [hcomm] at hh
  exact hh


private theorem alpha_exists_from_finite_frames_sphere_quotient_high_filtration_zero {D : Model H M Syn} (BHS : EInftyInput D)
    (q : ℕ) (hq : 0<q) (m w : ℤ) (N : ℕ) (hN : (q:ℤ)≤m+N-w)
    (z : BiHom m w (XModLambdaN (S_0_0 : Syn) q))
    (hz : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) N z) : z=0 := by
  classical
  let O : SyntheticObject := .quotient q .sphere
  have hsep : ∀ z : BiHom m w (O.obj D.nu D.auxiliary),
      (∀ j : ℕ, FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) j z) → z=0 :=
    D.homotopySeparated O m w
  refine (D.convergence O).eq_zero_of_eInfty_isZero_ge N m w hsep ?_ z hz
  intro j hj
  let i : Tridegree := (j,m+j,w)
  let f := XModLambdaN.map D.nu.unitIso.hom q
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.inv_hom_id,D.quotientFunctoriality.map_id]
  let P := BHS.presentation.finite SphereSpectrum q hq ((j:ℤ),m+j) w
  have hh : ¬(0≤m+j-w ∧ m+j-w<q) := by omega
  haveI : Subsingleton (PageRepresentatives.finiteEInftyModel H SphereSpectrum q ((j:ℤ),m+j) w) := by
    dsimp only [PageRepresentatives.finiteEInftyModel]
    rw [if_neg hh]
    infer_instance
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro e
  have he : (D.family.functor.map g).eInftyMap i e=0 :=
    P.injective (Subsingleton.elim _ _)
  have h := congrArg (fun a=>(D.family.functor.map f).eInftyMap i a) he
  change ((D.family.functor.map g).eInftyMap i ≫ (D.family.functor.map f).eInftyMap i) e=_ at h
  rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
    CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id] at h
  simpa only [ConcreteCategory.id_apply,map_zero] using h


private theorem alpha_exists_from_finite_frames_finite_sphere_frame {D : Model H M Syn}
    (BHS : EInftyInput D) (q k : ℕ) (hq : 0<q) (hkq : k<q) (s t : ℤ)
    (c : PageRepresentatives.cycles H SphereSpectrum ((q:ℤ)-t+(t-k)) (s,t))
    (hframe : ∀ y : PageRepresentatives.CycleQuotient H SphereSpectrum
        ((q:ℤ)-t+(t-k)) (1+t-(t-k)) (s,t),
      y=0 ∨ y=NestedQuotient.projection _ _ c) :
    ∀ e : ((D.family.quotient (S_0_0 : Syn) q).sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) q) 2 (s,t,t-k)
        (D.quotientLabel q s t k c.val) e := by
  classical
  intro e
  let P := BHS.presentation.finiteWindow SphereSpectrum q hq (s,t) (t-k)
    (by constructor <;> omega)
  let f := XModLambdaN.map D.nu.unitIso.hom q
  let g := XModLambdaN.map D.nu.unitIso.inv q
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←D.quotientFunctoriality.map_comp,Iso.inv_hom_id,D.quotientFunctoriality.map_id]
  have heq : (D.family.functor.map f).eInftyMap (s,t,t-k)
      ((D.family.functor.map g).eInftyMap (s,t,t-k) e)=e := by
    change ((D.family.functor.map g).eInftyMap (s,t,t-k) ≫
      (D.family.functor.map f).eInftyMap (s,t,t-k)) e=e
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,hgf,
      CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    rfl
  rcases hframe (P ((D.family.functor.map g).eInftyMap (s,t,t-k) e)) with hz|hz
  · left
    have hzero : (D.family.functor.map g).eInftyMap (s,t,t-k) e=0 :=
      P.injective (hz.trans (map_zero P).symm)
    rw [hzero,map_zero] at heq
    exact heq.symm
  · right
    have hn := (BHS.labels.1 .sphere q hq (s,t) k hkq c _).mpr hz
    have hl : familyPageMap D.family f 2 (s,t,t-k)
        (finiteTargetLabel D .sphere q s t k c.val)=D.quotientLabel q s t k c.val := by
      rw [←alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) q k s t c.val]
      calc
        _ = familyPageMap D.family (g≫f) 2 (s,t,t-k) (D.quotientLabel q s t k c.val) :=
          ConcreteCategory.congr_hom (alpha_exists_from_finite_frames_family_page_comp (D:=D) g f 2 (s,t,t-k)) _
        _ = D.quotientLabel q s t k c.val := by
          rw [hgf,alpha_exists_from_finite_frames_family_map_data,CategoryTheory.Functor.map_id]
          exact ConcreteCategory.congr_hom (SSDataMorphism.pageMap_id
            (D.family.functor.obj (XModLambdaN (S_0_0 : Syn) q)).ssData
            (s,t,t-k) ↑(2-2:ℤ).toNat) _
    have h := alpha_exists_from_finite_frames_family_infinity_representative_map f (s,t,t-k) _ _ hn
    rw [hl,heq] at h
    exact h


private theorem alpha_exists_from_finite_frames_filtration_postcompose {D : Model H M Syn} {X Y : Syn} (f : X⟶Y) (s m w : ℤ)
    (a : BiHom m w X) (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (a≫f) := by
  classical
  obtain ⟨b,hb⟩ := ha
  refine ⟨b≫adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat,?_⟩
  change (b≫adamsTowerInduced (nuCoefficientUnit H.unit D.nu) f s.toNat)≫
    adamsTowerMap (nuCoefficientUnit H.unit D.nu) Y 0 s.toNat _=a≫f
  change b≫adamsTowerMap (nuCoefficientUnit H.unit D.nu) X 0 s.toNat _=a at hb
  rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hb]
  rfl


private theorem alpha_exists_from_finite_frames_alpha_three_layer_restriction {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}
    (I : KIP126.Computation.Route.Inputs D L G) (BHS : EInftyInput D) (facts : Derived.SphereFacts I.realization)
    (h14 : I.realization.basis .sphere 14 138 2∈PageRepresentatives.cycles H SphereSpectrum 4 (14,138))
    (h15 : I.realization.basis .sphere 15 139 1+I.realization.basis .sphere 15 139 3∈PageRepresentatives.cycles H SphereSpectrum 3 (15,139))
    (c13 : BiHom 124 137 (S_0_0 : Syn))
    (hc13 : D.sphereFirstQuotient 13 137 (quotientClass 1 c13)=I.realization.sphere 13 137 correction)
    (c14 : BiHom 124 138 (S_0_0 : Syn))
    (hc14 : D.sphereFirstQuotient 14 138 (quotientClass 1 c14)=I.realization.basis .sphere 14 138 2)
    (c15 : BiHom 124 139 (S_0_0 : Syn))
    (hc15 : D.sphereFirstQuotient 15 139 (quotientClass 1 c15)=I.realization.basis .sphere 15 139 1+I.realization.basis .sphere 15 139 3)
    (z : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11))
    (hz : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 13 z) :
    ∃ b13 b14 b15 : Bool,
      z≫(D.quotientTower S_0_0).rho 9 11 (by decide) =
      (if b13 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 6 (quotientClass 9 c13)) else 0)+
      (if b14 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 7 (quotientClass 9 c14)) else 0)+
      (if b15 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 8 (quotientClass 9 c15)) else 0) := by
  classical
  obtain ⟨frame13,frame14a,frame15a⟩ := alpha_all_finite_frames I facts h14 h15
  obtain ⟨x13,hx13,frame13⟩ := frame13
  have frame13' := alpha_exists_from_finite_frames_finite_sphere_frame (D:=D) BHS 11 6 (by decide) (by decide) 13 137 x13 frame13
  rw [hx13] at frame13'
  have frame14 := alpha_exists_from_finite_frames_finite_sphere_frame (D:=D) BHS 11 7 (by decide) (by decide) 14 138
    ⟨I.realization.basis .sphere 14 138 2,h14⟩ frame14a
  have frame15 := alpha_exists_from_finite_frames_finite_sphere_frame (D:=D) BHS 11 8 (by decide) (by decide) 15 139
    ⟨I.realization.basis .sphere 15 139 1+I.realization.basis .sphere 15 139 3,h15⟩
    frame15a
  let v13 : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) := lambdaMultiply 6 (quotientClass 11 c13)
  let v14 : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) := lambdaMultiply 7 (quotientClass 11 c14)
  let v15 : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) := lambdaMultiply 8 (quotientClass 11 c15)
  obtain ⟨b13,hb13⟩ := alpha_exists_from_finite_frames_finite_detection_peel (D:=D) 11 (by decide) (13,137,131) _ frame13' v13
    (alpha_exists_from_finite_frames_sphere_lift_finite_detection (D:=D) 11 (by decide) 6 13 137 _ c13 hc13) z hz
  obtain ⟨b14,hb14⟩ := alpha_exists_from_finite_frames_finite_detection_peel (D:=D) 11 (by decide) (14,138,131) _ frame14 v14
    (alpha_exists_from_finite_frames_sphere_lift_finite_detection (D:=D) 11 (by decide) 7 14 138 _ c14 hc14) _ hb13
  obtain ⟨b15,hb15⟩ := alpha_exists_from_finite_frames_finite_detection_peel (D:=D) 11 (by decide) (15,139,131) _ frame15 v15
    (alpha_exists_from_finite_frames_sphere_lift_finite_detection (D:=D) 11 (by decide) 8 15 139 _ c15 hc15) _ hb14
  let rho := (D.quotientTower S_0_0).rho 9 11 (by decide)
  have hzero : (((z-(if b13 then v13 else 0))-(if b14 then v14 else 0))-(if b15 then v15 else 0))≫rho=0 := by
    apply alpha_exists_from_finite_frames_sphere_quotient_high_filtration_zero (D:=D) BHS 9 (by decide) 124 131 16 (by decide)
    exact alpha_exists_from_finite_frames_filtration_postcompose (D:=D) rho 16 124 131 _ hb15
  have hc (n : ℕ) (w : ℤ) (c : BiHom 124 w (S_0_0 : Syn)) :
      lambdaMultiply n (quotientClass 11 c)≫rho=lambdaMultiply n (quotientClass 9 c) := by
    simp only [lambdaMultiply,quotientClass,Category.assoc,rho,
      FiniteLambdaQuotientTower.rho_quotient]
  refine ⟨b13,b14,b15,?_⟩
  simp only [Preadditive.sub_comp,ite_comp,zero_comp,v13,v14,v15,hc] at hzero
  rw [sub_sub,sub_sub] at hzero
  simpa only [add_assoc] using (sub_eq_zero.mp hzero)


private theorem alpha_exists_from_finite_frames_detects_infinity_equal {D : Model H M Syn}
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


private theorem alpha_exists_from_finite_frames_sphere_zero_weight_label {D : Model H M Syn}
    (BHS : EInftyInput D) (x : E2 H SphereSpectrum 10 134)
    (a : BiHom (134-10) (134-0) (S_0_0 : Syn))
    (ha : Detects D.sphereConvergence (10,134,134-0) (D.sphereE2 10 134 0 x) a) :
    D.sphereFirstQuotient 10 134 (quotientClass 1 a)=x := by
  classical
  let y := D.sphereFirstQuotient 10 134 (quotientClass 1 a)
  have hd := alpha_exists_from_finite_frames_detected_map (D:=D) .sphere (.quotient 1 .sphere)
    (XModLambdaN.incl (S_0_0 : Syn) 1) (10,134,134-0) _ a ha
  have hd' := D.comparisonCompatible.first_quotient 10 134 y
  have hy : (D.sphereFirstQuotient 10 134).symm y=quotientClass 1 a := by
    exact (D.sphereFirstQuotient 10 134).symm_apply_apply _
  rw [hy] at hd'
  obtain ⟨e,he,hf⟩ := alpha_exists_from_finite_frames_detects_infinity_equal (.quotient 1 .sphere) (10,134,134-0)
    (quotientClass 1 a) _ _ hd hd'
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (10,134,134-0)
    (D.quotientLabel 1 10 134 0 x) e at he
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (10,134,134-0)
    (D.quotientLabel 1 10 134 0 y) e at hf
  let g := XModLambdaN.map D.nu.unitIso.inv 1
  have he' := alpha_exists_from_finite_frames_family_infinity_representative_map g (10,134,134-0) _ _ he
  have hf' := alpha_exists_from_finite_frames_family_infinity_representative_map g (10,134,134-0) _ _ hf
  have hlx := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 1 0 10 134 x
  have hly := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 1 0 10 134 y
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


private theorem alpha_exists_from_finite_frames_finite_boundary_detects_sub_filtration {D : Model H M Syn}
    (BHS : EInftyInput D)
    (x y : E2 H SphereSpectrum 10 134)
    (hx : x∈PageRepresentatives.cycles H SphereSpectrum 8 (10,134))
    (hy : y∈PageRepresentatives.cycles H SphereSpectrum 8 (10,134))
    (hxy : x-y∈PageRepresentatives.boundaries H SphereSpectrum 4 (10,134))
    (a b : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11))
    (ha : Detects (D.quotientConvergence 11 (by decide)) (10,134,131)
      (D.quotientLabel 11 10 134 3 x) a)
    (hb : Detects (D.quotientConvergence 11 (by decide)) (10,134,131)
      (D.quotientLabel 11 10 134 3 y) b) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 (a-b) := by
  classical
  obtain ⟨e,he,a',ha',hga⟩ := ha
  obtain ⟨f,hf,b',hb',hgb⟩ := hb
  let g := XModLambdaN.map D.nu.unitIso.inv 11
  have he' := alpha_exists_from_finite_frames_family_infinity_representative_map g (10,134,131) _ _ he
  have hf' := alpha_exists_from_finite_frames_family_infinity_representative_map g (10,134,131) _ _ hf
  have hlx := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 11 3 10 134 x
  have hly := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 11 3 10 134 y
  change familyPageMap D.family g 2 (10,134,131) (D.quotientLabel 11 10 134 3 x)=_ at hlx
  change familyPageMap D.family g 2 (10,134,131) (D.quotientLabel 11 10 134 3 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  let xx : PageRepresentatives.cycles H SphereSpectrum (11-134+(134-3)) (10,134) := ⟨x,hx⟩
  let yy : PageRepresentatives.cycles H SphereSpectrum (11-134+(134-3)) (10,134) := ⟨y,hy⟩
  have hxq := (BHS.labels.1 .sphere 11 (by decide) (10,134) 3 (by decide) xx _).mp he'
  have hyq := (BHS.labels.1 .sphere 11 (by decide) (10,134) 3 (by decide) yy _).mp hf'
  have hz : NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 4 (10,134)) (xx-yy)=0 :=
    (NestedQuotient.projection_eq_zero (xx-yy)).mpr hxy
  rw [map_sub] at hz
  have heq := sub_eq_zero.mp hz
  have hge : (D.family.functor.map g).eInftyMap (10,134,131) e=
      (D.family.functor.map g).eInftyMap (10,134,131) f := by
    apply (BHS.presentation.finiteWindow SphereSpectrum 11 (by decide) (10,134) 131 (by decide)).injective
    change BHS.presentation.finiteWindow SphereSpectrum 11 (by decide) (10,134) 131 (by decide)
      ((D.family.functor.map g).eInftyMap (10,134,131) e) =
      NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 4 (10,134)) xx at hxq
    change BHS.presentation.finiteWindow SphereSpectrum 11 (by decide) (10,134) 131 (by decide)
      ((D.family.functor.map g).eInftyMap (10,134,131) f) =
      NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 4 (10,134)) yy at hyq
    exact hxq.trans (heq.trans hyq.symm)
  let h := (D.family.functor.map (XModLambdaN.map D.nu.unitIso.hom 11)).eInftyMap (10,134,131)
  have hgh : (D.family.functor.map g).eInftyMap (10,134,131) ≫ h=𝟙 _ := by
    dsimp only [g,h]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←D.quotientFunctoriality.map_comp,D.nu.unitIso.inv_hom_id,
      D.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  have hef : e=f := by
    have he0 := ConcreteCategory.congr_hom hgh e
    have hf0 := ConcreteCategory.congr_hom hgh f
    change h ((D.family.functor.map g).eInftyMap (10,134,131) e)=e at he0
    change h ((D.family.functor.map g).eInftyMap (10,134,131) f)=f at hf0
    exact he0.symm.trans ((congrArg h hge).trans hf0)
  apply detects_sub_filtration (D.quotientConvergence 11 (by decide)) (10,134,131)
    (show Detects _ _ (D.quotientLabel 11 10 134 3 x) a from ⟨e,he,a',ha',hga⟩)
  exact ⟨e,he,b',hb',hef ▸ hgb⟩


private def alpha_exists_from_finite_frames_shiftSwap (a b : ℤ × ℤ) (A : Syn) :
    (SyntheticCategory.biShift b).obj ((SyntheticCategory.biShift a).obj A) ≅
    (SyntheticCategory.biShift a).obj ((SyntheticCategory.biShift b).obj A) :=
  (biShiftAddIso a b (a+b) rfl).app A ≪≫
    ((biShiftAddIso b a (a+b) (add_comm _ _)).app A).symm


private theorem alpha_exists_from_finite_frames_shiftSwap_add (coh : BiShiftCoherence Syn)
    (a b c : ℤ × ℤ) (A : Syn) :
    (alpha_exists_from_finite_frames_shiftSwap a (b+c) A).hom ≫
      (SyntheticCategory.biShift a).map ((biShiftAddIso b c (b+c) rfl).inv.app A) =
    (biShiftAddIso b c (b+c) rfl).inv.app ((SyntheticCategory.biShift a).obj A) ≫
      (SyntheticCategory.biShift c).map (alpha_exists_from_finite_frames_shiftSwap a b A).hom ≫
      (alpha_exists_from_finite_frames_shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
  classical
  let habc : (a+b)+c=a+(b+c) := add_assoc a b c
  let hbac : b+(a+c)=a+(b+c) := by abel
  have h₁ := coh.associativity a b c (a+b) (b+c) (a+(b+c)) rfl rfl habc rfl A
  have h₂ := coh.associativity b a c (a+b) (a+c) (a+(b+c))
    (add_comm _ _) rfl habc hbac A
  have h₃ := coh.associativity b c a (b+c) (a+c) (a+(b+c))
    rfl (add_comm _ _) (add_comm _ _) hbac A
  simp only [alpha_exists_from_finite_frames_shiftSwap,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Iso.app_inv]
  rw [Functor.map_comp]
  apply (cancel_epi ((biShiftAddIso b c (b+c) rfl).hom.app
    ((SyntheticCategory.biShift a).obj A))).mp
  simp only [Category.assoc,Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc,← h₁]
  simp only [Category.assoc]
  apply (cancel_epi ((SyntheticCategory.biShift c).map
    ((biShiftAddIso a b (a+b) rfl).hom.app A))).mpr
  -- Cancel the common left factor introduced by the first associativity square.
  apply (cancel_epi ((SyntheticCategory.biShift c).map
    ((biShiftAddIso b a (a+b) (add_comm _ _)).hom.app A))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,CategoryTheory.Functor.map_id,Category.id_comp]
  rw [← Category.assoc,h₂]
  simp only [Category.assoc]
  apply (cancel_epi ((biShiftAddIso a c (a+c) rfl).hom.app
    ((SyntheticCategory.biShift b).obj A))).mpr
  apply (cancel_epi ((biShiftAddIso c a (a+c) (add_comm _ _)).hom.app
    ((SyntheticCategory.biShift b).obj A))).mp
  rw [← Category.assoc,← Category.assoc,← h₃]
  simp only [Category.assoc,Iso.hom_inv_id_app_assoc,← Functor.map_comp,
    Iso.hom_inv_id_app,CategoryTheory.Functor.map_id,Category.id_comp]
  erw [CategoryTheory.Category.id_comp,←Functor.map_comp,Iso.hom_inv_id_app,CategoryTheory.Functor.map_id]
  rfl


private theorem alpha_exists_from_finite_frames_shiftSwap_add_eq (coh : BiShiftCoherence Syn)
    (a b c d : ℤ × ℤ) (h : b+c=d) (A : Syn) :
    (alpha_exists_from_finite_frames_shiftSwap a d A).hom ≫
      (SyntheticCategory.biShift a).map ((biShiftAddIso b c d h).inv.app A) =
    (biShiftAddIso b c d h).inv.app ((SyntheticCategory.biShift a).obj A) ≫
      (SyntheticCategory.biShift c).map (alpha_exists_from_finite_frames_shiftSwap a b A).hom ≫
      (alpha_exists_from_finite_frames_shiftSwap a c ((SyntheticCategory.biShift b).obj A)).hom := by
  classical
  subst d
  exact alpha_exists_from_finite_frames_shiftSwap_add coh a b c A


private theorem alpha_exists_from_finite_frames_shiftSwap_natural (a b : ℤ × ℤ) {A B : Syn} (f : A ⟶ B) :
    (SyntheticCategory.biShift b).map ((SyntheticCategory.biShift a).map f) ≫
      (alpha_exists_from_finite_frames_shiftSwap a b B).hom =
    (alpha_exists_from_finite_frames_shiftSwap a b A).hom ≫
      (SyntheticCategory.biShift a).map ((SyntheticCategory.biShift b).map f) := by
  classical
  exact ((biShiftAddIso a b (a+b) rfl) ≪≫
    (biShiftAddIso b a (a+b) (add_comm _ _)).symm).hom.naturality f


private theorem alpha_exists_from_finite_frames_shiftSwap_hom_eq (a b d : ℤ × ℤ)
    (hab : a+b=d) (hba : b+a=d) (A : Syn) :
    (alpha_exists_from_finite_frames_shiftSwap a b A).hom =
      (biShiftAddIso a b d hab).hom.app A ≫ (biShiftAddIso b a d hba).inv.app A := by
  classical
  subst d
  rfl


private theorem alpha_exists_from_finite_frames_lambda_pow_shift (coh : BiShiftCoherence Syn)
    (n : ℕ) (a : ℤ × ℤ) (A : Syn) :
    lambdaPow n ((SyntheticCategory.biShift a).obj A) =
      (alpha_exists_from_finite_frames_shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) A).hom ≫
        (SyntheticCategory.biShift a).map (lambdaPow n A) := by
  classical
  induction n generalizing A with
  | zero =>
    change SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
      (alpha_exists_from_finite_frames_shiftSwap a 0 A).hom ≫
        (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A)
    have h : SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj A) =
        (biShiftAddIso a 0 a (add_zero a)).hom.app A ≫
          (biShiftAddIso 0 a a (zero_add a)).inv.app A ≫
            (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app A) := by
      rw [←coh.left_unit a A,Iso.inv_hom_id_app,Category.comp_id]
      exact (coh.right_unit a A).symm
    rw [alpha_exists_from_finite_frames_shiftSwap_hom_eq a 0 a (add_zero a) (zero_add a),Category.assoc]
    exact h
  | succ n ih =>
    have h1 : lambdaPow 1 ((SyntheticCategory.biShift a).obj A) =
        (alpha_exists_from_finite_frames_shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
          (SyntheticCategory.biShift a).map (lambdaPow 1 A) := by
      rw [lambdaPow_one coh,lambdaPow_one coh]
      change SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj A) =
        (alpha_exists_from_finite_frames_shiftSwap a (0,-1) A).hom ≫ (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app A)
      rw [alpha_exists_from_finite_frames_shiftSwap_hom_eq a (0,-1) (a+(0,-1)) rfl (add_comm _ _),Category.assoc]
      exact coh.lambda_comm a A
    have hn := alpha_exists_from_finite_frames_shiftSwap_natural a (KIP126.Synthetic.Context.lambdaDegree n) (lambdaPow 1 A)
    have hh := alpha_exists_from_finite_frames_shiftSwap_add_eq coh a (KIP126.Synthetic.Context.lambdaDegree 1) (KIP126.Synthetic.Context.lambdaDegree n)
      (KIP126.Synthetic.Context.lambdaDegree (n+1)) (by ext <;> simp [KIP126.Synthetic.Context.lambdaDegree]) A
    change (alpha_exists_from_finite_frames_shiftSwap a (KIP126.Synthetic.Context.lambdaDegree (n+1)) A).hom ≫
        (SyntheticCategory.biShift a).map ((lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app A) =
      (lambdaShiftAddIso 1 n (n+1) (by omega)).inv.app ((SyntheticCategory.biShift a).obj A) ≫
        (SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree n)).map (alpha_exists_from_finite_frames_shiftSwap a (KIP126.Synthetic.Context.lambdaDegree 1) A).hom ≫
        (alpha_exists_from_finite_frames_shiftSwap a (KIP126.Synthetic.Context.lambdaDegree n) ((SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree 1)).obj A)).hom at hh
    rw [lambdaPow_add coh 1 n (n+1) (by omega) ((SyntheticCategory.biShift a).obj A),
      lambdaPow_add coh 1 n (n+1) (by omega) A,h1,ih]
    simp only [Functor.map_comp,Category.assoc]
    rw [reassoc_of% hn]
    rw [reassoc_of% hh]
    rfl


private theorem alpha_exists_from_finite_frames_shift_assoc_inv (coh : BiShiftCoherence Syn)
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


private theorem alpha_exists_from_finite_frames_sphere_action_lambda_three (D : Model H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn))
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11)) :
    sphereAction (lambdaMultiply 3 η) a = lambdaMultiply 3 (sphereAction η a) := by
  classical
  let S := (S_0_0 : Syn)
  have h₁ := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (1,2) (123,132) (0,-3)
    (124,134) (123,129) (124,131) (by decide) (by decide) (by decide) (by decide) S
  have h₂ := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (1,2) (0,-3) (123,132)
    (1,-1) (123,129) (124,131) (by decide) (by decide) (by decide) (by decide) S
  simp only [biShiftAddIso,Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,eqToHom_app,
    eqToHom_refl,Category.id_comp] at h₁ h₂
  have hp :
    (SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app S ≫
      lambdaPow 3 (Smn 124 134) ≫
      (SyntheticCategory.biShift_comp (1,2) (123,132)).inv.app S =
    (SyntheticCategory.biShift_comp (1,-1) (123,132)).inv.app S ≫
      (SyntheticCategory.biShift (123,132)).map
        ((SyntheticCategory.biShift_comp (1,2) (0,-3)).inv.app S) ≫
      (SyntheticCategory.biShift (123,132)).map (lambdaPow 3 (Smn 1 2)) := by
    rw [←lambdaPow_naturality]
    change (SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app S ≫
      (SyntheticCategory.biShift (0,-3)).map ((SyntheticCategory.biShift_comp (1,2) (123,132)).inv.app S) ≫
      lambdaPow 3 ((SyntheticCategory.biShift (123,132)).obj (Smn 1 2)) = _
    rw [alpha_exists_from_finite_frames_lambda_pow_shift D.shiftCoherence 3 (123,132) (Smn 1 2)]
    dsimp only [alpha_exists_from_finite_frames_shiftSwap,KIP126.Synthetic.Context.lambdaDegree]
    simp only [Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.app_hom,Iso.app_inv,biShiftAddIso,
      NatTrans.comp_app,eqToIso.hom,eqToIso.inv,eqToHom_app,eqToHom_refl,
      Category.comp_id,Category.id_comp]
    simp only [Category.assoc]
    erw [←Category.assoc ((SyntheticCategory.biShift_comp (124,134) (0,-3)).inv.app S)]
    erw [h₁]
    simp only [Category.assoc,Smn,S,Nat.cast_ofNat,Iso.inv_hom_id_app_assoc]
    simpa only [Category.assoc,Smn,S,Nat.cast_ofNat] using
      (congrArg (fun z => z ≫ (SyntheticCategory.biShift (123,132)).map (lambdaPow 3 (Smn 1 2))) h₂.symm)
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl,Category.id_comp,Functor.map_comp,Category.assoc]
  simpa only [Category.assoc,S,Smn,Int.reduceAdd,Int.reduceSub,Nat.cast_ofNat] using
    (congrArg (fun z => z ≫ (SyntheticCategory.biShift (123,132)).map η ≫ a) hp).symm


private theorem alpha_exists_from_finite_frames_boundary_of_zero_representative {H : Mod2EilenbergMacLane (C:=C)}
    {r : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
    (hx : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x 0) :
    x ∈ boundaries H SphereSpectrum (r-1) p := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData p
  obtain ⟨hr,z,hz,hzero⟩ := hx
  change (Subobject.ofLE (P.Z ↑(r-2).toNat) (P.Z 0) _ ≫ P.pageπ 0) z=x at hz
  change P.pageπ ↑(r-2).toNat z=0 at hzero
  obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
    (Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _)) z).mp hzero
  have hrindex : r-1-1=r-2 := by omega
  change ∃ y, boundaryMap H SphereSpectrum ↑(r-1-1).toNat p y=x
  rw [hrindex]
  refine ⟨y,?_⟩
  have hf : Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _) ≫
      cycleMap H SphereSpectrum ↑(r-2).toNat p = boundaryMap H SphereSpectrum ↑(r-2).toNat p := by
    dsimp only [boundaryMap,cycleMap,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
  rw [←hf,CategoryTheory.comp_apply,hy]
  exact hz


private theorem alpha_exists_from_finite_frames_cycle_quotient_zero_of_page {H : Mod2EilenbergMacLane (C:=C)}
    (r c b : ℤ) (p : ℤ×ℤ) (hr : 2≤r) (hc : r≤c+1) (hb : r-1≤b)
    (hz : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r p)) :
    Subsingleton (CycleQuotient H SphereSpectrum c b p) := by
  classical
  have hall (x : cycles H SphereSpectrum c p) : NestedQuotient.projection _ (boundaries H SphereSpectrum b p) x=0 := by
    obtain ⟨x',hx'⟩ := (isCycle_iff_represents H SphereSpectrum (c+1) (by omega) p x.val).mp ⟨by omega,by simpa using x.property⟩
    obtain ⟨xr,hxr⟩ := represents_before hr hc hx'
    rw [hz.elim xr 0] at hxr
    exact (NestedQuotient.projection_eq_zero x).mpr
      (boundaries_monotone H SphereSpectrum p hb (alpha_exists_from_finite_frames_boundary_of_zero_representative hxr))
  have hz' (x : CycleQuotient H SphereSpectrum c b p) : x=0 := by
    obtain ⟨x⟩ := x
    exact hall x
  exact ⟨fun x y=>(hz' x).trans (hz' y).symm⟩


private theorem alpha_exists_from_finite_frames_alpha_error_filtration_gap {D : Model H M Syn}
    (BHS : SyntheticInputs D)
    (h11 : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 5 (11,135)))
    (h12 : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 4 (12,136)))
    (a : BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11)) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 11 a ↔
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 13 a := by
  classical
  apply (D.quotientConvergence 11 (by decide)).filtrationAtLeast_iff_of_eInfty_isZero
    11 13 124 131 (by decide)
  intro j hj hj'
  haveI : Subsingleton (PageRepresentatives.CycleQuotient H SphereSpectrum
      (11-(124+j)+131) (1+(124+j)-131) (j,124+j)) := by
    rw [show (11:ℤ)-(124+j)+131=18-j by omega,
      show (1:ℤ)+(124+j)-131=j-6 by omega,add_comm 124 j]
    have hjcases : j=11 ∨ j=12 := by omega
    rcases hjcases with rfl|rfl
    · exact alpha_exists_from_finite_frames_cycle_quotient_zero_of_page 5 7 5 (11,135) (by decide) (by decide) (by decide) h11
    · exact alpha_exists_from_finite_frames_cycle_quotient_zero_of_page 4 6 6 (12,136) (by decide) (by decide) (by decide) h12
  let e := BHS.eInfty.presentation.finiteWindow SphereSpectrum 11 (by decide) (j,124+j) 131
    (by constructor <;> omega)
  haveI : Subsingleton (((D.family.nuQuotient D.nu SphereSpectrum 11).sequence.ssData (j,124+j,131)).eInfty) :=
    e.injective.subsingleton
  let hn := ModuleCat.isZero_of_subsingleton
    (((D.family.nuQuotient D.nu SphereSpectrum 11).sequence.ssData (j,124+j,131)).eInfty)
  let f := (D.family.functor.map (XModLambdaN.map D.nu.unitIso.hom 11)).eInftyMap (j,124+j,131)
  let g := (D.family.functor.map (XModLambdaN.map D.nu.unitIso.inv 11)).eInftyMap (j,124+j,131)
  have hfg : g ≫ f=𝟙 _ := by
    dsimp only [f,g]
    rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,
      ←D.quotientFunctoriality.map_comp,D.nu.unitIso.inv_hom_id,
      D.quotientFunctoriality.map_id,CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  exact hfg.symm.trans (by rw [hn.eq_of_src f 0,CategoryTheory.Limits.comp_zero])


private theorem alpha_exists_from_finite_frames_alpha_error_filtration_thirteen {D : Model H M Syn}
    (BHS : SyntheticInputs D) (algebra : AlgebraData D) (binding : AlgebraBinding D algebra)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toModelData η)
    (U : E2 H SphereSpectrum 10 134) (V : E2 H SphereSpectrum 9 132)
    (source : E2 H SphereSpectrum 8 133)
    (hU : U∈PageRepresentatives.cycles H SphereSpectrum 8 (10,134))
    (hd : HasDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      2 (8,133) (10,134) source (Sphere.Internal.product H M (s:=1) (t:=2) (s':=9) (t':=132) (Sphere.Internal.hi H M 1) V + U))
    (h11 : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 5 (11,135)))
    (h12 : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 4 (12,136)))
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11))
    (ha : FiniteDetected D 11 (by decide) 9 132 0 V a)
    (u : BiHom 124 134 (S_0_0 : Syn)) (hu : SphereDetected D 10 134 0 U u) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 13
      ((show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) from lambdaMultiply 3 (sphereAction η a))-
        (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) from lambdaMultiply 3 (quotientClass 11 u))) := by
  classical
  have hlabel := alpha_exists_from_finite_frames_sphere_zero_weight_label BHS.eInfty U u hu.1
  have he := D.comparisonCompatible.homotopy_lambda 1 2 3 η
  change D.sphereFirstQuotient 1 2 (quotientClass 1 η)=Sphere.Internal.hi H M 1 at hη
  rw [hη] at he
  have hp : Detects (D.quotientConvergence 11 (by decide)) (10,134,131)
      (D.quotientLabel 11 10 134 3 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=9) (t':=132) (Sphere.Internal.hi H M 1) V))
      (sphereAction (lambdaMultiply 3 η) a) :=
    binding.finite_action 11 (by decide) 1 2 9 132 3 0
      (Sphere.Internal.hi H M 1) V (lambdaMultiply 3 η) a he ha.1
  rw [alpha_exists_from_finite_frames_sphere_action_lambda_three D η a] at hp
  have hu3 := D.comparisonCompatible.homotopy_lambda 10 134 3 u
  rw [hlabel] at hu3
  have huq := alpha_exists_from_finite_frames_detected_map (D:=D) .sphere (.quotient 11 .sphere)
    (XModLambdaN.incl (S_0_0 : Syn) 11) (10,134,131) _ (lambdaMultiply 3 u) hu3
  have hcomm : lambdaMultiply 3 u≫XModLambdaN.incl (S_0_0 : Syn) 11 =
      lambdaMultiply 3 (quotientClass 11 u) := by
    simp only [lambdaMultiply,quotientClass,Category.assoc]
  change Detects (D.quotientConvergence 11 (by decide)) (10,134,131)
    (D.quotientLabel 11 10 134 3 U) (lambdaMultiply 3 u≫XModLambdaN.incl (S_0_0 : Syn) 11) at huq
  rw [hcomm] at huq
  have hU2 : U+U=0 := by
    apply (MilnorCohomology.comparison H M 10 134).symm.injective
    rw [map_add,map_zero,←two_smul KIP126.Core.Algebra.F2,
      show (2:KIP126.Core.Algebra.F2)=0 from rfl,zero_smul]
  have hneg : -U=U := by
    apply neg_eq_iff_add_eq_zero.mpr
    exact hU2
  have hd0 := differential_target_later_zero (show (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).r₀≤2 from le_rfl)
    (show (2:ℤ)<3 from by decide) hd
  have hbound := alpha_exists_from_finite_frames_boundary_of_zero_representative (H:=H) (r:=3) (p:=(10,134)) hd0
  have hbound4 : Sphere.Internal.product H M (s:=1) (t:=2) (s':=9) (t':=132) (Sphere.Internal.hi H M 1) V-U∈
      PageRepresentatives.boundaries H SphereSpectrum 4 (10,134) := by
    rw [sub_eq_add_neg,hneg]
    exact PageRepresentatives.boundaries_monotone H SphereSpectrum (10,134) (by decide : (2:ℤ)≤4) hbound
  have hprod : Sphere.Internal.product H M (s:=1) (t:=2) (s':=9) (t':=132) (Sphere.Internal.hi H M 1) V∈
      PageRepresentatives.cycles H SphereSpectrum 8 (10,134) := by
    have hb := PageRepresentatives.boundaries_le_cycles H SphereSpectrum (10,134) 4 8 hbound4
    have hh := (PageRepresentatives.cycles H SphereSpectrum 8 (10,134)).add_mem hb hU
    simpa only [sub_add_cancel] using hh
  apply (alpha_exists_from_finite_frames_alpha_error_filtration_gap BHS h11 h12 _).mp
  exact alpha_exists_from_finite_frames_finite_boundary_detects_sub_filtration BHS.eInfty _ U hprod hU hbound4 _ _ hp huq


private theorem alpha_exists_from_finite_frames_lambda_six_one (D : Model H M Syn)
    (c : BiHom 124 138 (S_0_0 : Syn)) :
    lambdaMultiply 6 (lambdaMultiply 1 c) = lambdaMultiply 7 c := by
  classical
  have ha := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (124,138) (0,-1) (0,-6)
    (124,137) (0,-7) (124,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv,
    eqToHom_app, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (124,138) (0,-1)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 6 (lambdaPow 1 (Smn 124 138)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add D.shiftCoherence 1 6 7 (by decide) (Smn 124 138)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl


private theorem alpha_exists_from_finite_frames_lambda_six_two (D : Model H M Syn)
    (c : BiHom 124 139 (S_0_0 : Syn)) :
    lambdaMultiply 6 (lambdaMultiply 2 c) = lambdaMultiply 8 c := by
  classical
  have ha := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (124,139) (0,-2) (0,-6)
    (124,137) (0,-8) (124,131) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv,
    eqToHom_app, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 6
    ((SyntheticCategory.biShift_comp (124,139) (0,-2)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 6 (lambdaPow 2 (Smn 124 139)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add D.shiftCoherence 2 6 8 (by decide) (Smn 124 139)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl


private theorem alpha_exists_from_finite_frames_lambda_one_one (D : Model H M Syn)
    (c : BiHom 125 141 (S_0_0 : Syn)) :
    lambdaMultiply 1 (lambdaMultiply 1 c) = lambdaMultiply 2 c := by
  classical
  have ha := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (125,141) (0,-1) (0,-1)
    (125,140) (0,-2) (125,139) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv,
    eqToHom_app, eqToHom_refl, Category.id_comp] at ha
  unfold lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, Nat.cast_ofNat, Int.reduceSub]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift_comp (125,141) (0,-1)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 1 (lambdaPow 1 (Smn 125 141)))]
  erw [← Category.assoc, ha]
  erw [lambdaPow_add D.shiftCoherence 1 1 2 (by decide) (Smn 125 141)]
  simp only [lambdaShiftAddIso, biShiftAddIso, KIP126.Synthetic.Context.lambdaDegree,
    Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rfl


private theorem alpha_exists_from_finite_frames_sphere_action_right_one (D : Model H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn))
    (c : BiHom 124 138 (S_0_0 : Syn)) :
    sphereAction η (lambdaMultiply 1 c) = lambdaMultiply 1 (sphereAction η c) := by
  classical
  have ha := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (1,2) (124,138) (0,-1)
    (125,140) (124,137) (125,139) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv,
    eqToHom_app, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift_comp (1,2) (124,138)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 1
    ((SyntheticCategory.biShift (124,138)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,138) (0,-1)).inv.naturality η)]
  rfl


private theorem alpha_exists_from_finite_frames_sphere_action_right_two (D : Model H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn))
    (c : BiHom 124 139 (S_0_0 : Syn)) :
    sphereAction η (lambdaMultiply 2 c) = lambdaMultiply 2 (sphereAction η c) := by
  classical
  have ha := alpha_exists_from_finite_frames_shift_assoc_inv D.shiftCoherence (1,2) (124,139) (0,-2)
    (125,141) (124,137) (125,139) (by decide) (by decide) (by decide) (by decide) (S_0_0 : Syn)
  simp only [biShiftAddIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv,
    eqToHom_app, eqToHom_refl, Category.id_comp] at ha
  unfold sphereAction lambdaMultiply
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, Nat.cast_ofNat,
    Int.reduceSub, Int.reduceAdd]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift_comp (1,2) (124,139)).inv.app (S_0_0 : Syn)))]
  erw [← reassoc_of% (lambdaPow_naturality 2
    ((SyntheticCategory.biShift (124,139)).map η))]
  erw [reassoc_of% ha]
  erw [← reassoc_of% ((SyntheticCategory.biShift_comp (124,139) (0,-2)).inv.naturality η)]
  rfl


private theorem alpha_exists_from_finite_frames_sphere_action_right_two_as_ones (D : Model H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn)) (c : BiHom 124 139 (S_0_0 : Syn)) :
    sphereAction η (lambdaMultiply 2 c) = lambdaMultiply 1 (lambdaMultiply 1 (sphereAction η c)) := by
  classical
  exact (alpha_exists_from_finite_frames_sphere_action_right_two D η c).trans (alpha_exists_from_finite_frames_lambda_one_one D (sphereAction η c)).symm


private theorem alpha_exists_from_finite_frames_lambda_one_division_of_quotient_zero
    {X : Syn} (m w : ℤ) (z : BiHom m (w-1) X) (hz : quotientClass 1 z=0) :
    ∃ b : BiHom m w X, lambdaMultiply 1 b=z := by
  classical
  obtain ⟨a,ha⟩ := (vanishesModLambda_iff_factors 1 z).mp hz
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
  let e : F.obj (Smn m w : Syn) ≅ Smn m (w-1) :=
    (SyntheticCategory.biShift_comp (m,w) (0,-1)).app S_0_0 ≪≫
      eqToIso (by congr 1 <;> simp [sub_eq_add_neg])
  let b := (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).preimage (e.hom≫a)
  have hb : F.map b=e.hom≫a :=
    (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).map_preimage _
  refine ⟨b,?_⟩
  have he : lambdaMultiply 1 b=e.inv≫lambdaPow 1 (Smn m w)≫b := by
    unfold lambdaMultiply
    change eqToHom (by congr 1 <;> simp [sub_eq_add_neg]) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0 ≫
      lambdaPow 1 (Smn m w) ≫ b =
      (eqToHom (by congr 1 <;> simp [sub_eq_add_neg]) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0) ≫
      lambdaPow 1 (Smn m w) ≫ b
    exact (Category.assoc _ _ _).symm
  rw [he]
  rw [←lambdaPow_naturality 1 b]
  change e.inv≫F.map b≫lambdaPow 1 X=z
  rw [hb]
  simp only [Category.assoc,e.inv_hom_id_assoc]
  exact ha


private theorem alpha_exists_from_finite_frames_sphere_zero_weight_label_14_139 {D : Model H M Syn}
    (BHS : EInftyInput D) (x : E2 H SphereSpectrum 14 139)
    (a : BiHom (139-14) (139-0) (S_0_0 : Syn))
    (ha : Detects D.sphereConvergence (14,139,139-0) (D.sphereE2 14 139 0 x) a) :
    D.sphereFirstQuotient 14 139 (quotientClass 1 a)=x := by
  classical
  let y := D.sphereFirstQuotient 14 139 (quotientClass 1 a)
  have hd := alpha_exists_from_finite_frames_detected_map (D:=D) .sphere (.quotient 1 .sphere)
    (XModLambdaN.incl (S_0_0 : Syn) 1) (14,139,139-0) _ a ha
  have hd' := D.comparisonCompatible.first_quotient 14 139 y
  have hy : (D.sphereFirstQuotient 14 139).symm y=quotientClass 1 a := by
    exact (D.sphereFirstQuotient 14 139).symm_apply_apply _
  rw [hy] at hd'
  obtain ⟨e,he,hf⟩ := alpha_exists_from_finite_frames_detects_infinity_equal (.quotient 1 .sphere) (14,139,139-0)
    (quotientClass 1 a) _ _ hd hd'
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (14,139,139-0)
    (D.quotientLabel 1 14 139 0 x) e at he
  change HasInfinityRepresentative (D.family.quotient (S_0_0 : Syn) 1) 2 (14,139,139-0)
    (D.quotientLabel 1 14 139 0 y) e at hf
  let g := XModLambdaN.map D.nu.unitIso.inv 1
  have he' := alpha_exists_from_finite_frames_family_infinity_representative_map g (14,139,139-0) _ _ he
  have hf' := alpha_exists_from_finite_frames_family_infinity_representative_map g (14,139,139-0) _ _ hf
  have hlx := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 1 0 14 139 x
  have hly := alpha_exists_from_finite_frames_sphere_quotient_label_to_nu (D:=D) 1 0 14 139 y
  change familyPageMap D.family g 2 (14,139,139-0) (D.quotientLabel 1 14 139 0 x)=_ at hlx
  change familyPageMap D.family g 2 (14,139,139-0) (D.quotientLabel 1 14 139 0 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  let xx : PageRepresentatives.cycles H SphereSpectrum (1-139+(139-0)) (14,139) :=
    ⟨x,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
  let yy : PageRepresentatives.cycles H SphereSpectrum (1-139+(139-0)) (14,139) :=
    ⟨y,by simp only [sub_zero,sub_add_cancel,PageRepresentatives.cycles_one,Submodule.mem_top]⟩
  have hxq := (BHS.labels.1 .sphere 1 (by decide) (14,139) 0 (by decide) xx _).mp he'
  have hyq := (BHS.labels.1 .sphere 1 (by decide) (14,139) 0 (by decide) yy _).mp hf'
  have heq := hxq.symm.trans hyq
  change NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (14,139)) xx =
    NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (14,139)) yy at heq
  have hz : NestedQuotient.projection _ (PageRepresentatives.boundaries H SphereSpectrum 1 (14,139)) (xx-yy)=0 := by rw [map_sub,heq,sub_self]
  have hm := (NestedQuotient.projection_eq_zero (xx-yy)).mp hz
  change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (14,139) at hm
  have ht : 1+139-(139-0)=1 := by omega
  change x-y∈PageRepresentatives.boundaries H SphereSpectrum 1 (14,139) at hm
  rw [PageRepresentatives.boundaries_one,Submodule.mem_bot] at hm
  exact (sub_eq_zero.mp hm).symm


private theorem alpha_exists_from_finite_frames_eta_correction_lambda_divisible {D : Model H M Syn}
    (BHS : EInftyInput D)
    (η : BiHom 1 2 (S_0_0 : Syn)) (c : BiHom 124 137 (S_0_0 : Syn))
    (x : E2 H SphereSpectrum 13 137)
    (hη : D.sphereFirstQuotient 1 2 (quotientClass 1 η)=Sphere.Internal.hi H M 1)
    (hc : D.sphereFirstQuotient 13 137 (quotientClass 1 c)=x)
    (hp : Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137) (Sphere.Internal.hi H M 1) x=0) :
    ∃ b : BiHom 125 140 (S_0_0 : Syn), lambdaMultiply 1 b=sphereAction η c := by
  classical
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
  have hc0 : lambdaMultiply 0 c=c := by
    have hc := D.shiftCoherence.right_unit (124,137) (S_0_0 : Syn)
    have he : (SyntheticCategory.biShift_comp (124,137) (0,0)).hom.app (S_0_0 : Syn)=
        SyntheticCategory.biShift_zero.hom.app (Smn 124 137 : Syn) := by
      change (biShiftAddIso (124,137) (0,0) (124,137) (by decide)).hom.app _=_ at hc
      simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
        eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
    dsimp only [lambdaMultiply,lambdaPow]
    simp only [Nat.cast_zero,neg_zero,sub_zero,eqToHom_refl,Category.id_comp]
    rw [←he]
    change (SyntheticCategory.biShift_comp (124,137) (0,0)).inv.app (S_0_0 : Syn) ≫
      (SyntheticCategory.biShift_comp (124,137) (0,0)).hom.app (S_0_0 : Syn) ≫ c=c
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
  have hηd := D.comparisonCompatible.homotopy_lambda 1 2 0 η
  rw [hη0,hη] at hηd
  have hcd := D.comparisonCompatible.homotopy_lambda 13 137 0 c
  rw [hc0,hc] at hcd
  have hd := D.multiplicationCompatible 1 2 13 137 0 0 (Sphere.Internal.hi H M 1) x η c hηd hcd
  change Detects D.sphereConvergence (14,139,139-0)
    (D.sphereE2 14 139 0 (Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137) (Sphere.Internal.hi H M 1) x))
    (sphereAction η c) at hd
  rw [hp] at hd
  have hfirst := alpha_exists_from_finite_frames_sphere_zero_weight_label_14_139 BHS 0 (sphereAction η c) hd
  have hzero : quotientClass 1 (sphereAction η c)=0 := by
    apply (D.sphereFirstQuotient 14 139).injective
    exact hfirst.trans (map_zero (D.sphereFirstQuotient 14 139)).symm
  exact alpha_exists_from_finite_frames_lambda_one_division_of_quotient_zero 125 140 (sphereAction η c) hzero


private theorem alpha_exists_from_finite_frames_sphere_first_label_transport {D : Model H M Syn} (s t : ℤ)
    (x : E2 H SphereSpectrum s t) :
    D.sphereFirstQuotient s t
      (firstLabel D .sphere s t x ≫ XModLambdaN.map
        (SyntheticCategory.biShift_zero.hom.app (D.nu.functor.obj SphereSpectrum) ≫ D.nu.unitIso.hom) 1)=x := by
  classical
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


private theorem alpha_exists_from_finite_frames_sphere_permanent_first_quotient_lift {D : Model H M Syn}
    (synthetic : SyntheticInputs D) (s t : ℤ) (x : E2 H SphereSpectrum s t)
    (hx : IsPermanentCycle (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) (s,t) x) :
    ∃ a : BiHom (t-s) t (S_0_0 : Syn), D.sphereFirstQuotient s t (quotientClass 1 a)=x := by
  classical
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
  exact alpha_exists_from_finite_frames_sphere_first_label_transport s t x


private theorem alpha_exists_from_finite_frames_alpha_h0_rho_zero {D : Model H M Syn}
    (hzero : ∀ a : BiHom 123 130 (XModLambdaN (S_0_0 : Syn) 9),
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 16 a → a=0)
    (h0 : BiHom 0 1 (S_0_0 : Syn))
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 17
      (lambdaMultiply 3 (sphereAction h0 a))) :
    lambdaMultiply 3 (sphereAction h0 (a≫(D.quotientTower S_0_0).rho 9 11 (by decide)))=0 := by
  classical
  apply hzero
  have h := alpha_exists_from_finite_frames_filtration_postcompose (D:=D) ((D.quotientTower S_0_0).rho 9 11 (by decide))
    17 123 130 (lambdaMultiply 3 (sphereAction h0 a)) ha
  have h16 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 16
      (lambdaMultiply 3 (sphereAction h0 a)≫(D.quotientTower S_0_0).rho 9 11 (by decide)) :=
    towerFiltrationSubmodule_antitone _ _ _ (by decide : (16:ℤ)≤17) h
  simpa only [lambdaMultiply,sphereAction,Category.assoc] using h16


private theorem alpha_exists_from_finite_frames_alpha_correction_sum (D : Model H M Syn)
    (η : BiHom 1 2 (S_0_0 : Syn))
    (c13 : BiHom 124 137 (S_0_0 : Syn))
    (c14 : BiHom 124 138 (S_0_0 : Syn))
    (c15 : BiHom 124 139 (S_0_0 : Syn))
    (b : BiHom 125 140 (S_0_0 : Syn)) (hb : lambdaMultiply 1 b=sphereAction η c13)
    (b13 b14 b15 : Bool) :
    ∃ (a2 : BiHom 124 137 (XModLambdaN (S_0_0 : Syn) 9))
      (a3 : BiHom 125 140 (XModLambdaN (S_0_0 : Syn) 9)),
      (if b13 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 6 (quotientClass 9 c13)) else 0)+
      (if b14 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 7 (quotientClass 9 c14)) else 0)+
      (if b15 then (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 8 (quotientClass 9 c15)) else 0)=lambdaMultiply 6 a2 ∧
      sphereAction η a2=lambdaMultiply 1 a3 := by
  classical
  have lam_add {m w : ℤ} {X : Syn} (n : ℕ) (a b : BiHom m w X) :
      lambdaMultiply n (a+b)=lambdaMultiply n a+lambdaMultiply n b := by
    simp only [lambdaMultiply,Preadditive.comp_add]
  have lam_if {m w : ℤ} {X : Syn} (n : ℕ) (a : BiHom m w X) (b : Bool) :
      lambdaMultiply n (if b then a else 0)=(if b then lambdaMultiply n a else 0) := by
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte,lambdaMultiply,comp_zero]
  have act_add {m w : ℤ} {X : Syn} (a b : BiHom m w X) :
      sphereAction η (a+b)=sphereAction η a+sphereAction η b := by
    simp only [sphereAction,Preadditive.comp_add]
  have act_if {m w : ℤ} {X : Syn} (a : BiHom m w X) (b : Bool) :
      sphereAction η (if b then a else 0)=(if b then sphereAction η a else 0) := by
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte,sphereAction,comp_zero]
  let c : BiHom 124 137 (S_0_0 : Syn) := (if b13 then c13 else 0)+
    (if b14 then (show BiHom 124 137 (S_0_0 : Syn) from lambdaMultiply 1 c14) else 0)+
    (if b15 then (show BiHom 124 137 (S_0_0 : Syn) from lambdaMultiply 2 c15) else 0)
  let d : BiHom 125 140 (S_0_0 : Syn) := (if b13 then b else 0)+
    (if b14 then (show BiHom 125 140 (S_0_0 : Syn) from sphereAction η c14) else 0)+
    (if b15 then (show BiHom 125 140 (S_0_0 : Syn) from lambdaMultiply 1 (sphereAction η c15)) else 0)
  have hlam : lambdaMultiply 6 c=
      (if b13 then (show BiHom 124 131 (S_0_0 : Syn) from lambdaMultiply 6 c13) else 0)+
      (if b14 then (show BiHom 124 131 (S_0_0 : Syn) from lambdaMultiply 7 c14) else 0)+
      (if b15 then (show BiHom 124 131 (S_0_0 : Syn) from lambdaMultiply 8 c15) else 0) := by
    dsimp only [c]
    rw [lam_add,lam_add,lam_if,lam_if,lam_if,alpha_exists_from_finite_frames_lambda_six_one D,alpha_exists_from_finite_frames_lambda_six_two D]
  have heta : sphereAction η c=lambdaMultiply 1 d := by
    dsimp only [c,d]
    rw [act_add,act_add,act_if,act_if,act_if,lam_add,lam_add,lam_if,lam_if,lam_if,
      hb,alpha_exists_from_finite_frames_sphere_action_right_one D,alpha_exists_from_finite_frames_sphere_action_right_two_as_ones D]
  refine ⟨quotientClass 9 c,quotientClass 9 d,?_,?_⟩
  · have hh := congrArg (fun a=>a≫XModLambdaN.incl (S_0_0 : Syn) 9) hlam
    simp only [Preadditive.add_comp,ite_comp,zero_comp] at hh
    simpa only [lambdaMultiply,quotientClass,Category.assoc] using hh.symm
  · have hh := congrArg (fun a=>a≫XModLambdaN.incl (S_0_0 : Syn) 9) heta
    simpa only [lambdaMultiply,sphereAction,quotientClass,Category.assoc] using hh


private theorem alpha_exists_from_finite_frames_alpha_computation_inputs {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}
    (I : KIP126.Computation.Route.Inputs D L G) (facts : Derived.SphereFacts I.realization) :
    I.realization.sphere 10 134 U∈PageRepresentatives.cycles H SphereSpectrum 8 (10,134) ∧
    HasDifferential (sequence D .sphere) 2 (8,133) (10,134)
      (I.realization.sphere 8 133 (atom .x_125_8))
      (Sphere.Internal.product H M (s:=1) (t:=2) (s':=9) (t':=132) (Sphere.Internal.hi H M 1)
        (I.realization.sphere 9 132 V)+I.realization.sphere 10 134 U) ∧
    Sphere.Internal.product H M (s:=1) (t:=2) (s':=13) (t':=137) (Sphere.Internal.hi H M 1)
      (I.realization.sphere 13 137 correction)=0 := by
  classical
  constructor
  · apply PageRepresentatives.permanentCycles_le_cycles H SphereSpectrum (10,134) 8
    obtain ⟨z,hz,_⟩ := facts.u_permanent
    exact ⟨z,hz⟩
  constructor
  · have h := (facts.d2_x_125_8).toHasDifferential
    have hp := I.products ⟨1,2,9,132⟩ (by simp [Raw.products]) dataH1 V
    dsimp only at hp
    change HasDifferential (sequence D .sphere) 2 (8,133) (10,134)
      (I.realization.sphere 8 133 (atom .x_125_8))
      (I.realization.sphere 10 134 (mulAt dataH1 V+U)) at h
    rw [map_add,hp,I.labels.h1] at h
    exact h
  · have hp := I.products ⟨1,2,13,137⟩ (by simp [Raw.products]) dataH1 correction
    dsimp only at hp
    rw [I.labels.h1] at hp
    exact hp.symm.trans facts.h1_correction_zero


private theorem alpha_exists_from_finite_frames
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}
    (I : KIP126.Computation.Route.Inputs D L G) (BHS : SyntheticInputs D) (facts : Derived.SphereFacts I.realization)
    (algebra : AlgebraData D) (binding : AlgebraBinding D algebra)
    (η : BiHom 1 2 (S_0_0 : Syn)) (hη : EtaChoice M D.toModelData η)
    (h0 : BiHom 0 1 (S_0_0 : Syn))
    (h0filtration : ∀ (a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11)),
      FiniteDetected D 11 (by decide) 9 132 0 (I.realization.sphere 9 132 V) a →
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 17 (lambdaMultiply 3 (sphereAction h0 a)))
    (h0zero : ∀ a : BiHom 123 130 (XModLambdaN (S_0_0 : Syn) 9),
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 16 a → a=0)
    (hp14 : IsPermanentCycle (sequence D .sphere) (14,138) (I.realization.basis .sphere 14 138 2))
    (hp15 : IsPermanentCycle (sequence D .sphere) (15,139)
      (I.realization.basis .sphere 15 139 1+I.realization.basis .sphere 15 139 3)) :
    ∃ a : BiHom 123 132 (XModLambdaN (S_0_0 : Syn) 11),
      AlphaOneProperties D η h0 (I.realization.sphere 10 134 U) (I.realization.sphere 9 132 V) a := by
  classical
  obtain ⟨a,ha11,ha9⟩ := alpha_exists_from_finite_frames_alpha_one_detected_pair BHS.eInfty _ facts.v_to_e12
  obtain ⟨hU,hd,hprod⟩ := alpha_exists_from_finite_frames_alpha_computation_inputs I facts
  have hpc : IsPermanentCycle (sequence D .sphere) (13,137) (I.realization.sphere 13 137 correction) := by
    obtain ⟨z,hz,_⟩ := facts.correction_permanent
    exact ⟨z,hz⟩
  obtain ⟨c13,hc13⟩ := alpha_exists_from_finite_frames_sphere_permanent_first_quotient_lift BHS 13 137 _ hpc
  obtain ⟨c14,hc14⟩ := alpha_exists_from_finite_frames_sphere_permanent_first_quotient_lift BHS 14 138 _ hp14
  obtain ⟨c15,hc15⟩ := alpha_exists_from_finite_frames_sphere_permanent_first_quotient_lift BHS 15 139 _ hp15
  obtain ⟨b,hb⟩ := alpha_exists_from_finite_frames_eta_correction_lambda_divisible BHS.eInfty η c13 _ hη hc13 hprod
  have h14 : I.realization.basis .sphere 14 138 2∈PageRepresentatives.cycles H SphereSpectrum 4 (14,138) :=
    PageRepresentatives.permanentCycles_le_cycles H SphereSpectrum (14,138) 4 hp14
  have h15 : I.realization.basis .sphere 15 139 1+I.realization.basis .sphere 15 139 3∈PageRepresentatives.cycles H SphereSpectrum 3 (15,139) :=
    PageRepresentatives.permanentCycles_le_cycles H SphereSpectrum (15,139) 3 hp15
  refine ⟨a,ha11,ha9,?_,?_⟩
  · intro u hu
    have herr := alpha_exists_from_finite_frames_alpha_error_filtration_thirteen BHS algebra binding η hη _ _ _ hU hd
      facts.e5_stem124_af11 facts.e4_stem124_af12 a ha11 u hu
    obtain ⟨b13,b14,b15,hbits⟩ := alpha_exists_from_finite_frames_alpha_three_layer_restriction I BHS.eInfty facts h14 h15
      c13 hc13 c14 hc14 c15 hc15 _ herr
    obtain ⟨a2,a3,hs,heta⟩ := alpha_exists_from_finite_frames_alpha_correction_sum (D:=D) η c13 c14 c15 b hb b13 b14 b15
    refine ⟨a2,a3,?_,heta⟩
    have he := hbits.trans hs
    have hrho :
        ((show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) from lambdaMultiply 3 (sphereAction η a))-
          (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 11) from lambdaMultiply 3 (quotientClass 11 u)))≫
            (D.quotientTower S_0_0).rho 9 11 (by decide) =
        (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 3
          (sphereAction η (a≫(D.quotientTower S_0_0).rho 9 11 (by decide))))-
          (show BiHom 124 131 (XModLambdaN (S_0_0 : Syn) 9) from lambdaMultiply 3 (quotientClass 9 u)) := by
      simp only [Preadditive.sub_comp,lambdaMultiply,sphereAction,quotientClass,Category.assoc,
        FiniteLambdaQuotientTower.rho_quotient]
    rw [hrho] at he
    exact sub_eq_iff_eq_add'.mp he
  · exact alpha_exists_from_finite_frames_alpha_h0_rho_zero h0zero h0 a (h0filtration a ha11)

end

end AlphaOneExistenceProof

local notation "D" => routeModel
local notation "M" => standardMilnorCooperations
local notation "L" => routeLabels
local notation "I" => routeComputation
local notation "η" => routeEta
local notation "h₀" => routeLiterature.toda.h0

abbrev eV := (I).realization.sphere 9 132 KIP126.Computation.Near126.V
abbrev eCorrection := (I).realization.sphere 13 137 KIP126.Computation.Near126.correction

open KIP126.LinE2 KIP126.Computation.Near126 in
/-- The Q9 d3 actually used to eliminate the other AF13 error direction.
The weight131 target is nonzero on E3, not just an E2 label with exponent8. -/
theorem ninth_quotient_error_d3 :
    FiniteNonzeroDifferential D 9 3 13 137 16 139 6 8
      ((I).realization.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12)))
      ((I).realization.sphere 16 139 (mulAt dataH1 (atom .x_122_15_2))) := by
  exact finite_last_nonzero routeLiterature.synthetic 9 3 6 (by decide) (by decide)
    13 137 _ _
    (KIP126.Computation.Route.sphere_facts routeComputation sphereVanishing).d3_h4_x_109_12

open KIP126.LinE2 KIP126.Computation.Near126 in
/-- Q11, weight130: both common E7 representatives and target nonzero
are required. BHS lifting of the classical equation alone is insufficient. -/
theorem eleventh_quotient_candidate_d7 :
    FiniteNonzeroDifferential D 11 7 11 134 18 140 4 10
      ((I).realization.sphere 11 134 d7Source)
      ((I).realization.sphere 18 140 (mulAt dataH1 (atom .x_121_17))) := by
  exact finite_last_nonzero routeLiterature.synthetic 11 7 4 (by decide) (by decide)
    11 134 _ _
    (KIP126.Computation.Route.sphere_facts routeComputation sphereVanishing).d7_source

open KIP126.LinE2 KIP126.Computation.Near126 in
/-- The other Q11 weight130 candidate supports a nonzero E3 differential.
Its target has the same degree as the d7 target but a different E2 label. -/
theorem eleventh_quotient_candidate_d3 :
    FiniteNonzeroDifferential D 11 3 15 138 18 140 8 10
      ((I).realization.sphere 15 138 (mulAt h0Sq (atom .x_123_13_2)))
      ((I).realization.sphere 18 140 (mulAt h0Sq (atom .x_122_16))) := by
  exact finite_last_nonzero routeLiterature.synthetic 11 3 8 (by decide) (by decide)
    15 138 _ _
    (KIP126.Computation.Route.sphere_facts routeComputation sphereVanishing).d3_h0Sq_x_123_13_2

set_option backward.isDefEq.respectTransparency false in
private theorem sphere_quotient_page_zero (q : ℕ) (hq : 0 < q)
    (r s t w : ℤ) (hr : 2 ≤ r) (hwindow : t < w ∨ (q : ℤ) ≤ t - w) :
    Subsingleton (((D).family.quotient (S_0_0 : KIP126.Def.standardRouteInput.Syn) q).Page
      r (s,t,w)) := by
  classical
  let Q := (D).quotientFunctoriality.functor q

  let e := (D).family.functor.mapIso (Q.mapIso (D).nu.unitIso)

  have hz := routeLiterature.synthetic.finite_quotient_page_vanishing
    .sphere q hq r s t w hr hwindow

  let i := e.inv.pageMap r (s,t,w)

  let j := e.hom.pageMap r (s,t,w)

  have hij : i ≫ j = 𝟙 _ := by
    classical
    dsimp only [i, j]
    rw [← SpectralSequenceMorphism.pageMap_comp, e.inv_hom_id,
      SpectralSequenceMorphism.pageMap_id]

  have hi : Function.Injective i := by
    classical
    intro x y hxy
    have hh := congrArg j hxy
    simpa only [← CategoryTheory.comp_apply, hij, ModuleCat.id_apply] using hh

  have hsource : Subsingleton ((KIP126.Core.SpectralSequence.Page
      ((D).family.functor.obj (XModLambdaN ((D).nu.functor.obj SphereSpectrum) q))
      r (s,t,w)) : ModuleCat ℤ) := by
    classical
    simpa only [KIP126.Core.SpectralSequence.Page, (D).family.firstPage,
      SyntheticAdamsFamily.nuQuotient, SyntheticAdamsFamily.quotient,
      SyntheticAdamsFamily.obj, SyntheticAdamsSS.Page, ClassicalObject.obj] using hz

  have hz' : Subsingleton ((KIP126.Core.SpectralSequence.Page
      ((D).family.functor.obj (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) q))
      r (s,t,w)) : ModuleCat ℤ) := ⟨fun x y => hi (hsource.elim _ _)⟩

  simpa only [KIP126.Core.SpectralSequence.Page, (D).family.firstPage,
      SyntheticAdamsFamily.nuQuotient, SyntheticAdamsFamily.quotient,
      SyntheticAdamsFamily.obj, SyntheticAdamsSS.Page, ClassicalObject.obj] using hz'


/-- In Q9 both preceding targets have exponent10, so this WHOLE component
vanishes on every finite page. Transport of the BHS nu(S) statement uses
the same unit isomorphism and actual quotient functor. -/
theorem ninth_quotient_candidate_target_zero (r : ℤ) (hr : 2 ≤ r) :
    Subsingleton (((D).family.quotient (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9).Page
      r (18,140,130)) := by
  exact sphere_quotient_page_zero 9 (by decide) r 18 140 130 hr
    (Or.inr (by norm_num))

/-- The actual rho page map kills these Q11 targets in Q9. This records
the map used in Lemma x1239, rather than only comparing two dimensions. -/
theorem rho_to_ninth_kills_candidate_target (r : ℤ) (hr : 2 ≤ r)
    (y : ((D).family.quotient (S_0_0 : KIP126.Def.standardRouteInput.Syn) 11).Page
      r (18,140,130)) :
    familyPageMap (D).family ((D).quotientTower S_0_0 |>.rho 9 11 (by decide))
      r (18,140,130) y = 0 := by
  exact (ninth_quotient_candidate_target_zero r hr).elim _ _

/-- `prop:possible_h_6_sq`: complete stem124 staircase reconstruction,
including the negative-filtration half-plane, before passing to homotopy.
This is E-infinity vanishing, not a false E2 vanishing assertion. -/
theorem classical_stem124_einfty_below_ten (s : ℤ) (hs : s < 10) :
    Subsingleton ((adamsTowerInternalSpectralSequence standardFoundation.hf2.unit
      SphereSpectrum).ssData (s,s+124)).eInfty := by
  set_option backward.isDefEq.respectTransparency false in
  set_option maxRecDepth 10000 in
    let E := adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum
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
        standardFoundation.hf2.unit SphereSpectrum 2 s (s+124) hneg)
    have hs0 : 0 ≤ s := by omega
    by_cases hsmall : s ≤ 5
    · have hd : (⟨.sphere,s.toNat,(s+124).toNat,[]⟩ : KIP126.Computation.Route.Raw.Degree) ∈ KIP126.Computation.Route.Raw.degrees := by
        interval_cases s <;> simp [KIP126.Computation.Route.Raw.degrees]
      obtain ⟨e,_⟩ := routeComputation.basis _ hd
      change KIP126.Computation.Route.Page routeModel .sphere s.toNat (s+124).toNat ≃ₗ[ℤ] (Fin 0 →₀ KIP126.Core.Algebra.F2) at e
      have he : Subsingleton (KIP126.Computation.Route.Page routeModel .sphere s.toNat (s+124).toNat) := e.injective.subsingleton
      apply collapse 2
      simpa only [KIP126.Computation.Route.Page,KIP126.Computation.Route.sequence,KIP126.Computation.Route.object,E,standardFoundation,
      KIP126.Def.StageInput.witness, KIP126.Implementation.foundation, KIP126.Foundation.FoundationInput.toStandard,Int.toNat_of_nonneg hs0,
        Int.toNat_of_nonneg (by omega : 0 ≤ s+124)] using he
    have hfinite := stem124_finite_pages routeComputation
    change Subsingleton (E.Page 6 (6,130)) ∧ Subsingleton (E.Page 6 (7,131)) ∧
      Subsingleton (E.Page 3 (8,132)) ∧ Subsingleton (E.Page 4 (9,133)) at hfinite
    interval_cases s
    · exact collapse 6 hfinite.1
    · exact collapse 6 hfinite.2.1
    · exact collapse 3 hfinite.2.2.1
    · exact collapse 4 hfinite.2.2.2

/-- Full AF10 exhaustion in `prop:possible_h_6_sq`: incoming d2/d4,
the remaining outgoing d5, and U's nonzero permanence are all needed. -/
theorem classical_stem124_af10_generated :
    ClassicalInfinityGenerated 10 134 ((L).U M) := by
  have h := stem124_af10_exhaustion routeComputation sphereVanishing
  rw [(KIP126.Computation.Route.route_expression_labels routeComputation).2.1] at h
  exact h

/-- Full AF13 exhaustion. The E2 group has four basis vectors; only the
permanent correction remains at infinity. Finite Reaches1000 uses V's
independent tail before it may supply the infinite representative. -/
theorem classical_stem124_af13_generated :
    ClassicalInfinityGenerated 13 137 eCorrection := by
  exact stem124_af13_exhaustion routeComputation sphereVanishing

/-- The filtration bound in Proposition 7.8 combines classical vanishing
with BHS boundary stabilization at weight128. The remaining incoming sources
vanish, excluding synthetic lambda-torsion in these lower filtrations. -/
theorem theta5_square_filtration_ten
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (htheta : ThetaChoice M (D).toModelData theta) :
    FiltrationAtLeast (nuCoefficientUnit standardFoundation.hf2.unit (D).nu) 10
      (sphereProduct theta theta) := by
  exact stem124_weight128_filtration_ten routeLiterature.synthetic I
    classical_stem124_einfty_below_ten (sphereProduct theta theta)

/-- The three exhaustive branches in Proposition 7.8, retaining a real
lambda preimage in the third branch and nonzero leading detection in the
first two. This does not assume which branch actually occurs. -/
theorem theta5_square_three_cases
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (htheta : ThetaChoice M (D).toModelData theta) :
    C4At M (D).toModelData L theta ∨
      SphereDetected D 13 137 9 eCorrection (sphereProduct theta theta) ∨
      ∃ a : BiHom 124 138 (S_0_0 : KIP126.Def.standardRouteInput.Syn),
        lambdaMultiply 10 a = sphereProduct theta theta := by
  have h := theta_three_cases_from_frames routeComputation routeLiterature.synthetic
    ((L).U M) eCorrection classical_stem124_af10_generated classical_stem124_af13_generated
    (KIP126.Computation.Route.sphere_facts routeComputation sphereVanishing).e5_stem124_af11
    (KIP126.Computation.Route.sphere_facts routeComputation sphereVanishing).e4_stem124_af12
    (sphereProduct theta theta) (theta5_square_filtration_ten theta htheta)
  exact h

/-- At weight130 and stem123 the BHS finite-quotient window for Q9 is
7<=s<=15. Every graded piece at s>=16 vanishes. Actual separatedness
then kills the filtration, without asserting lambda^9 acts as zero on Q9. -/
theorem ninth_quotient_stem123_weight130_filtration16_zero
    (a : BiHom 123 130 (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9))
    (ha : FiltrationAtLeast (nuCoefficientUnit standardFoundation.hf2.unit (D).nu) 16 a) :
    a = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    apply ((D).quotientConvergence 9 (by decide)).eq_zero_of_eInfty_isZero_ge
      16 123 130 ((D).homotopySeparated (.quotient 9 .sphere) 123 130) ?_ a ha
    intro j hj
    let E := (((D).family.quotient (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9).sequence.ssData
      (j, 123+j, 130))
    have hzero : Subsingleton (E.page 0) :=
      sphere_quotient_page_zero 9 (by decide) 2 j (123+j) 130 (by decide)
        (Or.inr (by omega))
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun x y => ?_⟩
    haveI : Epi (E.pageπ ⊤) := inferInstanceAs
      (Epi (CategoryTheory.Limits.cokernel.π _))
    obtain ⟨x', rfl⟩ := (ModuleCat.epi_iff_surjective (E.pageπ ⊤)).mp inferInstance x
    obtain ⟨y', rfl⟩ := (ModuleCat.epi_iff_surjective (E.pageπ ⊤)).mp inferInstance y
    exact E.infinity_projection_eq_of_page_projection_eq 0 x' y' (hzero.elim _ _)

/-- The calculation is performed in Q11: its two weight130 candidates
support the nonzero d7(lambda^4 d7Source) and d3(lambda^8 h0^2 x123,13,2).
Those targets disappear in Q9, so doing the calculation there first would
lose the needed exclusion. All representatives with this detector qualify. -/
theorem alpha_one_h0_filtration_seventeen
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 11))
    (ha : FiniteDetected D 11 (by decide) 9 132 0 eV a) :
    FiltrationAtLeast (nuCoefficientUnit standardFoundation.hf2.unit (D).nu) 17
      (lambdaMultiply 3 (sphereAction h₀ a)) := by
  exact alpha_h0_filtration_from_finite_window routeComputation routeLiterature.synthetic
    literature.bindings.route.algebra literature.bindings.route.algebraBinding h₀ eV a ha

/-- `lem:x_123_9`: this includes the nonzero Q9 d3 on lambda^6 h4x109,12,
all error-space exhaustion, and rho's actual preservation of filtration.
The three exact homotopy equations are not inferred from leading Ext
relations alone. They remain internal proof obligations here. -/
theorem alpha_one_exists :
    ∃ a11 : BiHom 123 132 (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 11),
      AlphaOneProperties D η h₀ ((L).U M) eV a11 := by
  obtain ⟨hp14,hp15⟩ := full_staircase_high_cycles computation sphereVanishing
  have h := alpha_exists_from_finite_frames routeComputation routeLiterature.synthetic
    (KIP126.Computation.Route.sphere_facts routeComputation sphereVanishing)
    literature.bindings.route.algebra literature.bindings.route.algebraBinding
    routeEta routeLiterature.classical.hopf.1 routeLiterature.toda.h0
    alpha_one_h0_filtration_seventeen
    ninth_quotient_stem123_weight130_filtration16_zero hp14 hp15
  rw [(KIP126.Computation.Route.route_expression_labels routeComputation).2.1] at h
  exact h

end
end KIP126.Main.Solution.Route.Section7
