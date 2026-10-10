import KIP126.Def.ClassicalAdams.SphereClasses.Product.Proofs
import KIP126.LinProgram.Model.RelationCertificates
import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
import KIP126.Def.SpectralSequence.Computation.Proofs
import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
import KIP126.LinProgram.Model.Classes.Proofs
import KIP126.Main.Solution.Computation.Route.Consequences
import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
import KIP126.Def.SpectralSequence.Permanence.Proofs
import KIP126.Def.ClassicalAdams.Convergence.Tower.Predicates

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

/-- The two existing filtration spellings are the images of the SAME tower
maps on the SAME sphere homotopy groups. Strong convergence's Hausdorff
clause therefore supplies the exact separation premise used below. This
adapter assumes the actual strong-convergence theorem, not merely an
arbitrary associated-graded isomorphism. -/
theorem classical_sphere_separated_of_strong_convergence
    (S : IsAdamsTowerStronglyConvergent H.unit (SphereSpectrum (C := C))) :
    ClassicalSphereSeparated H := by
  intro n a ha
  let e := ModuleCat.subobjectModule (towerAbutment (SphereSpectrum (C := C)) n)
  have hz := S.separated n (e.symm (Submodule.span ℤ {a})) (fun s => by
    apply e.symm.monotone
    apply Submodule.span_le.mpr
    intro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    obtain ⟨y, hy⟩ := ha s.toNat
    refine ⟨y, ?_⟩
    change y ≫ adamsTowerMap H.unit SphereSpectrum 0 s.toNat _ = b
    change y ≫ adamsTowerMap H.unit SphereSpectrum 0 (s.toNat : ℤ).toNat _ = b at hy
    simpa only [Int.toNat_natCast] using hy)
  have hspan : Submodule.span ℤ {a} = (⊥ : Submodule ℤ (HomotopyGroup n SphereSpectrum)) := by
    have h := congrArg e hz
    rw [e.apply_symm_apply, e.map_bot] at h
    exact h
  have hm : a ∈ Submodule.span ℤ ({a} : Set (HomotopyGroup n SphereSpectrum)) :=
    Submodule.subset_span (Set.mem_singleton a)
  simpa [hspan] using hm

variable {D : Model H M Syn} {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}

/-- Tail outside the selected sphere file.  In positive stem n <= 127,
filtration s >= 66 already lies in the uniform vanishing region.  The
125-stem specialization below uses the sharper s >= 65 bound. -/
theorem sphere_page_zero_above_uniform_bound (V : SphereVanishingLine H)
    (r s n : ℤ) (hr : 2 ≤ r) (hn : 0 < n) (hn' : n ≤ 127) (hs : 66 ≤ s) :
    Subsingleton ((sequence D .sphere).Page r (s,s+n)) := by
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum
    2 r s (s+n) (by omega) hr (V s (s+n) (by omega) (by omega))

/-- At n=125 the exact arithmetic is 125 < 2*65-3=127.  No claim is
inferred merely from the absence of rows past the file's t=261 cutoff. -/
theorem sphere_page_zero_stem125_tail (V : SphereVanishingLine H)
    (r s : ℤ) (hr : 2 ≤ r) (hs : 65 ≤ s) :
    Subsingleton ((sequence D .sphere).Page r (s,s+125)) := by
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum
    2 r s (s+125) (by omega) hr (V s (s+125) (by omega) (by omega))

/-- Late outgoing differentials from all relevant positive-stem classes
have zero actual target page.  This supplies the missing infinite tail of
an honest finite `ReachesPage 1000` record. -/
theorem late_outgoing_target_zero (V : SphereVanishingLine H)
    (s t : ℕ) (hn : 1 < (t : ℤ) - s) (hn' : (t : ℤ) - s ≤ 127)
    (r : ℤ) (hr : 1000 ≤ r) :
    Subsingleton ((sequence D .sphere).Page r ((s : ℤ)+r,(t : ℤ)+r-1)) := by
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum
    2 r ((s : ℤ)+r) ((t : ℤ)+r-1) (by omega) (by omega)
    (V _ _ (by omega) (by omega))

/-- A single finite-page common representative, together with eventual
zero outgoing targets, gives a single representative in the actual Z-infinity
intersection.  This conclusion intentionally allows an incoming boundary. -/
theorem permanent_cycle_of_reaches1000 (V : SphereVanishingLine H)
    (s t : ℕ) (hn : 1 < (t : ℤ) - s) (hn' : (t : ℤ) - s ≤ 127)
    (x : E2 H SphereSpectrum s t)
    (hx : ReachesPage (sequence D .sphere) 1000 (s,t) x) :
    IsPermanentCycle (sequence D .sphere) (s,t) x := by
  apply isPermanentCycle_of_reachesPage (sequence D .sphere) 1000
    (by change (2 : ℤ) ≤ 1000; omega) (s, t) x hx
  intro r hr
  haveI : Subsingleton ((sequence D .sphere).Page r
      (((s : ℤ), (t : ℤ)) + (sequence D .sphere).diffDeg r)) := by
    change Subsingleton ((sequence D .sphere).Page r ((s : ℤ) + r, (t : ℤ) + (r - 1)))
    simpa only [add_sub_assoc] using late_outgoing_target_zero (D := D) V s t hn hn' r hr
  ext y
  exact Subsingleton.elim _ _

/-- Nonzero permanence needs nonzero survival to E1000.  For s<1000 every
later incoming source has negative filtration; the actual tower vanishing
lemma excludes it.  E2 nonzero or `ReachesPage` alone is not this hypothesis. -/
theorem nonzero_permanent_of_survives1000 (V : SphereVanishingLine H)
    (s t : ℕ) (hs : s < 1000)
    (hn : 1 < (t : ℤ) - s) (hn' : (t : ℤ) - s ≤ 127)
    (x : E2 H SphereSpectrum s t)
    (hx : SurvivesTo (sequence D .sphere) 1000 (s,t) x) :
    NonzeroSurvival (sequence D .sphere) (s,t) x := by
  apply nonzeroSurvival_of_survivesTo (sequence D .sphere) 1000
    (by change (2 : ℤ) ≤ 1000; omega) (s, t) x hx
  · intro r hr
    haveI : Subsingleton ((sequence D .sphere).Page r
        (((s : ℤ), (t : ℤ)) + (sequence D .sphere).diffDeg r)) := by
      change Subsingleton ((sequence D .sphere).Page r ((s : ℤ) + r, (t : ℤ) + (r - 1)))
      simpa only [add_sub_assoc] using late_outgoing_target_zero (D := D) V s t hn hn' r hr
    ext y
    exact Subsingleton.elim _ _
  · intro r hr
    haveI : Subsingleton ((sequence D .sphere).Page r
        (((s : ℤ), (t : ℤ)) - (sequence D .sphere).diffDeg r)) :=
      adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
        r ((s : ℤ) - r) ((t : ℤ) - (r - 1)) (by omega)
    ext y
    change (sequence D .sphere).d r _ y = 0
    rw [Subsingleton.elim y 0, map_zero]

section

private theorem u_survives1000_h157 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (4,130) (7,132) (I.realization.basis .sphere 4 130 0) (I.realization.basis .sphere 7 132 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "S0_AdamsE2_ss", 2437⟩ (by
    exact List.mem_of_getElem? (i := 157) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (4,130) (7,132) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h163 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (5,130) (7,131) (I.realization.basis .sphere 5 130 0) (I.realization.basis .sphere 7 131 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 5, 130, [0], 7, 131, [2], "S0_AdamsE2_ss", 2435⟩ (by
    exact List.mem_of_getElem? (i := 163) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,130) (7,131) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h171 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 0) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 3) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3], "S0_AdamsE2_ss", 2492⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h172 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 1) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 1 + I.realization.basis .sphere 10 134 3 + I.realization.basis .sphere 10 134 4) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4], "S0_AdamsE2_ss", 2493⟩ (by
    exact List.mem_of_getElem? (i := 172) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h200 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,133) (11,135) (I.realization.basis .sphere 8 133 0) (I.realization.basis .sphere 11 135 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2629⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,133) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h201 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,133) (10,134) (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "S0_AdamsE2_ss", 2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,133) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem u_survives1000_h249 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (10,134) (I.realization.basis .sphere 10 134 4) := by
  classical
  have hrow := I.results ⟨.sphere, .reaches, 1000, 10, 134, [4], 10, 134, [], "S0_AdamsE2_ss", 2693⟩ (by
    exact List.mem_of_getElem? (i := 249) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [4] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem u_survives1000
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H} (I : Inputs D L G) :
    SurvivesTo (sequence D .sphere) 1000 (10,134) (I.realization.basis .sphere 10 134 4) := by
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
  obtain ⟨e8_133,he8_133⟩ := I.basis ⟨.sphere, 8, 133, ["376,1", "375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 161) (by rfl))
  change E.Page 2 (8,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e8_133
  change ∀i : Fin 2, e8_133.symm (Finsupp.single i 1) = I.realization.basis .sphere 8 133 i.val at he8_133
  have he8_133_0 : e8_133.symm (Finsupp.single 0 1) = I.realization.basis .sphere 8 133 0 := he8_133 0
  have he8_133_1 : e8_133.symm (Finsupp.single 1 1) = I.realization.basis .sphere 8 133 1 := he8_133 1
  obtain ⟨e7_132,he7_132⟩ := I.basis ⟨.sphere, 7, 132, ["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e7_132
  change ∀i : Fin 1, e7_132.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 132 i.val at he7_132
  have he7_132_0 : e7_132.symm (Finsupp.single 0 1) = I.realization.basis .sphere 7 132 0 := he7_132 0
  obtain ⟨e6_131,he6_131⟩ := I.basis ⟨.sphere, 6, 131, ["69,1,76,1", "0,1,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 137) (by rfl))
  change E.Page 2 (6,131) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e6_131
  change ∀i : Fin 2, e6_131.symm (Finsupp.single i 1) = I.realization.basis .sphere 6 131 i.val at he6_131
  have he6_131_0 : e6_131.symm (Finsupp.single 0 1) = I.realization.basis .sphere 6 131 0 := he6_131 0
  have he6_131_1 : e6_131.symm (Finsupp.single 1 1) = I.realization.basis .sphere 6 131 1 := he6_131 1
  obtain ⟨e5_130,he5_130⟩ := I.basis ⟨.sphere, 5, 130, ["340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 126) (by rfl))
  change E.Page 2 (5,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e5_130
  change ∀i : Fin 1, e5_130.symm (Finsupp.single i 1) = I.realization.basis .sphere 5 130 i.val at he5_130
  have he5_130_0 : e5_130.symm (Finsupp.single 0 1) = I.realization.basis .sphere 5 130 0 := he5_130 0
  obtain ⟨e7_131,he7_131⟩ := I.basis ⟨.sphere, 7, 131, ["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e7_131
  change ∀i : Fin 3, e7_131.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 131 i.val at he7_131
  have he7_131_0 : e7_131.symm (Finsupp.single 0 1) = I.realization.basis .sphere 7 131 0 := he7_131 0
  have he7_131_1 : e7_131.symm (Finsupp.single 1 1) = I.realization.basis .sphere 7 131 1 := he7_131 1
  have he7_131_2 : e7_131.symm (Finsupp.single 2 1) = I.realization.basis .sphere 7 131 2 := he7_131 2
  have h157 : HasDifferential E 3 (4,130) (7,132) (I.realization.basis .sphere 4 130 0) (I.realization.basis .sphere 7 132 0) := u_survives1000_h157 I
  have h163 : HasDifferential E 2 (5,130) (7,131) (I.realization.basis .sphere 5 130 0) (I.realization.basis .sphere 7 131 2) := u_survives1000_h163 I
  have h171 : HasDifferential E 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 0) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 3) := u_survives1000_h171 I
  have h172 : HasDifferential E 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 1) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 1 + I.realization.basis .sphere 10 134 3 + I.realization.basis .sphere 10 134 4) := u_survives1000_h172 I
  have h200 : HasDifferential E 3 (8,133) (11,135) (I.realization.basis .sphere 8 133 0) (I.realization.basis .sphere 11 135 0) := u_survives1000_h200 I
  have h201 : HasDifferential E 2 (8,133) (10,134) (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := u_survives1000_h201 I
  have h249 : ReachesPage E 1000 (10,134) (I.realization.basis .sphere 10 134 4) := u_survives1000_h249 I
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
  have generated_one {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2)) (a : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (x : E.Page r p) : x=0 ∨ x=a := by
    exact FinitePageCalculus.generated_one hr e a ha x
  have generated_two {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2)) (a b : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (hb : RepresentsOnPage E r p (e.symm (Finsupp.single 1 1)) b)
      (x : E.Page r p) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    exact FinitePageCalculus.generated_two hr e a b ha hb x
  have incoming2 (x : E.Page 2 (8,133)) : E.d 2 (8,133) x=0 ∨
      E.d 2 (8,133) x=I.realization.basis .sphere 10 134 2+I.realization.basis .sphere 10 134 4 := by
    obtain ⟨_,a,b,ha,hb,hd⟩ := h200
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a,ha⟩
    have d1 := h201.eq_on_page_two.2
    change E.d 2 (8,133) (I.realization.basis .sphere 8 133 1)=_ at d1
    have h := generated_two (by decide : (2:ℤ)≤2) e8_133 _ _
      (by rw [he8_133_0]; exact hrep2 _) (by rw [he8_133_1]; exact hrep2 _) x
    rcases h with h|h|h|h
    · exact Or.inl (by rw [h,map_zero])
    · exact Or.inl (by rw [h,d0])
    · exact Or.inr (by rw [h,d1])
    · exact Or.inr (by rw [h,map_add,d0,d1,zero_add])
  have incoming3 : E.d 3 (7,132)=0 := by
    obtain ⟨_,a,b,ha,hb,hd⟩ := h157
    have hd0 : E.d 3 (7,132) b=0 := IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(4,130)) ⟨a,hd⟩
    ext x
    rcases generated_one (by decide : (2:ℤ)≤3) e7_132 b (by rw [he7_132_0]; exact hb) x with h|h
    · simp only [h,map_zero,ModuleCat.hom_zero,LinearMap.zero_apply]
    · simp only [h,hd0,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a4,y4,ha4,hy4,hda4⟩ := h171
  obtain ⟨_,b4,z4,hb4,hz4,hdb4⟩ := h172
  have incoming4 (x : E.Page 4 (6,131)) : E.d 4 (6,131) x=0 ∨ E.d 4 (6,131) x=y4 ∨
      E.d 4 (6,131) x=z4 ∨ E.d 4 (6,131) x=y4+z4 := by
    have da : E.d 4 (6,131) a4=y4 := hda4
    have db : E.d 4 (6,131) b4=z4 := hdb4
    rcases generated_two (by decide : (2:ℤ)≤4) e6_131 a4 b4
      (by rw [he6_131_0]; exact ha4) (by rw [he6_131_1]; exact hb4) x with h|h|h|h
    · exact Or.inl (by rw [h,map_zero])
    · exact Or.inr (Or.inl (by rw [h,da]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h,db])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h,map_add,da,db])))
  have source5 : Subsingleton (E.Page 3 (5,130)) := by
    have hd := h163.eq_on_page_two.2
    change E.d 2 (5,130) (I.realization.basis .sphere 5 130 0)=I.realization.basis .sphere 7 131 2 at hd
    have hn : I.realization.basis .sphere 7 131 2 ≠ 0 := by
      rw [←he7_131_2]
      intro h
      have hh := congrArg (fun x => e7_131 x 2) h
      simpa using hh
    have ker (x : E.Page 2 (5,130)) (hx : E.d 2 (5,130) x=0) : x=0 := by
      rcases generated_one (by decide : (2:ℤ)≤2) e5_130 _ (by rw [he5_130_0]; exact hrep2 _) x with h|h
      · exact h
      · exact (hn (by simpa only [h,hd] using hx)).elim
    have hinj : Function.Injective (E.d 2 (5,130)) := (injective_iff_map_eq_zero _).mpr ker
    let S := E.pageShortComplex 2 ((5,130)-E.diffDeg 2)
    have hs : Function.Injective S.g := hinj
    have hsex : S.Exact := S.moduleCat_exact_iff.mpr (by
      intro z hz
      have hz0 : z=0 := hs (hz.trans (map_zero _).symm)
      exact ⟨0,by simpa [hz0]⟩)
    have hzero := (S.exact_iff_isZero_homology).mp hsex
    exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 2 (5,130)
      (by change (2:ℤ)≤2; omega)).isZero_iff.mpr hzero)
  have incoming_late (r : ℤ) (hr : 5≤r) : E.d r ((10,134)-E.diffDeg r)=0 := by
    have hz : Subsingleton (E.Page r (10-r,135-r)) := by
      by_cases heq : r=5
      · subst r
        exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 3 5 5 130 (by omega) (by omega) source5
      have hq : 10-r≤4 := by omega
      by_cases hneg : 10-r<0
      · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r (10-r) (135-r) hneg
      have hd : (⟨.sphere,(10-r).toNat,(135-r).toNat,[]⟩ : Raw.Degree) ∈ Raw.degrees := by
        have hq0 : 0≤10-r := by omega
        have hrlo : 6≤r := by omega
        have hrhi : r≤10 := by omega
        interval_cases r <;> simp [Raw.degrees]
      obtain ⟨e,_⟩ := I.basis _ hd
      change Page D .sphere (10-r).toNat (135-r).toNat ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      have he : Subsingleton (Page D .sphere (10-r).toNat (135-r).toNat) := e.injective.subsingleton
      apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r (10-r) (135-r) (by omega) (by omega)
      simpa only [KIP126.Computation.Route.Page,KIP126.Computation.Route.sequence,KIP126.Computation.Route.object,ClassicalObject.obj,
        Int.toNat_of_nonneg (by omega : 0≤10-r),Int.toNat_of_nonneg (by omega : 0≤135-r)] using he
    have hp : (10,134)-E.diffDeg r=(10-r,135-r) := by
      change (10-r,134-(r-1))=(10-r,135-r)
      congr 1 <;> omega
    rw [hp]
    ext x
    change E.d r (10-r,135-r) x=0
    rw [hz.elim x 0,map_zero]
  let ell (x : E.Page 2 (10,134)) : F2 := e10_134 x 1 + e10_134 x 2 + e10_134 x 4
  have ell0 : ell 0=0 := by simp [ell]
  have elladd (x y : E.Page 2 (10,134)) : ell (x+y)=ell x+ell y := by
    dsimp only [ell]
    simp only [map_add,Finsupp.add_apply]
    abel
  have ellsub (x y : E.Page 2 (10,134)) : ell (x-y)=ell x-ell y := by
    dsimp only [ell]
    simp only [map_sub,Finsupp.sub_apply]
    abel
  have ellB (i : Fin 5) : ell (I.realization.basis .sphere 10 134 i.val) =
      (Finsupp.single i (1:F2) : Fin 5 →₀ F2) 1 +
      (Finsupp.single i (1:F2) : Fin 5 →₀ F2) 2 +
      (Finsupp.single i (1:F2) : Fin 5 →₀ F2) 4 := by
    rw [←he10_134 i]
    simp only [ell,LinearEquiv.apply_symm_apply]
  have ellB0 : ell (I.realization.basis .sphere 10 134 0)=0 := by simpa using ellB 0
  have ellB1 : ell (I.realization.basis .sphere 10 134 1)=1 := by simpa using ellB 1
  have ellB2 : ell (I.realization.basis .sphere 10 134 2)=1 := by simpa using ellB 2
  have ellB3 : ell (I.realization.basis .sphere 10 134 3)=0 := by simpa using ellB 3
  have ellB4 : ell (I.realization.basis .sphere 10 134 4)=1 := by simpa using ellB 4
  have ell_incoming2 (x : E.Page 2 (8,133)) : ell (E.d 2 (8,133) x)=0 := by
    rcases incoming2 x with h|h
    · rw [h,ell0]
    · rw [h,elladd,ellB2,ellB4]
      decide
  have nonzero3 {x : E.Page 2 (10,134)} (hx : ell x=1) {a : E.Page 3 (10,134)}
      (ha : RepresentsOnPage E 3 (10,134) x a) : a ≠ 0 := by
    obtain ⟨_,z,hz2,hz3⟩ := ha
    intro hzero
    obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 2
      (by change (2:ℤ)≤2; omega) (8,133) z).mp (hz3.trans hzero)
    have he : E.d 2 (8,133) b=x := hb.trans hz2
    have hh := ell_incoming2 b
    rw [he,hx] at hh
    exact one_ne_zero hh
  have nonzero4 {x : E.Page 2 (10,134)} (hx : ell x=1) {a : E.Page 4 (10,134)}
      (ha : RepresentsOnPage E 4 (10,134) x a) : a ≠ 0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    exact represents_next_nonzero_of_incoming_zero_at
      (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) (by exact incoming3) ha hb (nonzero3 hx hb)
  have nonzero5 {a : E.Page 5 (10,134)}
      (ha : RepresentsOnPage E 5 (10,134) (I.realization.basis .sphere 10 134 4) a) : a ≠ 0 := by
    obtain ⟨_,z,hz2,hz5⟩ := ha
    let A := E.ssData (10,134)
    let i := Subobject.ofLE (A.Z 3) (A.Z 2) (A.Z_anti (by decide : (2:WithTop ℕ)≤3))
    let u4 := A.pageπ 2 (i z)
    have hu4 : RepresentsOnPage E 4 (10,134) (I.realization.basis .sphere 10 134 4) u4 := by
      refine ⟨by decide,i z,?_,rfl⟩
      change (i ≫ Subobject.ofLE (A.Z 2) (A.Z 0) _ ≫ A.pageπ 0) z = _
      dsimp only [i]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz2
    have un : u4≠0 := nonzero4 ellB4 hu4
    have uy : u4≠y4 := by
      intro h
      have hn := nonzero4 (by rw [ellsub,ellB4,elladd,ellB0,ellB3]; simp) (hsub hu4 hy4)
      exact hn (sub_eq_zero.mpr h)
    have uz : u4≠z4 := by
      intro h
      have hn := nonzero4 (by
        rw [ellsub,ellB4,elladd,elladd,elladd,ellB0,ellB1,ellB3,ellB4]
        decide) (hsub hu4 hz4)
      exact hn (sub_eq_zero.mpr h)
    have uyz : u4≠y4+z4 := by
      intro h
      have hn := nonzero4 (by
        rw [ellsub,ellB4,elladd,elladd,elladd,elladd,elladd,ellB0,ellB1,ellB3,ellB4]
        decide) (hsub hu4 (hadd hy4 hz4))
      exact hn (sub_eq_zero.mpr h)
    intro hzero
    obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 4
      (by change (2:ℤ)≤4; omega) (6,131) z).mp (hz5.trans hzero)
    change E.d 4 (6,131) b=u4 at hb
    rcases incoming4 b with h|h|h|h
    · exact un (hb.symm.trans h)
    · exact uy (hb.symm.trans h)
    · exact uz (hb.symm.trans h)
    · exact uyz (hb.symm.trans h)
  obtain ⟨a,ha⟩ := h249
  refine ⟨a,ha,?_⟩
  obtain ⟨_,z,hz2,hza⟩ := ha
  let A := E.ssData (10,134)
  let i := Subobject.ofLE (A.Z 998) (A.Z 3) (A.Z_anti (by decide : (3:WithTop ℕ)≤998))
  have rep5 : RepresentsOnPage E 5 (10,134) (I.realization.basis .sphere 10 134 4) (A.pageπ 3 (i z)) := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 3) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have hB : A.B ⊤=A.B 3 := boundaries_top_eq_of_d_eq_zero E 5 (by change (2:ℤ)≤5; omega) (10,134) incoming_late
  intro ha0
  have hb := (subobject_cokernel_π_eq_zero_iff (A.B 998) (A.Z 998) (A.B_le_Z _) z).mp (hza.trans ha0)
  have hb' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono (show (998:WithTop ℕ)≤⊤ from le_top)) hb
  rw [hB] at hb'
  apply nonzero5 rep5
  apply (subobject_cokernel_π_eq_zero_iff (A.B 3) (A.Z 3) (A.B_le_Z _) (i z)).mpr
  change (i ≫ (A.Z 3).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]


private theorem p_survives1000_h198 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,131) (11,133) (I.realization.basis .sphere 8 131 0) (I.realization.basis .sphere 11 133 0 + I.realization.basis .sphere 11 133 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 8, 131, [0], 11, 133, [0, 1], "S0_AdamsE2_ss", 2488⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,131) (11,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 133 [0, 1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem p_survives1000_h199 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,132) (10,133) (I.realization.basis .sphere 8 132 0) (I.realization.basis .sphere 10 133 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 8, 132, [0], 10, 133, [2], "S0_AdamsE2_ss", 2571⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,132) (10,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem p_survives1000_h219 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 12 (9,132) (I.realization.basis .sphere 9 132 0 + I.realization.basis .sphere 9 132 1) := by
  classical
  have hrow := I.results ⟨.sphere, .reaches, 12, 9, 132, [0, 1], 9, 132, [], "S0_AdamsE2_ss", 2569⟩ (by
    exact List.mem_of_getElem? (i := 219) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0, 1] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem p_survives1000_h220 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,132) (12,134) (I.realization.basis .sphere 9 132 1) (I.realization.basis .sphere 12 134 1 + I.realization.basis .sphere 12 134 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 9, 132, [1], 12, 134, [1, 2], "S0_AdamsE2_ss", 2570⟩ (by
    exact List.mem_of_getElem? (i := 220) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem p_survives1000_h245 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,133) (12,134) (I.realization.basis .sphere 10 133 1) (I.realization.basis .sphere 12 134 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 10, 133, [1], 12, 134, [2], "S0_AdamsE2_ss", 2625⟩ (by
    exact List.mem_of_getElem? (i := 245) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,133) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem p_survives1000_h268 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (11,133) (I.realization.basis .sphere 11 133 1) := by
  classical
  have hrow := I.results ⟨.sphere, .reaches, 1000, 11, 133, [1], 11, 133, [], "S0_AdamsE2_ss", 2622⟩ (by
    exact List.mem_of_getElem? (i := 268) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 133 [1] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem p_survives1000_h295 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,132) (12,134) (I.realization.basis .sphere 9 132 0) (I.realization.basis .sphere 12 134 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 9, 132, [0], 12, 134, [1], "S0_AdamsE2_ss", 2683⟩ (by
    exact List.mem_of_getElem? (i := 295) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem p_survives1000_h296 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (12,134) (I.realization.basis .sphere 12 134 0) := by
  classical
  have hrow := I.results ⟨.sphere, .reaches, 1000, 12, 134, [0], 12, 134, [], "S0_AdamsE2_ss", 2684⟩ (by
    exact List.mem_of_getElem? (i := 296) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 134 [0] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem p_survives1000
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H} (I : Inputs D L G) :
    SurvivesTo (sequence D .sphere) 1000 (11,133) (I.realization.basis .sphere 11 133 1) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e11_133,he11_133⟩ := I.basis ⟨.sphere, 11, 133, ["371,1", "69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 189) (by rfl))
  change E.Page 2 (11,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e11_133
  change ∀i : Fin 2, e11_133.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 133 i.val at he11_133
  have he11_133_0 : e11_133.symm (Finsupp.single 0 1) = I.realization.basis .sphere 11 133 0 := he11_133 0
  have he11_133_1 : e11_133.symm (Finsupp.single 1 1) = I.realization.basis .sphere 11 133 1 := he11_133 1
  obtain ⟨e12_134,he12_134⟩ := I.basis ⟨.sphere, 12, 134, ["18,1,188,1", "0,1,371,1", "0,1,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  change E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e12_134
  change ∀i : Fin 3, e12_134.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 134 i.val at he12_134
  have he12_134_0 : e12_134.symm (Finsupp.single 0 1) = I.realization.basis .sphere 12 134 0 := he12_134 0
  have he12_134_1 : e12_134.symm (Finsupp.single 1 1) = I.realization.basis .sphere 12 134 1 := he12_134 1
  have he12_134_2 : e12_134.symm (Finsupp.single 2 1) = I.realization.basis .sphere 12 134 2 := he12_134 2
  obtain ⟨e10_133,he10_133⟩ := I.basis ⟨.sphere, 10, 133, ["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e10_133
  change ∀i : Fin 3, e10_133.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 133 i.val at he10_133
  have he10_133_0 : e10_133.symm (Finsupp.single 0 1) = I.realization.basis .sphere 10 133 0 := he10_133 0
  have he10_133_1 : e10_133.symm (Finsupp.single 1 1) = I.realization.basis .sphere 10 133 1 := he10_133 1
  have he10_133_2 : e10_133.symm (Finsupp.single 2 1) = I.realization.basis .sphere 10 133 2 := he10_133 2
  obtain ⟨e9_132,he9_132⟩ := I.basis ⟨.sphere, 9, 132, ["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e9_132
  change ∀i : Fin 2, e9_132.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 132 i.val at he9_132
  have he9_132_0 : e9_132.symm (Finsupp.single 0 1) = I.realization.basis .sphere 9 132 0 := he9_132 0
  have he9_132_1 : e9_132.symm (Finsupp.single 1 1) = I.realization.basis .sphere 9 132 1 := he9_132 1
  obtain ⟨e8_131,he8_131⟩ := I.basis ⟨.sphere, 8, 131, ["352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 159) (by rfl))
  change E.Page 2 (8,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e8_131
  change ∀i : Fin 1, e8_131.symm (Finsupp.single i 1) = I.realization.basis .sphere 8 131 i.val at he8_131
  have he8_131_0 : e8_131.symm (Finsupp.single 0 1) = I.realization.basis .sphere 8 131 0 := he8_131 0
  have h198 : HasDifferential E 3 (8,131) (11,133) (I.realization.basis .sphere 8 131 0) (I.realization.basis .sphere 11 133 0 + I.realization.basis .sphere 11 133 1) := p_survives1000_h198 I
  have h199 : HasDifferential E 2 (8,132) (10,133) (I.realization.basis .sphere 8 132 0) (I.realization.basis .sphere 10 133 2) := p_survives1000_h199 I
  have h219 : ReachesPage E 12 (9,132) (I.realization.basis .sphere 9 132 0 + I.realization.basis .sphere 9 132 1) := p_survives1000_h219 I
  have h220 : HasDifferential E 3 (9,132) (12,134) (I.realization.basis .sphere 9 132 1) (I.realization.basis .sphere 12 134 1 + I.realization.basis .sphere 12 134 2) := p_survives1000_h220 I
  have h245 : HasDifferential E 2 (10,133) (12,134) (I.realization.basis .sphere 10 133 1) (I.realization.basis .sphere 12 134 2) := p_survives1000_h245 I
  have h268 : ReachesPage E 1000 (11,133) (I.realization.basis .sphere 11 133 1) := p_survives1000_h268 I
  have h295 : HasDifferential E 3 (9,132) (12,134) (I.realization.basis .sphere 9 132 0) (I.realization.basis .sphere 12 134 1) := p_survives1000_h295 I
  have h296 : ReachesPage E 1000 (12,134) (I.realization.basis .sphere 12 134 0) := p_survives1000_h296 I
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
  have generated_one {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2)) (a : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (x : E.Page r p) : x=0 ∨ x=a := by
    exact FinitePageCalculus.generated_one hr e a ha x
  have generated_two {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2)) (a b : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (hb : RepresentsOnPage E r p (e.symm (Finsupp.single 1 1)) b)
      (x : E.Page r p) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    exact FinitePageCalculus.generated_two hr e a b ha hb x
  have low123 (r q : ℤ) (hr : 2≤r) (hq : q≤7) : Subsingleton (E.Page r (q,q+123)) := by
    by_cases hneg : q<0
    · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r q (q+123) hneg
    have hq0 : 0≤q := by omega
    have hd : (⟨.sphere,q.toNat,(q+123).toNat,[]⟩ : Raw.Degree) ∈ Raw.degrees := by
      interval_cases q <;> simp [Raw.degrees]
    obtain ⟨e,_⟩ := I.basis _ hd
    change KIP126.Computation.Route.Page D .sphere q.toNat (q+123).toNat ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    have he : Subsingleton (KIP126.Computation.Route.Page D .sphere q.toNat (q+123).toNat) := e.injective.subsingleton
    apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r q (q+123) (by omega) hr
    simpa only [KIP126.Computation.Route.Page,KIP126.Computation.Route.sequence,KIP126.Computation.Route.object,ClassicalObject.obj,
      Int.toNat_of_nonneg hq0,Int.toNat_of_nonneg (by omega : 0≤q+123)] using he
  obtain ⟨_,a30,t30,ha30,ht30,hda30⟩ := h295
  obtain ⟨_,a31,t31,ha31,ht31,hda31⟩ := h220
  have d2_9 : E.d 2 (9,132)=0 := by
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a30,ha30⟩
    have d1 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a31,ha31⟩
    ext x
    rcases generated_two (by decide : (2:ℤ)≤2) e9_132 _ _
      (by rw [he9_132_0];exact hrep2 _) (by rw [he9_132_1];exact hrep2 _) x with h|h|h|h
    all_goals simp only [h,map_add,map_zero,d0,d1,zero_add,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a3,t3,ha3,ht3,hda3⟩ := h198
  have incoming3 (x : E.Page 3 (8,131)) : E.d 3 (8,131) x=0 ∨ E.d 3 (8,131) x=t3 := by
    have hd : E.d 3 (8,131) a3=t3 := hda3
    rcases generated_one (by decide : (2:ℤ)≤3) e8_131 a3 (by rw [he8_131_0];exact ha3) x with h|h
    · exact Or.inl (by rw [h,map_zero])
    · exact Or.inr (by rw [h,hd])
  have nonzero3 {x : E.Page 2 (11,133)} (hx : x≠0) {a : E.Page 3 (11,133)}
      (ha : RepresentsOnPage E 3 (11,133) x a) : a≠0 :=
    represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)≤2)
      (by exact d2_9) ha (hrep2 x) hx
  have nonzero4 {a : E.Page 4 (11,133)}
      (ha : RepresentsOnPage E 4 (11,133) (I.realization.basis .sphere 11 133 1) a) : a≠0 := by
    obtain ⟨_,z,hz2,hz4⟩ := ha
    let A := E.ssData (11,133)
    let i := Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2))
    let p3 := A.pageπ 1 (i z)
    have hp3 : RepresentsOnPage E 3 (11,133) (I.realization.basis .sphere 11 133 1) p3 := by
      refine ⟨by decide,i z,?_,rfl⟩
      change (i ≫ Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0) z = _
      dsimp only [i]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz2
    have pn : p3≠0 := nonzero3 (by
      rw [←he11_133_1]
      intro h
      have hh := congrArg (fun x => e11_133 x 1) h
      simpa using hh) hp3
    have pt : p3≠t3 := by
      intro h
      have hn := nonzero3 (by
        rw [←he11_133_0,←he11_133_1]
        intro h
        have hh := congrArg (fun x => e11_133 x 0) h
        simp only [map_add,map_sub,LinearEquiv.apply_symm_apply,map_zero,Finsupp.add_apply,Finsupp.sub_apply] at hh
        norm_num at hh) (hsub hp3 ht3)
      exact hn (sub_eq_zero.mpr h)
    intro hzero
    obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 3
      (by change (2:ℤ)≤3;omega) (8,131) z).mp (hz4.trans hzero)
    change E.d 3 (8,131) b=p3 at hb
    rcases incoming3 b with h|h
    · exact pn (hb.symm.trans h)
    · exact pt (hb.symm.trans h)
  have incoming_late (r : ℤ) (hr : 4≤r) : E.d r ((11,133)-E.diffDeg r)=0 := by
    have hp : (11,133)-E.diffDeg r=(11-r,(11-r)+123) := by
      change (11-r,133-(r-1))=(11-r,(11-r)+123)
      congr 1 <;> omega
    rw [hp]
    have hz := low123 r (11-r) (by omega) (by omega)
    ext x
    change E.d r _ x=0
    rw [hz.elim x 0,map_zero]
  obtain ⟨a,ha⟩ := h268
  refine ⟨a,ha,?_⟩
  obtain ⟨_,z,hz2,hza⟩ := ha
  let A := E.ssData (11,133)
  let i := Subobject.ofLE (A.Z 998) (A.Z 2) (A.Z_anti (by decide : (2:WithTop ℕ)≤998))
  have rep4 : RepresentsOnPage E 4 (11,133) (I.realization.basis .sphere 11 133 1) (A.pageπ 2 (i z)) := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 2) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have hB : A.B ⊤=A.B 2 := boundaries_top_eq_of_d_eq_zero E 4 (by change (2:ℤ)≤4;omega) (11,133) incoming_late
  intro ha0
  have hb := (subobject_cokernel_π_eq_zero_iff (A.B 998) (A.Z 998) (A.B_le_Z _) z).mp (hza.trans ha0)
  have hb' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono (show (998:WithTop ℕ)≤⊤ from le_top)) hb
  rw [hB] at hb'
  apply nonzero4 rep4
  apply (subobject_cokernel_π_eq_zero_iff (A.B 2) (A.Z 2) (A.B_le_Z _) (i z)).mpr
  change (i ≫ (A.Z 2).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]


private theorem q_survives1000_h198 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,131) (11,133) (I.realization.basis .sphere 8 131 0) (I.realization.basis .sphere 11 133 0 + I.realization.basis .sphere 11 133 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 8, 131, [0], 11, 133, [0, 1], "S0_AdamsE2_ss", 2488⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,131) (11,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 133 [0, 1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_h199 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,132) (10,133) (I.realization.basis .sphere 8 132 0) (I.realization.basis .sphere 10 133 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 8, 132, [0], 10, 133, [2], "S0_AdamsE2_ss", 2571⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,132) (10,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_h219 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 12 (9,132) (I.realization.basis .sphere 9 132 0 + I.realization.basis .sphere 9 132 1) := by
  classical
  have hrow := I.results ⟨.sphere, .reaches, 12, 9, 132, [0, 1], 9, 132, [], "S0_AdamsE2_ss", 2569⟩ (by
    exact List.mem_of_getElem? (i := 219) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0, 1] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem q_survives1000_h220 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,132) (12,134) (I.realization.basis .sphere 9 132 1) (I.realization.basis .sphere 12 134 1 + I.realization.basis .sphere 12 134 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 9, 132, [1], 12, 134, [1, 2], "S0_AdamsE2_ss", 2570⟩ (by
    exact List.mem_of_getElem? (i := 220) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_h245 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,133) (12,134) (I.realization.basis .sphere 10 133 1) (I.realization.basis .sphere 12 134 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 10, 133, [1], 12, 134, [2], "S0_AdamsE2_ss", 2625⟩ (by
    exact List.mem_of_getElem? (i := 245) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,133) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_h268 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (11,133) (I.realization.basis .sphere 11 133 1) := by
  classical
  have hrow := I.results ⟨.sphere, .reaches, 1000, 11, 133, [1], 11, 133, [], "S0_AdamsE2_ss", 2622⟩ (by
    exact List.mem_of_getElem? (i := 268) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 133 [1] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem q_survives1000_h295 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,132) (12,134) (I.realization.basis .sphere 9 132 0) (I.realization.basis .sphere 12 134 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 9, 132, [0], 12, 134, [1], "S0_AdamsE2_ss", 2683⟩ (by
    exact List.mem_of_getElem? (i := 295) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,132) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_h296 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (12,134) (I.realization.basis .sphere 12 134 0) := by
  classical
  have hrow := I.results ⟨.sphere, .reaches, 1000, 12, 134, [0], 12, 134, [], "S0_AdamsE2_ss", 2684⟩ (by
    exact List.mem_of_getElem? (i := 296) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 134 [0] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem q_survives1000_h183 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (7,131) (10,133) (I.realization.basis .sphere 7 131 0) (I.realization.basis .sphere 10 133 0 + I.realization.basis .sphere 10 133 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 7, 131, [0], 10, 133, [0, 1], "S0_AdamsE2_ss", 2491⟩ (by
    exact List.mem_of_getElem? (i := 183) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (7,131) (10,133) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0, 1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_h294 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,133) (12,134) (I.realization.basis .sphere 10 133 0) (I.realization.basis .sphere 12 134 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 10, 133, [0], 12, 134, [2], "S0_AdamsE2_ss", 2682⟩ (by
    exact List.mem_of_getElem? (i := 294) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,133) (12,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem q_survives1000_nonzero4
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}     (I : Inputs D L G) {a : (sequence D .sphere).Page 4 (12,134)}
      (ha : RepresentsOnPage (sequence D .sphere) 4 (12,134) (I.realization.basis .sphere 12 134 0) a) : a≠0  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e12_134,he12_134⟩ := I.basis ⟨.sphere, 12, 134, ["18,1,188,1", "0,1,371,1", "0,1,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  change E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e12_134
  change ∀i : Fin 3, e12_134.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 134 i.val at he12_134
  have he12_134_0 : e12_134.symm (Finsupp.single 0 1) = I.realization.basis .sphere 12 134 0 := he12_134 0
  have he12_134_1 : e12_134.symm (Finsupp.single 1 1) = I.realization.basis .sphere 12 134 1 := he12_134 1
  have he12_134_2 : e12_134.symm (Finsupp.single 2 1) = I.realization.basis .sphere 12 134 2 := he12_134 2
  obtain ⟨e10_133,he10_133⟩ := I.basis ⟨.sphere, 10, 133, ["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e10_133
  change ∀i : Fin 3, e10_133.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 133 i.val at he10_133
  obtain ⟨e9_132,he9_132⟩ := I.basis ⟨.sphere, 9, 132, ["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e9_132
  change ∀i : Fin 2, e9_132.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 132 i.val at he9_132
  have he9_132_0 : e9_132.symm (Finsupp.single 0 1) = I.realization.basis .sphere 9 132 0 := he9_132 0
  have he9_132_1 : e9_132.symm (Finsupp.single 1 1) = I.realization.basis .sphere 9 132 1 := he9_132 1
  have h199 : HasDifferential E 2 (8,132) (10,133) (I.realization.basis .sphere 8 132 0) (I.realization.basis .sphere 10 133 2) := q_survives1000_h199 I
  have h220 : HasDifferential E 3 (9,132) (12,134) (I.realization.basis .sphere 9 132 1) (I.realization.basis .sphere 12 134 1 + I.realization.basis .sphere 12 134 2) := q_survives1000_h220 I
  have h245 : HasDifferential E 2 (10,133) (12,134) (I.realization.basis .sphere 10 133 1) (I.realization.basis .sphere 12 134 2) := q_survives1000_h245 I
  have h295 : HasDifferential E 3 (9,132) (12,134) (I.realization.basis .sphere 9 132 0) (I.realization.basis .sphere 12 134 1) := q_survives1000_h295 I
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have hsub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have generated_two {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2)) (a b : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (hb : RepresentsOnPage E r p (e.symm (Finsupp.single 1 1)) b)
      (x : E.Page r p) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    exact FinitePageCalculus.generated_two hr e a b ha hb x
  have h294 : HasDifferential E 2 (10,133) (12,134) (I.realization.basis .sphere 10 133 0) (I.realization.basis .sphere 12 134 2) := q_survives1000_h294 I
  obtain ⟨_,a30,t30,ha30,ht30,hda30⟩ := h295
  obtain ⟨_,a31,t31,ha31,ht31,hda31⟩ := h220
  let ell (x : E.Page 2 (12,134)) : F2 := e12_134 x 0
  have ell0 : ell 0=0 := by simp [ell]
  have elladd (x y : E.Page 2 (12,134)) : ell (x+y)=ell x+ell y := by simp [ell]
  have ellsub (x y : E.Page 2 (12,134)) : ell (x-y)=ell x-ell y := by simp [ell]
  have ellB0 : ell (I.realization.basis .sphere 12 134 0)=1 := by
    rw [←he12_134_0]
    simp [ell]
  have ellB1 : ell (I.realization.basis .sphere 12 134 1)=0 := by
    rw [←he12_134_1]
    simp [ell]
  have ellB2 : ell (I.realization.basis .sphere 12 134 2)=0 := by
    rw [←he12_134_2]
    simp [ell]
  have ell_incoming2 (x : E.Page 2 (10,133)) : ell (E.d 2 (10,133) x)=0 := by
    have d0 := h294.eq_on_page_two.2
    have d1 := h245.eq_on_page_two.2
    change E.d 2 (10,133) (I.realization.basis .sphere 10 133 0)=I.realization.basis .sphere 12 134 2 at d0
    change E.d 2 (10,133) (I.realization.basis .sphere 10 133 1)=I.realization.basis .sphere 12 134 2 at d1
    have d2 : E.d 2 (10,133) (I.realization.basis .sphere 10 133 2)=0 := by
      have hd := h199.eq_on_page_two.2
      change E.d 2 (8,132) _ = _ at hd
      rw [←hd]
      exact congrArg (fun f => f (I.realization.basis .sphere 8 132 0)) (E.d_comp_d 2 (8,132))
    have one (i : Fin 3) : ell (E.d 2 (10,133) (e10_133.symm (Finsupp.single i 1)))=0 := by
      rw [he10_133]
      fin_cases i
      · rw [d0,ellB2]
      · rw [d1,ellB2]
      · rw [d2,ell0]
    have all (f : Fin 3 →₀ F2) : ell (E.d 2 (10,133) (e10_133.symm f))=0 := by
      induction f using Finsupp.induction with
      | zero => simp only [map_zero,ell0]
      | @single_add i a f hi ha ih =>
        rw [map_add,map_add,elladd,ih,add_zero]
        fin_cases a
        · simp only [Fin.mk_zero,Finsupp.single_zero,map_zero,ell0]
        · exact one i
    simpa only [LinearEquiv.symm_apply_apply] using all (e10_133 x)
  have nonzero3 {x : E.Page 2 (12,134)} (hx : ell x=1) {a : E.Page 3 (12,134)}
      (ha : RepresentsOnPage E 3 (12,134) x a) : a≠0 := by
    obtain ⟨_,z,hz2,hz3⟩ := ha
    intro ha0
    obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 2
      (by change (2:ℤ)≤2;omega) (10,133) z).mp (hz3.trans ha0)
    have he : E.d 2 (10,133) b=x := hb.trans hz2
    have hh := ell_incoming2 b
    rw [he,hx] at hh
    exact one_ne_zero hh

  obtain ⟨_,z,hz2,hz4⟩ := ha
  let A := E.ssData (12,134)
  let i := Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2))
  let q3 := A.pageπ 1 (i z)
  have hq3 : RepresentsOnPage E 3 (12,134) (I.realization.basis .sphere 12 134 0) q3 := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have avoid {x : E.Page 2 (12,134)} {t : E.Page 3 (12,134)}
      (hx : ell x=0) (ht : RepresentsOnPage E 3 (12,134) x t) : q3≠t := by
    intro h
    have hn := nonzero3 (by rw [ellsub,ellB0,hx,sub_zero]) (hsub hq3 ht)
    exact hn (sub_eq_zero.mpr h)
  have qn : q3≠0 := nonzero3 ellB0 hq3
  have q0 : q3≠t30 := avoid ellB1 ht30
  have q1 : q3≠t31 := avoid (by rw [elladd,ellB1,ellB2,add_zero]) ht31
  have q01 : q3≠t30+t31 := avoid (by simp only [elladd,ellB1,ellB2,add_zero]) (hadd ht30 ht31)
  intro ha0
  obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 3
    (by change (2:ℤ)≤3;omega) (9,132) z).mp (hz4.trans ha0)
  change E.d 3 (9,132) b=q3 at hb
  have d0 : E.d 3 (9,132) a30=t30 := hda30
  have d1 : E.d 3 (9,132) a31=t31 := hda31
  rcases generated_two (by decide : (2:ℤ)≤3) e9_132 a30 a31
    (by rw [he9_132_0];exact ha30) (by rw [he9_132_1];exact ha31) b with h|h|h|h
  · apply qn
    simpa only [h,map_zero] using hb.symm
  · apply q0
    simpa only [h,d0] using hb.symm
  · apply q1
    simpa only [h,d1] using hb.symm
  · apply q01
    simpa only [h,map_add,d0,d1] using hb.symm

private theorem q_survives1000_source8
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H}     (I : Inputs D L G) : Subsingleton ((sequence D .sphere).Page 4 (8,131))  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e11_133,he11_133⟩ := I.basis ⟨.sphere, 11, 133, ["371,1", "69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 189) (by rfl))
  change E.Page 2 (11,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e11_133
  change ∀i : Fin 2, e11_133.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 133 i.val at he11_133
  have he11_133_0 : e11_133.symm (Finsupp.single 0 1) = I.realization.basis .sphere 11 133 0 := he11_133 0
  have he11_133_1 : e11_133.symm (Finsupp.single 1 1) = I.realization.basis .sphere 11 133 1 := he11_133 1
  obtain ⟨e9_132,he9_132⟩ := I.basis ⟨.sphere, 9, 132, ["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e9_132
  change ∀i : Fin 2, e9_132.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 132 i.val at he9_132
  have he9_132_0 : e9_132.symm (Finsupp.single 0 1) = I.realization.basis .sphere 9 132 0 := he9_132 0
  have he9_132_1 : e9_132.symm (Finsupp.single 1 1) = I.realization.basis .sphere 9 132 1 := he9_132 1
  obtain ⟨e8_131,he8_131⟩ := I.basis ⟨.sphere, 8, 131, ["352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 159) (by rfl))
  change E.Page 2 (8,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e8_131
  change ∀i : Fin 1, e8_131.symm (Finsupp.single i 1) = I.realization.basis .sphere 8 131 i.val at he8_131
  have he8_131_0 : e8_131.symm (Finsupp.single 0 1) = I.realization.basis .sphere 8 131 0 := he8_131 0
  have h198 : HasDifferential E 3 (8,131) (11,133) (I.realization.basis .sphere 8 131 0) (I.realization.basis .sphere 11 133 0 + I.realization.basis .sphere 11 133 1) := q_survives1000_h198 I
  have h220 : HasDifferential E 3 (9,132) (12,134) (I.realization.basis .sphere 9 132 1) (I.realization.basis .sphere 12 134 1 + I.realization.basis .sphere 12 134 2) := q_survives1000_h220 I
  have h295 : HasDifferential E 3 (9,132) (12,134) (I.realization.basis .sphere 9 132 0) (I.realization.basis .sphere 12 134 1) := q_survives1000_h295 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have generated_one {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2)) (a : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (x : E.Page r p) : x=0 ∨ x=a := by
    exact FinitePageCalculus.generated_one hr e a ha x
  have generated_two {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2)) (a b : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (hb : RepresentsOnPage E r p (e.symm (Finsupp.single 1 1)) b)
      (x : E.Page r p) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    exact FinitePageCalculus.generated_two hr e a b ha hb x
  obtain ⟨_,a30,t30,ha30,ht30,hda30⟩ := h295
  obtain ⟨_,a31,t31,ha31,ht31,hda31⟩ := h220
  have d2_9 : E.d 2 (9,132)=0 := by
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a30,ha30⟩
    have d1 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a31,ha31⟩
    ext x
    rcases generated_two (by decide : (2:ℤ)≤2) e9_132 _ _
      (by rw [he9_132_0];exact hrep2 _) (by rw [he9_132_1];exact hrep2 _) x with h|h|h|h
    all_goals simp only [h,map_add,map_zero,d0,d1,zero_add,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a3,t3,ha3,ht3,hda3⟩ := h198
  have p_nonzero3 {x : E.Page 2 (11,133)} (hx : x≠0) {a : E.Page 3 (11,133)}
      (ha : RepresentsOnPage E 3 (11,133) x a) : a≠0 :=
    represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)≤2)
      (by exact d2_9) ha (hrep2 x) hx

  have tn : t3≠0 := p_nonzero3 (by
    rw [←he11_133_0,←he11_133_1]
    intro h
    have hh := congrArg (fun x => e11_133 x 0) h
    simp only [map_add,LinearEquiv.apply_symm_apply,map_zero,Finsupp.add_apply] at hh
    norm_num at hh) ht3
  have hd : E.d 3 (8,131) a3=t3 := hda3
  have ker (x : E.Page 3 (8,131)) (hx : E.d 3 (8,131) x=0) : x=0 := by
    rcases generated_one (by decide : (2:ℤ)≤3) e8_131 a3 (by rw [he8_131_0];exact ha3) x with h|h
    · exact h
    · exact (tn (by simpa only [h,hd] using hx)).elim
  have hinj : Function.Injective (E.d 3 (8,131)) := (injective_iff_map_eq_zero _).mpr ker
  let S := E.pageShortComplex 3 ((8,131)-E.diffDeg 3)
  have hs : Function.Injective S.g := hinj
  have hsex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro z hz
    have hz0 : z=0 := hs (hz.trans (map_zero _).symm)
    exact ⟨0,by simpa [hz0]⟩)
  have hzero := (S.exact_iff_isZero_homology).mp hsex
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (8,131)
    (by change (2:ℤ)≤3;omega)).isZero_iff.mpr hzero)

private theorem q_survives1000
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H} (I : Inputs D L G) :
    SurvivesTo (sequence D .sphere) 1000 (12,134) (I.realization.basis .sphere 12 134 0) := by
  classical
  let E := sequence D .sphere
  have h296 : ReachesPage E 1000 (12,134) (I.realization.basis .sphere 12 134 0) := q_survives1000_h296 I
  have low123 (r q : ℤ) (hr : 2≤r) (hq : q≤7) : Subsingleton (E.Page r (q,q+123)) := by
    by_cases hneg : q<0
    · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r q (q+123) hneg
    have hq0 : 0≤q := by omega
    have hd : (⟨.sphere,q.toNat,(q+123).toNat,[]⟩ : Raw.Degree) ∈ Raw.degrees := by
      interval_cases q <;> simp [Raw.degrees]
    obtain ⟨e,_⟩ := I.basis _ hd
    change KIP126.Computation.Route.Page D .sphere q.toNat (q+123).toNat ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    have he : Subsingleton (KIP126.Computation.Route.Page D .sphere q.toNat (q+123).toNat) := e.injective.subsingleton
    apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r q (q+123) (by omega) hr
    simpa only [KIP126.Computation.Route.Page,KIP126.Computation.Route.sequence,KIP126.Computation.Route.object,ClassicalObject.obj,
      Int.toNat_of_nonneg hq0,Int.toNat_of_nonneg (by omega : 0≤q+123)] using he
  have source8 : Subsingleton (E.Page 4 (8,131))  := q_survives1000_source8 I
  have nonzero4 {a : E.Page 4 (12,134)}
      (ha : RepresentsOnPage E 4 (12,134) (I.realization.basis .sphere 12 134 0) a) : a≠0  := q_survives1000_nonzero4 I ha
  have incoming_late (r : ℤ) (hr : 4≤r) : E.d r ((12,134)-E.diffDeg r)=0 := by
    have hp : (12,134)-E.diffDeg r=(12-r,(12-r)+123) := by
      change (12-r,134-(r-1))=(12-r,(12-r)+123)
      congr 1 <;> omega
    rw [hp]
    have hz : Subsingleton (E.Page r (12-r,(12-r)+123)) := by
      by_cases he : r=4
      · subst r
        exact source8
      exact low123 r (12-r) (by omega) (by omega)
    ext x
    change E.d r _ x=0
    rw [hz.elim x 0,map_zero]
  obtain ⟨a,ha⟩ := h296
  refine ⟨a,ha,?_⟩
  obtain ⟨_,z,hz2,hza⟩ := ha
  let A := E.ssData (12,134)
  let i := Subobject.ofLE (A.Z 998) (A.Z 2) (A.Z_anti (by decide : (2:WithTop ℕ)≤998))
  have rep4 : RepresentsOnPage E 4 (12,134) (I.realization.basis .sphere 12 134 0) (A.pageπ 2 (i z)) := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 2) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have hB : A.B ⊤=A.B 2 := boundaries_top_eq_of_d_eq_zero E 4 (by change (2:ℤ)≤4;omega) (12,134) incoming_late
  intro ha0
  have hb := (subobject_cokernel_π_eq_zero_iff (A.B 998) (A.Z 998) (A.B_le_Z _) z).mp (hza.trans ha0)
  have hb' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono (show (998:WithTop ℕ)≤⊤ from le_top)) hb
  rw [hB] at hb'
  apply nonzero4 rep4
  apply (subobject_cokernel_π_eq_zero_iff (A.B 2) (A.Z 2) (A.B_le_Z _) (i z)).mpr
  change (i ≫ (A.Z 2).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]


private theorem named_survival_labels
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H} (I : Inputs D L G) :
    I.realization.sphere 10 134 U = I.realization.basis .sphere 10 134 4 ∧
    I.realization.sphere 11 133 P = I.realization.basis .sphere 11 133 1 ∧
    I.realization.sphere 12 134 Q = I.realization.basis .sphere 12 134 0 := by
  classical
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
  have p_label : I.realization.sphere 11 133 P = I.realization.basis .sphere 11 133 1 := by
    have hc := I.csv (⟨.sphere,11,133,["371,1","69,1,79,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 189) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (1 : Fin 2)
    have heq : P=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨69,by decide⟩ * generator ⟨79,by decide⟩ = projection (monomialOfString "69,1,79,1")
      have hs : "69,1,79,1" ≠ "" := by decide
      have hp : (("69,1,79,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69,1,79,1] := by
        have split : "69,1,79,1".splitOn "," = ["69","1","79","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  have q_label : I.realization.sphere 12 134 Q = I.realization.basis .sphere 12 134 0 := by
    have hc := I.csv (⟨.sphere,12,134,["18,1,188,1","0,1,371,1","0,1,69,1,79,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 198) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 3)
    have heq : Q=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨18,by decide⟩ * generator ⟨188,by decide⟩ = projection (monomialOfString "18,1,188,1")
      have hs : "18,1,188,1" ≠ "" := by decide
      have hp : (("18,1,188,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [18,1,188,1] := by
        have split : "18,1,188,1".splitOn "," = ["18","1","188","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  exact ⟨u_label,p_label,q_label⟩

private theorem named_upq_survives1000 (I : Inputs D L G) :
    Derived.Survival I.realization 1000 U ∧
    Derived.Survival I.realization 1000 P ∧ Derived.Survival I.realization 1000 Q := by
  classical

  obtain ⟨hu,hp,hq⟩ := named_survival_labels I
  constructor
  · change SurvivesTo (sequence D .sphere) 1000 (10,134) _
    rw [hu]
    exact u_survives1000 I
  constructor
  · change SurvivesTo (sequence D .sphere) 1000 (11,133) _
    rw [hp]
    exact p_survives1000 I
  · change SurvivesTo (sequence D .sphere) 1000 (12,134) _
    rw [hq]
    exact q_survives1000 I

private theorem correction_source8_four_h200 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,133) (11,135)
    (I.realization.basis .sphere 8 133 0) (I.realization.basis .sphere 11 135 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,8,133,[0],11,135,[0],"S0_AdamsE2_ss",2629⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,133) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h201 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,133) (10,134)
    (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,133,[1],10,134,[2, 4],"S0_AdamsE2_ss",2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,133) (10,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h226 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,134) (12,136)
    (I.realization.basis .sphere 9 134 1) (I.realization.basis .sphere 12 136 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
    exact List.mem_of_getElem? (i := 226) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,134) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h227 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    (I.realization.basis .sphere 9 134 0) (I.realization.basis .sphere 11 135 3 + I.realization.basis .sphere 11 135 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
    exact List.mem_of_getElem? (i := 227) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h228 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    (I.realization.basis .sphere 9 134 4) (I.realization.basis .sphere 11 135 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
    exact List.mem_of_getElem? (i := 228) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h224 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (9,134) (I.realization.basis .sphere 9 134 2) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
    exact List.mem_of_getElem? (i := 224) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (9,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four_h225 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 7 (9,134) (I.realization.basis .sphere 9 134 3) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
    exact List.mem_of_getElem? (i := 225) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 7 (9,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [3] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem correction_source8_four (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (8,133)) := by
  classical
  let E := sequence D .sphere
  have h200 : HasDifferential E 3 (8,133) (11,135)
      (I.realization.basis .sphere 8 133 0) (I.realization.basis .sphere 11 135 0) := correction_source8_four_h200 I
  have h201 : HasDifferential E 2 (8,133) (10,134)
      (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := correction_source8_four_h201 I
  have h226 : HasDifferential E 3 (9,134) (12,136)
      (I.realization.basis .sphere 9 134 1) (I.realization.basis .sphere 12 136 0) := correction_source8_four_h226 I
  have h227 : HasDifferential E 2 (9,134) (11,135)
      (I.realization.basis .sphere 9 134 0) (I.realization.basis .sphere 11 135 3 + I.realization.basis .sphere 11 135 4) := correction_source8_four_h227 I
  have h228 : HasDifferential E 2 (9,134) (11,135)
      (I.realization.basis .sphere 9 134 4) (I.realization.basis .sphere 11 135 4) := correction_source8_four_h228 I
  have h224 : ReachesPage E 1000 (9,134) (I.realization.basis .sphere 9 134 2) := correction_source8_four_h224 I
  have h225 : ReachesPage E 7 (9,134) (I.realization.basis .sphere 9 134 3) := correction_source8_four_h225 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,8,133,["376,1", "375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 161) (by rfl))
  change E.Page 2 (8,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 8 133 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 8 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 8 133 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 173) (by rfl))
  change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 134 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 9 134 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 9 134 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 9 134 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 9 134 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 9 134 4 := hf 4
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 135 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 11 135 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 11 135 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 11 135 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 11 135 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 11 135 4 := hg 4
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 134 i.val at hk
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 10 134 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 10 134 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 10 134 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 10 134 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 10 134 4 := hk 4
  have dz {p : ℤ×ℤ} {x : E.Page 2 p} {r : ℤ} (hr : 3≤r)
      (hx : ReachesPage E r p x) : E.d 2 p x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega) hb ⟨a,ha⟩
  have hd0 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 0) =
      I.realization.basis .sphere 11 135 3 + I.realization.basis .sphere 11 135 4 := h227.eq_on_page_two.2
  have hd1 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 1) = 0 := by
    obtain ⟨_,x,y,hx,_,_⟩ := h226
    exact dz (by decide) ⟨x,hx⟩
  have hd2 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 2) = 0 := dz (by decide) h224
  have hd3 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 3) = 0 := dz (by decide) h225
  have hd4 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 4) =
      I.realization.basis .sphere 11 135 4 := h228.eq_on_page_two.2
  have incoming_zero (x : E.Page 2 (9,134)) : g (E.d 2 (9,134) x) 0=0 := by
    have hall (a : Fin 5 →₀ F2) : g (E.d 2 (9,134) (f.symm a)) 0=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (9,134) (f.symm (Finsupp.single i 1))) 0=0
          fin_cases i
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 0 1))) 0=0
            simp only [hf0,hd0,map_add,←hg3,←hg4,LinearEquiv.apply_symm_apply,Finsupp.add_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 1 1))) 0=0
            simp only [hf1,hd1,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 2 1))) 0=0
            simp only [hf2,hd2,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 3 1))) 0=0
            simp only [hf3,hd3,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 4 1))) 0=0
            simp only [hf4,hd4,←hg4,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h200
  have hd' : E.d 3 (8,133) a=b := hd
  have hbne : b≠0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (9,134) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (11,135)).Z_anti bot_le) ≫
      (E.ssData (11,135)).pageπ 0) z ∈ LinearMap.range (E.d 2 (9,134)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (11,135)).Z_anti bot_le) ≫
      (E.ssData (11,135)).pageπ 0) z=I.realization.basis .sphere 11 135 0 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming_zero u
    rw [hu,←hg0,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  have hn : E.d 2 (8,133) (e.symm (Finsupp.single 1 1)) ≠ 0 := by
    rw [he1]
    have hh : E.d 2 (8,133) (I.realization.basis .sphere 8 133 1) =
      I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4 := h201.eq_on_page_two.2
    rw [hh]
    intro hz
    have hz' := congrArg (fun x=>k x 2) hz
    simp only [map_add,map_zero,←hk2,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hz'
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hz'
  have frame : ∀ q : E.Page 3 (8,133), q=0 ∨ q=a :=
    frame_after_second (by change (2:ℤ)≤2; omega) (by decide) e (he0.symm ▸ ha) hn
  have ker (q : E.Page 3 (8,133)) (hq : E.d 3 (8,133) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((8,133)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [ker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (8,133)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))


private theorem correction_source9_d4_zero_h226 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,134) (12,136)
    (I.realization.basis .sphere 9 134 1) (I.realization.basis .sphere 12 136 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
    exact List.mem_of_getElem? (i := 226) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,134) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h227 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    (I.realization.basis .sphere 9 134 0) (I.realization.basis .sphere 11 135 3 + I.realization.basis .sphere 11 135 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
    exact List.mem_of_getElem? (i := 227) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h228 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    (I.realization.basis .sphere 9 134 4) (I.realization.basis .sphere 11 135 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
    exact List.mem_of_getElem? (i := 228) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h251 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,134) (10,135)
    (I.realization.basis .sphere 8 134 1) (I.realization.basis .sphere 10 135 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
    exact List.mem_of_getElem? (i := 251) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,134) (10,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h252 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (10,135) (13,137)
    (I.realization.basis .sphere 10 135 0) (I.realization.basis .sphere 13 137 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
    exact List.mem_of_getElem? (i := 252) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (10,135) (13,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h253 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.realization.basis .sphere 10 135 1) (I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
    exact List.mem_of_getElem? (i := 253) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h254 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.realization.basis .sphere 10 135 2) (I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
    exact List.mem_of_getElem? (i := 254) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h255 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.realization.basis .sphere 10 135 4) (I.realization.basis .sphere 12 136 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
    exact List.mem_of_getElem? (i := 255) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h224 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (9,134) (I.realization.basis .sphere 9 134 2) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
    exact List.mem_of_getElem? (i := 224) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (9,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero_h225 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 7 (9,134) (I.realization.basis .sphere 9 134 3) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
    exact List.mem_of_getElem? (i := 225) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 7 (9,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [3] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem correction_source9_d4_zero (I : Inputs D L G) :
    (sequence D .sphere).d 4 (9,134)=0 := by
  classical
  let E := sequence D .sphere
  have h226 : HasDifferential E 3 (9,134) (12,136)
      (I.realization.basis .sphere 9 134 1) (I.realization.basis .sphere 12 136 0) := correction_source9_d4_zero_h226 I
  have h227 : HasDifferential E 2 (9,134) (11,135)
      (I.realization.basis .sphere 9 134 0) (I.realization.basis .sphere 11 135 3 + I.realization.basis .sphere 11 135 4) := correction_source9_d4_zero_h227 I
  have h228 : HasDifferential E 2 (9,134) (11,135)
      (I.realization.basis .sphere 9 134 4) (I.realization.basis .sphere 11 135 4) := correction_source9_d4_zero_h228 I
  have h251 : HasDifferential E 2 (8,134) (10,135)
      (I.realization.basis .sphere 8 134 1) (I.realization.basis .sphere 10 135 3) := correction_source9_d4_zero_h251 I
  have h252 : HasDifferential E 3 (10,135) (13,137)
      (I.realization.basis .sphere 10 135 0) (I.realization.basis .sphere 13 137 0) := correction_source9_d4_zero_h252 I
  have h253 : HasDifferential E 2 (10,135) (12,136)
      (I.realization.basis .sphere 10 135 1) (I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) := correction_source9_d4_zero_h253 I
  have h254 : HasDifferential E 2 (10,135) (12,136)
      (I.realization.basis .sphere 10 135 2) (I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4) := correction_source9_d4_zero_h254 I
  have h255 : HasDifferential E 2 (10,135) (12,136)
      (I.realization.basis .sphere 10 135 4) (I.realization.basis .sphere 12 136 4) := correction_source9_d4_zero_h255 I
  have h224 : ReachesPage E 1000 (9,134) (I.realization.basis .sphere 9 134 2) := correction_source9_d4_zero_h224 I
  have h225 : ReachesPage E 7 (9,134) (I.realization.basis .sphere 9 134 3) := correction_source9_d4_zero_h225 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 173) (by rfl))
  change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 134 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 9 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 9 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 9 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 9 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 9 134 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 135 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 10 135 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 10 135 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 10 135 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 10 135 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 10 135 4 := hf 4
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 136 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 12 136 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 12 136 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 12 136 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 12 136 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 12 136 4 := hg 4
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 135 i.val at hk
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 11 135 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 11 135 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 11 135 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 11 135 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 11 135 4 := hk 4
  have dz {p : ℤ×ℤ} {x : E.Page 2 p} {r : ℤ} (hr : 3≤r)
      (hx : ReachesPage E r p x) : E.d 2 p x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega) hb ⟨a,ha⟩
  have df0 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 0)=0 := by
    obtain ⟨_,a,b,ha,_,_⟩ := h252
    exact dz (by decide) ⟨a,ha⟩
  have df1 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 1)=
      I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2 := h253.eq_on_page_two.2
  have df2 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 2)=
      I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4 := h254.eq_on_page_two.2
  have df3 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 3)=0 := by
    have hh : E.d 2 (8,134) (I.realization.basis .sphere 8 134 1)=I.realization.basis .sphere 10 135 3 := h251.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(8,134)) ⟨_,hh⟩
  have df4 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 4)=
      I.realization.basis .sphere 12 136 4 := h255.eq_on_page_two.2
  have incoming_zero (x : E.Page 2 (10,135)) : g (E.d 2 (10,135) x) 0=0 := by
    have hall (a : Fin 5 →₀ F2) : g (E.d 2 (10,135) (f.symm a)) 0=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (10,135) (f.symm (Finsupp.single i 1))) 0=0
          fin_cases i
          · change g (E.d 2 (10,135) (f.symm (Finsupp.single 0 1))) 0=0
            simp only [hf0,df0,map_zero,map_add,←hg1,←hg2,←hg3,←hg4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply]
            skip
          · change g (E.d 2 (10,135) (f.symm (Finsupp.single 1 1))) 0=0
            simp only [hf1,df1,map_zero,map_add,←hg1,←hg2,←hg3,←hg4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · change g (E.d 2 (10,135) (f.symm (Finsupp.single 2 1))) 0=0
            simp only [hf2,df2,map_zero,map_add,←hg1,←hg2,←hg3,←hg4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · change g (E.d 2 (10,135) (f.symm (Finsupp.single 3 1))) 0=0
            simp only [hf3,df3,map_zero,map_add,←hg1,←hg2,←hg3,←hg4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply]
            skip
          · change g (E.d 2 (10,135) (f.symm (Finsupp.single 4 1))) 0=0
            simp only [hf4,df4,map_zero,map_add,←hg1,←hg2,←hg3,←hg4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a1,b1,ha1,hb1,hd⟩ := h226
  have hd' : E.d 3 (9,134) a1=b1 := hd
  have hbne : b1≠0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb1
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (10,135) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫
      (E.ssData (12,136)).pageπ 0) z ∈ LinearMap.range (E.d 2 (10,135)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫
      (E.ssData (12,136)).pageπ 0) z=I.realization.basis .sphere 12 136 0 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming_zero u
    rw [hu,←hg0,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000) h224.choose_spec
  obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤7) h225.choose_spec
  obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) h224.choose_spec
  obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤7) h225.choose_spec
  have hd32 : E.d 3 (9,134) a2=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) ha2 h224
  have hd33 : E.d 3 (9,134) a3=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) ha3 h225
  have hd42 : E.d 4 (9,134) b2=0 := represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide) hb2 h224
  have hd43 : E.d 4 (9,134) b3=0 := represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide) hb3 h225
  have hd0 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 0)=
      I.realization.basis .sphere 11 135 3 + I.realization.basis .sphere 11 135 4 := h227.eq_on_page_two.2
  have hd1 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 1)=0 := dz (by decide) ⟨a1,ha1⟩
  have hd2 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 2)=0 := dz (by decide) h224
  have hd3 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 3)=0 := dz (by decide) h225
  have hd4 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 4)=I.realization.basis .sphere 11 135 4 := h228.eq_on_page_two.2
  ext a
  change E.d 4 (9,134) a=0
  let A := E.ssData (9,134)
  haveI : Epi (A.pageπ 2) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hza⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 2)).mp inferInstance a
  let x : E.Page 2 (9,134) := (Subobject.ofLE _ _ (A.Z_anti (by decide : (0:WithTop ℕ)≤2)) ≫ A.pageπ 0) z
  have hxa : RepresentsOnPage E 4 (9,134) x a := ⟨by decide,z,rfl,hza⟩
  have hc : E.d 2 (9,134) x=0 := dz (by decide) ⟨a,hxa⟩
  have heq : e x = Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  generalize hc4 : e x 4=c4 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    rw [represents_unique hxa (RepresentsOnPage.zero (by decide : (2:ℤ)≤4)),map_zero]
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he3] at hc hxa
    rw [represents_unique hxa (hb3)]
    simp only [map_add,hd42,hd43,add_zero]
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he3, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he2] at hc hxa
    rw [represents_unique hxa (hb2)]
    simp only [map_add,hd42,hd43,add_zero]
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he2, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he2, he3] at hc hxa
    rw [represents_unique hxa (represents_add_tail (hb2) hb3)]
    simp only [map_add,hd42,hd43,add_zero]
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he2, he3, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1] at hc hxa
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) (ha1) ⟨a,hxa⟩
    exact (hbne (by simpa only [map_add,hd',hd32,hd33,add_zero] using hh)).elim
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he3] at hc hxa
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) (represents_add_tail (ha1) ha3) ⟨a,hxa⟩
    exact (hbne (by simpa only [map_add,hd',hd32,hd33,add_zero] using hh)).elim
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he3, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he2] at hc hxa
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) (represents_add_tail (ha1) ha2) ⟨a,hxa⟩
    exact (hbne (by simpa only [map_add,hd',hd32,hd33,add_zero] using hh)).elim
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he2, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he2, he3] at hc hxa
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) (represents_add_tail (represents_add_tail (ha1) ha2) ha3) ⟨a,hxa⟩
    exact (hbne (by simpa only [map_add,hd',hd32,hd33,add_zero] using hh)).elim
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he1, he2, he3, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 4) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he3] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he3, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he2] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he2, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he2, he3] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he2, he3, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he3] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he3, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he2] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he2, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he2, he3] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hc hxa
    simp only [he0, he1, he2, he3, he4] at hc hxa
    simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
    have hh := congrArg (fun y=>k y 3) hc
    simp only [map_add,map_zero,←hk3,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hh


private theorem correction_incoming3_h251 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,134) (10,135)
    (I.realization.basis .sphere 8 134 1) (I.realization.basis .sphere 10 135 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
    exact List.mem_of_getElem? (i := 251) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,134) (10,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_incoming3_h252 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (10,135) (13,137)
    (I.realization.basis .sphere 10 135 0) (I.realization.basis .sphere 13 137 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
    exact List.mem_of_getElem? (i := 252) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (10,135) (13,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_incoming3_h253 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.realization.basis .sphere 10 135 1) (I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
    exact List.mem_of_getElem? (i := 253) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_incoming3_h254 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.realization.basis .sphere 10 135 2) (I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
    exact List.mem_of_getElem? (i := 254) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_incoming3_h255 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.realization.basis .sphere 10 135 4) (I.realization.basis .sphere 12 136 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
    exact List.mem_of_getElem? (i := 255) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_incoming3 (I : Inputs D L G) :
    ∃ b : (sequence D .sphere).Page 3 (13,137),
      RepresentsOnPage (sequence D .sphere) 3 (13,137) (I.realization.basis .sphere 13 137 0) b ∧
      ∀ a : (sequence D .sphere).Page 3 (10,135),
        (sequence D .sphere).d 3 (10,135) a=0 ∨ (sequence D .sphere).d 3 (10,135) a=b := by
  classical
  let E := sequence D .sphere
  have h251 : HasDifferential E 2 (8,134) (10,135)
      (I.realization.basis .sphere 8 134 1) (I.realization.basis .sphere 10 135 3) := correction_incoming3_h251 I
  have h252 : HasDifferential E 3 (10,135) (13,137)
      (I.realization.basis .sphere 10 135 0) (I.realization.basis .sphere 13 137 0) := correction_incoming3_h252 I
  have h253 : HasDifferential E 2 (10,135) (12,136)
      (I.realization.basis .sphere 10 135 1) (I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) := correction_incoming3_h253 I
  have h254 : HasDifferential E 2 (10,135) (12,136)
      (I.realization.basis .sphere 10 135 2) (I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4) := correction_incoming3_h254 I
  have h255 : HasDifferential E 2 (10,135) (12,136)
      (I.realization.basis .sphere 10 135 4) (I.realization.basis .sphere 12 136 4) := correction_incoming3_h255 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 135 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 10 135 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 10 135 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 10 135 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 10 135 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 10 135 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 136 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 12 136 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 12 136 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 12 136 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 12 136 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 12 136 4 := hf 4
  obtain ⟨_,a0,b0,ha0,hb0,hd⟩ := h252
  have hd' : E.d 3 (10,135) a0=b0 := hd
  have hz3 : RepresentsOnPage E 3 (10,135) (I.realization.basis .sphere 10 135 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h251
  have dz {p : ℤ×ℤ} {x : E.Page 2 p} (hx : ReachesPage E 3 p x) : E.d 2 p x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) ha
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨a,ha⟩
  have hd0 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 0)=0 := dz ⟨a0,ha0⟩
  have hd1 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 1)=
      I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2 := h253.eq_on_page_two.2
  have hd2 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 2)=
      I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4 := h254.eq_on_page_two.2
  have hd3 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 3)=0 := dz ⟨0,hz3⟩
  have hd4 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 4)=
      I.realization.basis .sphere 12 136 4 := h255.eq_on_page_two.2
  have frame (a : E.Page 3 (10,135)) : a=0 ∨ a=a0 := by
    let A := E.ssData (10,135)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hza⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance a
    let x : E.Page 2 (10,135) := (Subobject.ofLE _ _ (A.Z_anti (by decide : (0:WithTop ℕ)≤1)) ≫ A.pageπ 0) z
    have hxa : RepresentsOnPage E 3 (10,135) x a := ⟨by decide,z,rfl,hza⟩
    have hc : E.d 2 (10,135) x=0 := dz ⟨a,hxa⟩
    have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [Finsupp.single_apply]
    have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    generalize hc2 : e x 2=c2 at hxe
    generalize hc3 : e x 3=c3 at hxe
    generalize hc4 : e x 4=c4 at hxe
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      exact Or.inl (represents_unique hxa (RepresentsOnPage.zero (by decide : (2:ℤ)≤3)))
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he3] at hc hxa
      exact Or.inl (represents_unique hxa hz3)
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2, he3] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2, he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he3] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2, he3] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2, he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0] at hc hxa
      exact Or.inr (represents_unique hxa ha0)
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he3] at hc hxa
      exact Or.inr (by simpa only [add_zero] using represents_unique hxa (represents_add_tail ha0 hz3))
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2, he3] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2, he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he3] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2, he3] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2, he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  refine ⟨b0,hb0,?_⟩
  intro a
  rcases frame a with rfl|rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr hd'


private theorem correction_nonzero_four_h279 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    (I.realization.basis .sphere 8 134 3) (I.realization.basis .sphere 11 136 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2850⟩ (by
    exact List.mem_of_getElem? (i := 279) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_nonzero_four_h280 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    (I.realization.basis .sphere 8 134 2) (I.realization.basis .sphere 11 136 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,8,134,[2],11,136,[2],"S0_AdamsE2_ss",2851⟩ (by
    exact List.mem_of_getElem? (i := 280) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_nonzero_four_h282 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (11,136) (15,139)
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

private theorem correction_nonzero_four_h283 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,136) (13,137)
    (I.realization.basis .sphere 11 136 4) (I.realization.basis .sphere 13 137 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2854⟩ (by
    exact List.mem_of_getElem? (i := 283) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,136) (13,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem correction_nonzero_four_h281 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 5 (11,136) (I.realization.basis .sphere 11 136 3) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,5,11,136,[3],11,136,[],"S0_AdamsE2_ss",2852⟩ (by
    exact List.mem_of_getElem? (i := 281) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 5 (11,136) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [3] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem correction_nonzero_four (I : Inputs D L G)
    {a : (sequence D .sphere).Page 4 (13,137)}
    (ha : RepresentsOnPage (sequence D .sphere) 4 (13,137)
      (I.realization.basis .sphere 13 137 1) a) : a≠0 := by
  classical
  let E := sequence D .sphere
  have h279 : HasDifferential E 3 (8,134) (11,136)
      (I.realization.basis .sphere 8 134 3) (I.realization.basis .sphere 11 136 1) := correction_nonzero_four_h279 I
  have h280 : HasDifferential E 3 (8,134) (11,136)
      (I.realization.basis .sphere 8 134 2) (I.realization.basis .sphere 11 136 2) := correction_nonzero_four_h280 I
  have h282 : HasDifferential E 4 (11,136) (15,139)
      (I.realization.basis .sphere 11 136 0) (I.realization.basis .sphere 15 139 0) := correction_nonzero_four_h282 I
  have h283 : HasDifferential E 2 (11,136) (13,137)
      (I.realization.basis .sphere 11 136 4) (I.realization.basis .sphere 13 137 3) := correction_nonzero_four_h283 I
  have h281 : ReachesPage E 5 (11,136) (I.realization.basis .sphere 11 136 3) := correction_nonzero_four_h281 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 137 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.realization.basis .sphere 13 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.realization.basis .sphere 13 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.realization.basis .sphere 13 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.realization.basis .sphere 13 137 3 := he 3
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 192) (by rfl))
  change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 136 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 11 136 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 11 136 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 11 136 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 11 136 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 11 136 4 := hf 4
  let ell (x : E.Page 2 (13,137)) : F2 := e x 1
  have hsub {r : ℤ} {p : ℤ×ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have dz {p : ℤ×ℤ} {x : E.Page 2 p} {r : ℤ} (hr : 3≤r)
      (hx : ReachesPage E r p x) : E.d 2 p x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega) hb ⟨a,ha⟩
  have hd0 : E.d 2 (11,136) (I.realization.basis .sphere 11 136 0)=0 := by
    obtain ⟨_,a,b,ha,_,_⟩ := h282
    exact dz (by decide) ⟨a,ha⟩
  have hd1 : E.d 2 (11,136) (I.realization.basis .sphere 11 136 1)=0 := by
    obtain ⟨_,a,b,_,hb,_⟩ := h279
    exact dz (by decide) ⟨b,hb⟩
  have hd2 : E.d 2 (11,136) (I.realization.basis .sphere 11 136 2)=0 := by
    obtain ⟨_,a,b,_,hb,_⟩ := h280
    exact dz (by decide) ⟨b,hb⟩
  have hd3 : E.d 2 (11,136) (I.realization.basis .sphere 11 136 3)=0 := dz (by decide) h281
  have hd4 : E.d 2 (11,136) (I.realization.basis .sphere 11 136 4)=I.realization.basis .sphere 13 137 3 := h283.eq_on_page_two.2
  have incoming_zero (x : E.Page 2 (11,136)) : ell (E.d 2 (11,136) x)=0 := by
    have hall (a : Fin 5 →₀ F2) : ell (E.d 2 (11,136) (f.symm a))=0 := by
      dsimp only [ell]
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change e (E.d 2 (11,136) (f.symm (Finsupp.single i 1))) 1=0
          fin_cases i
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 0 1))) 1=0
            simp only [hf0,hd0,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 1 1))) 1=0
            simp only [hf1,hd1,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 2 1))) 1=0
            simp only [hf2,hd2,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 3 1))) 1=0
            simp only [hf3,hd3,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 4 1))) 1=0
            rw [hf4,hd4,←he3,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  have nz3 {x : E.Page 2 (13,137)} (hx : ell x=1) {a : E.Page 3 (13,137)}
      (ha : RepresentsOnPage E 3 (13,137) x a) : a≠0 := by
    intro ha0
    obtain ⟨_,z,hz2,hz3⟩ := ha
    obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (11,136) z).mp (hz3.trans ha0)
    change E.d 2 (11,136) u = (Subobject.ofLE _ _ ((E.ssData (13,137)).Z_anti bot_le) ≫ (E.ssData (13,137)).pageπ 0) z at hu
    change (Subobject.ofLE _ _ ((E.ssData (13,137)).Z_anti bot_le) ≫ (E.ssData (13,137)).pageπ 0) z=x at hz2
    have hh := incoming_zero u
    rw [hu,hz2,hx] at hh
    exact one_ne_zero hh
  obtain ⟨b0,hb0,hin3⟩ := correction_incoming3 I
  obtain ⟨_,z,hz2,hz4⟩ := ha
  let A := E.ssData (13,137)
  let i := Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2))
  let a3 := A.pageπ 1 (i z)
  have ha3 : RepresentsOnPage E 3 (13,137) (I.realization.basis .sphere 13 137 1) a3 := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have heOne : ell (I.realization.basis .sphere 13 137 1)=1 := by
    dsimp only [ell]
    rw [←he1,LinearEquiv.apply_symm_apply]
    simp
  have hane : a3≠0 := nz3 heOne ha3
  have hab : a3≠b0 := by
    intro hab
    have hx : ell (I.realization.basis .sphere 13 137 1-I.realization.basis .sphere 13 137 0)=1 := by
      dsimp only [ell]
      rw [map_sub,←he1,←he0,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
      norm_num [Finsupp.sub_apply,Finsupp.single_apply,Fin.ext_iff]
    exact nz3 hx (hsub ha3 hb0) (sub_eq_zero.mpr hab)
  intro ha0
  obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 3 (by change (2:ℤ)≤3; omega) (10,135) z).mp (hz4.trans ha0)
  change E.d 3 (10,135) u=a3 at hu
  rcases hin3 u with h|h
  · exact hane (hu.symm.trans h)
  · exact hab (hu.symm.trans h)


private theorem stem125_af6_e5_zero_h157 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (4,130) (7,132) (I.realization.basis .sphere 4 130 0) (I.realization.basis .sphere 7 132 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "S0_AdamsE2_ss", 2437⟩ (by
    exact List.mem_of_getElem? (i := 157) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (4,130) (7,132) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h163 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (5,130) (7,131) (I.realization.basis .sphere 5 130 0) (I.realization.basis .sphere 7 131 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 5, 130, [0], 7, 131, [2], "S0_AdamsE2_ss", 2435⟩ (by
    exact List.mem_of_getElem? (i := 163) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,130) (7,131) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h171 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 0) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 3) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3], "S0_AdamsE2_ss", 2492⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h172 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 1) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 1 + I.realization.basis .sphere 10 134 3 + I.realization.basis .sphere 10 134 4) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4], "S0_AdamsE2_ss", 2493⟩ (by
    exact List.mem_of_getElem? (i := 172) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h200 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,133) (11,135) (I.realization.basis .sphere 8 133 0) (I.realization.basis .sphere 11 135 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2629⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,133) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h201 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,133) (10,134) (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "S0_AdamsE2_ss", 2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,133) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem125_af6_e5_zero_h249 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (10,134) (I.realization.basis .sphere 10 134 4) := by
  classical
  have hrow := I.results ⟨.sphere, .reaches, 1000, 10, 134, [4], 10, 134, [], "S0_AdamsE2_ss", 2693⟩ (by
    exact List.mem_of_getElem? (i := 249) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [4] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem stem125_af6_e5_zero (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (6,131)) := by
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
  obtain ⟨e8_133,he8_133⟩ := I.basis ⟨.sphere, 8, 133, ["376,1", "375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 161) (by rfl))
  change E.Page 2 (8,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e8_133
  change ∀i : Fin 2, e8_133.symm (Finsupp.single i 1) = I.realization.basis .sphere 8 133 i.val at he8_133
  have he8_133_0 : e8_133.symm (Finsupp.single 0 1) = I.realization.basis .sphere 8 133 0 := he8_133 0
  have he8_133_1 : e8_133.symm (Finsupp.single 1 1) = I.realization.basis .sphere 8 133 1 := he8_133 1
  obtain ⟨e7_132,he7_132⟩ := I.basis ⟨.sphere, 7, 132, ["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e7_132
  change ∀i : Fin 1, e7_132.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 132 i.val at he7_132
  have he7_132_0 : e7_132.symm (Finsupp.single 0 1) = I.realization.basis .sphere 7 132 0 := he7_132 0
  obtain ⟨e6_131,he6_131⟩ := I.basis ⟨.sphere, 6, 131, ["69,1,76,1", "0,1,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 137) (by rfl))
  change E.Page 2 (6,131) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e6_131
  change ∀i : Fin 2, e6_131.symm (Finsupp.single i 1) = I.realization.basis .sphere 6 131 i.val at he6_131
  have he6_131_0 : e6_131.symm (Finsupp.single 0 1) = I.realization.basis .sphere 6 131 0 := he6_131 0
  have he6_131_1 : e6_131.symm (Finsupp.single 1 1) = I.realization.basis .sphere 6 131 1 := he6_131 1
  obtain ⟨e5_130,he5_130⟩ := I.basis ⟨.sphere, 5, 130, ["340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 126) (by rfl))
  change E.Page 2 (5,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e5_130
  change ∀i : Fin 1, e5_130.symm (Finsupp.single i 1) = I.realization.basis .sphere 5 130 i.val at he5_130
  have he5_130_0 : e5_130.symm (Finsupp.single 0 1) = I.realization.basis .sphere 5 130 0 := he5_130 0
  obtain ⟨e7_131,he7_131⟩ := I.basis ⟨.sphere, 7, 131, ["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e7_131
  change ∀i : Fin 3, e7_131.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 131 i.val at he7_131
  have he7_131_0 : e7_131.symm (Finsupp.single 0 1) = I.realization.basis .sphere 7 131 0 := he7_131 0
  have he7_131_1 : e7_131.symm (Finsupp.single 1 1) = I.realization.basis .sphere 7 131 1 := he7_131 1
  have he7_131_2 : e7_131.symm (Finsupp.single 2 1) = I.realization.basis .sphere 7 131 2 := he7_131 2
  have h157 : HasDifferential E 3 (4,130) (7,132) (I.realization.basis .sphere 4 130 0) (I.realization.basis .sphere 7 132 0) := stem125_af6_e5_zero_h157 I
  have h163 : HasDifferential E 2 (5,130) (7,131) (I.realization.basis .sphere 5 130 0) (I.realization.basis .sphere 7 131 2) := stem125_af6_e5_zero_h163 I
  have h171 : HasDifferential E 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 0) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 3) := stem125_af6_e5_zero_h171 I
  have h172 : HasDifferential E 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 1) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 1 + I.realization.basis .sphere 10 134 3 + I.realization.basis .sphere 10 134 4) := stem125_af6_e5_zero_h172 I
  have h200 : HasDifferential E 3 (8,133) (11,135) (I.realization.basis .sphere 8 133 0) (I.realization.basis .sphere 11 135 0) := stem125_af6_e5_zero_h200 I
  have h201 : HasDifferential E 2 (8,133) (10,134) (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := stem125_af6_e5_zero_h201 I
  have h249 : ReachesPage E 1000 (10,134) (I.realization.basis .sphere 10 134 4) := stem125_af6_e5_zero_h249 I
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
  have generated_one {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2)) (a : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (x : E.Page r p) : x=0 ∨ x=a := by
    exact FinitePageCalculus.generated_one hr e a ha x
  have generated_two {r : ℤ} (hr : 2≤r) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ F2)) (a b : E.Page r p)
      (ha : RepresentsOnPage E r p (e.symm (Finsupp.single 0 1)) a)
      (hb : RepresentsOnPage E r p (e.symm (Finsupp.single 1 1)) b)
      (x : E.Page r p) : x=0 ∨ x=a ∨ x=b ∨ x=a+b := by
    exact FinitePageCalculus.generated_two hr e a b ha hb x
  have incoming2 (x : E.Page 2 (8,133)) : E.d 2 (8,133) x=0 ∨
      E.d 2 (8,133) x=I.realization.basis .sphere 10 134 2+I.realization.basis .sphere 10 134 4 := by
    obtain ⟨_,a,b,ha,hb,hd⟩ := h200
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a,ha⟩
    have d1 := h201.eq_on_page_two.2
    change E.d 2 (8,133) (I.realization.basis .sphere 8 133 1)=_ at d1
    have h := generated_two (by decide : (2:ℤ)≤2) e8_133 _ _
      (by rw [he8_133_0]; exact hrep2 _) (by rw [he8_133_1]; exact hrep2 _) x
    rcases h with h|h|h|h
    · exact Or.inl (by rw [h,map_zero])
    · exact Or.inl (by rw [h,d0])
    · exact Or.inr (by rw [h,d1])
    · exact Or.inr (by rw [h,map_add,d0,d1,zero_add])
  have incoming3 : E.d 3 (7,132)=0 := by
    obtain ⟨_,a,b,ha,hb,hd⟩ := h157
    have hd0 : E.d 3 (7,132) b=0 := IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(4,130)) ⟨a,hd⟩
    ext x
    rcases generated_one (by decide : (2:ℤ)≤3) e7_132 b (by rw [he7_132_0]; exact hb) x with h|h
    · simp only [h,map_zero,ModuleCat.hom_zero,LinearMap.zero_apply]
    · simp only [h,hd0,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a4,y4,ha4,hy4,hda4⟩ := h171
  obtain ⟨_,b4,z4,hb4,hz4,hdb4⟩ := h172
  have incoming4 (x : E.Page 4 (6,131)) : E.d 4 (6,131) x=0 ∨ E.d 4 (6,131) x=y4 ∨
      E.d 4 (6,131) x=z4 ∨ E.d 4 (6,131) x=y4+z4 := by
    have da : E.d 4 (6,131) a4=y4 := hda4
    have db : E.d 4 (6,131) b4=z4 := hdb4
    rcases generated_two (by decide : (2:ℤ)≤4) e6_131 a4 b4
      (by rw [he6_131_0]; exact ha4) (by rw [he6_131_1]; exact hb4) x with h|h|h|h
    · exact Or.inl (by rw [h,map_zero])
    · exact Or.inr (Or.inl (by rw [h,da]))
    · exact Or.inr (Or.inr (Or.inl (by rw [h,db])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h,map_add,da,db])))
  have nonzero3_coord {x : E.Page 2 (10,134)} (j : Fin 5) (hj : j=0 ∨ j=1)
      (hx : e10_134 x j ≠ 0) {a : E.Page 3 (10,134)}
      (ha : RepresentsOnPage E 3 (10,134) x a) : a≠0 := by
    obtain ⟨_,z,hz2,hz3⟩ := ha
    intro ha0
    obtain ⟨b,hb⟩ := (next_projection_zero_iff_incoming E 2
      (by change (2:ℤ)≤2;omega) (8,133) z).mp (hz3.trans ha0)
    have he : E.d 2 (8,133) b=x := hb.trans hz2
    apply hx
    rcases incoming2 b with h|h
    · rw [←he,h,map_zero]
      rfl
    · rw [←he,h,←he10_134_2,←he10_134_4,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
      rcases hj with rfl|rfl <;> simp
  have nonzero4_coord {x : E.Page 2 (10,134)} (j : Fin 5) (hj : j=0 ∨ j=1)
      (hx : e10_134 x j≠0) {a : E.Page 4 (10,134)}
      (ha : RepresentsOnPage E 4 (10,134) x a) : a≠0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    exact represents_next_nonzero_of_incoming_zero_at
      (by change (2:ℤ)≤3;omega) (by decide : (2:ℤ)≤3) (by exact incoming3) ha hb
      (nonzero3_coord j hj hx hb)
  have yn : y4≠0 := nonzero4_coord 0 (Or.inl rfl) (by
    rw [←he10_134_0,←he10_134_3,map_add,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    simp) hy4
  have zn : z4≠0 := nonzero4_coord 1 (Or.inr rfl) (by
    rw [←he10_134_0,←he10_134_1,←he10_134_3,←he10_134_4]
    simp only [map_add,LinearEquiv.apply_symm_apply,Finsupp.add_apply]
    simp) hz4
  have yzn : y4+z4≠0 := nonzero4_coord 1 (Or.inr rfl) (by
    rw [←he10_134_0,←he10_134_1,←he10_134_3,←he10_134_4]
    simp only [map_add,LinearEquiv.apply_symm_apply,Finsupp.add_apply]
    simp) (hadd hy4 hz4)
  have da : E.d 4 (6,131) a4=y4 := hda4
  have db : E.d 4 (6,131) b4=z4 := hdb4
  have ker (x : E.Page 4 (6,131)) (hx : E.d 4 (6,131) x=0) : x=0 := by
    rcases generated_two (by decide : (2:ℤ)≤4) e6_131 a4 b4
      (by rw [he6_131_0];exact ha4) (by rw [he6_131_1];exact hb4) x with h|h|h|h
    · exact h
    · exact (yn (by simpa only [h,da] using hx)).elim
    · exact (zn (by simpa only [h,db] using hx)).elim
    · exact (yzn (by simpa only [h,map_add,da,db] using hx)).elim
  have hinj : Function.Injective (E.d 4 (6,131)) := (injective_iff_map_eq_zero _).mpr ker
  let S := E.pageShortComplex 4 ((6,131)-E.diffDeg 4)
  have hs : Function.Injective S.g := hinj
  have hsex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro z hz
    have hz0 : z=0 := hs (hz.trans (map_zero _).symm)
    exact ⟨0,by simpa [hz0]⟩)
  have hzero := (S.exact_iff_isZero_homology).mp hsex
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 4 (6,131)
    (by change (2:ℤ)≤4;omega)).isZero_iff.mpr hzero)


private theorem tail_af5_h163 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (5,130) (7,131)
    (I.realization.basis .sphere 5 130 0) (I.realization.basis .sphere 7 131 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,5,130,[0],7,131,[2],"S0_AdamsE2_ss",2435⟩ (by
    exact List.mem_of_getElem? (i := 163) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,130) (7,131) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af5 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (5,130)) := by
  classical
  let E := sequence D .sphere
  have h163 : HasDifferential E 2 (5,130) (7,131)
      (I.realization.basis .sphere 5 130 0) (I.realization.basis .sphere 7 131 2) := tail_af5_h163 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,5,130,["340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 126) (by rfl))
  change E.Page 2 (5,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 5 130 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 5 130 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,7,131,["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 131 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 7 131 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 7 131 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 7 131 2 := hf 2
  have hd0 : E.d 2 (5,130) (I.realization.basis .sphere 5 130 0) =
      I.realization.basis .sphere 7 131 2 := h163.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (5,130)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(5,130)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 2) hx
    simp only [map_add, map_zero, ←hf2, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval


private theorem tail_af7_h157 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (4,130) (7,132)
    (I.realization.basis .sphere 4 130 0) (I.realization.basis .sphere 7 132 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,4,130,[0],7,132,[0],"S0_AdamsE2_ss",2437⟩ (by
    exact List.mem_of_getElem? (i := 157) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (4,130) (7,132) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af7 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (7,132)) := by
  classical
  let E := sequence D .sphere
  have h157 : HasDifferential E 3 (4,130) (7,132)
      (I.realization.basis .sphere 4 130 0) (I.realization.basis .sphere 7 132 0) := tail_af7_h157 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,7,132,["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 132 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 7 132 0 := he 0
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) h157


private theorem correction_survives1000_h323 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (13,137) (I.realization.basis .sphere 13 137 1) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,1000,13,137,[1],13,137,[],"S0_AdamsE2_ss",2916⟩ (by
    exact List.mem_of_getElem? (i := 323) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (13,137) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [1] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem correction_survives1000 (I : Inputs D L G) :
    SurvivesTo (sequence D .sphere) 1000 (13,137) (I.realization.basis .sphere 13 137 1) := by
  classical
  let E := sequence D .sphere
  have h323 : ReachesPage E 1000 (13,137) (I.realization.basis .sphere 13 137 1) := correction_survives1000_h323 I
  have empty (s : ℕ) (hs : s≤4) : Subsingleton (E.Page 2 (s,(s:ℤ)+125)) := by
    interval_cases s
    · change Subsingleton (E.Page 2 (0,125))
      obtain ⟨e,he⟩ := I.basis ⟨.sphere,0,125,[]⟩ (by
        exact List.mem_of_getElem? (i := 76) (by rfl))
      change E.Page 2 (0,125) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 0 125 i.val at he
      exact e.injective.subsingleton
    · change Subsingleton (E.Page 2 (1,126))
      obtain ⟨e,he⟩ := I.basis ⟨.sphere,1,126,[]⟩ (by
        exact List.mem_of_getElem? (i := 89) (by rfl))
      change E.Page 2 (1,126) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 1 126 i.val at he
      exact e.injective.subsingleton
    · change Subsingleton (E.Page 2 (2,127))
      obtain ⟨e,he⟩ := I.basis ⟨.sphere,2,127,[]⟩ (by
        exact List.mem_of_getElem? (i := 99) (by rfl))
      change E.Page 2 (2,127) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 2 127 i.val at he
      exact e.injective.subsingleton
    · change Subsingleton (E.Page 2 (3,128))
      obtain ⟨e,he⟩ := I.basis ⟨.sphere,3,128,[]⟩ (by
        exact List.mem_of_getElem? (i := 107) (by rfl))
      change E.Page 2 (3,128) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 3 128 i.val at he
      exact e.injective.subsingleton
    · change Subsingleton (E.Page 2 (4,129))
      obtain ⟨e,he⟩ := I.basis ⟨.sphere,4,129,[]⟩ (by
        exact List.mem_of_getElem? (i := 118) (by rfl))
      change E.Page 2 (4,129) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
      change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 4 129 i.val at he
      exact e.injective.subsingleton
  have incoming_late (r : ℤ) (hr : 4≤r) : E.d r ((13,137)-E.diffDeg r)=0 := by
    by_cases h9 : r<9
    · have hrs : r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 := by omega
      rcases hrs with rfl|rfl|rfl|rfl|rfl
      · exact correction_source9_d4_zero I
      · have he : Subsingleton (E.Page 5 (8,133)) :=
          adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 5 8 133
            (by decide) (by decide) (correction_source8_four I)
        ext x
        change E.d 5 (8,133) x=0
        rw [he.elim x 0,map_zero]
      · have he : Subsingleton (E.Page 6 (7,132)) :=
          adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 6 7 132
            (by decide) (by decide) (tail_af7 I)
        ext x
        change E.d 6 (7,132) x=0
        rw [he.elim x 0,map_zero]
      · have he : Subsingleton (E.Page 7 (6,131)) :=
          adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 7 6 131
            (by decide) (by decide) (stem125_af6_e5_zero I)
        ext x
        change E.d 7 (6,131) x=0
        rw [he.elim x 0,map_zero]
      · have he : Subsingleton (E.Page 8 (5,130)) :=
          adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 5 8 5 130
            (by decide) (by decide) (tail_af5 I)
        ext x
        change E.d 8 (5,130) x=0
        rw [he.elim x 0,map_zero]
    · by_cases h14 : 14≤r
      · have he : Subsingleton (E.Page r (13-r,138-r)) :=
          adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r (13-r) (138-r) (by omega)
        ext x
        change E.d r (13-r,137-(r-1)) x=0
        have he' : Subsingleton (E.Page r (13-r,137-(r-1))) := by
          have ht : (137:ℤ)-(r-1)=138-r := by omega
          simpa only [ht] using he
        rw [he'.elim x 0,map_zero]
      · have hr9 : 9≤r := by omega
        have hr13 : r≤13 := by omega
        interval_cases r
        · have he : Subsingleton (E.Page 9 (4,129)) :=
            adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 9 4 129
              (by decide) (by decide) (empty 4 (by decide))
          ext x
          change E.d 9 (4,129) x=0
          rw [he.elim x 0,map_zero]
        · have he : Subsingleton (E.Page 10 (3,128)) :=
            adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 10 3 128
              (by decide) (by decide) (empty 3 (by decide))
          ext x
          change E.d 10 (3,128) x=0
          rw [he.elim x 0,map_zero]
        · have he : Subsingleton (E.Page 11 (2,127)) :=
            adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 11 2 127
              (by decide) (by decide) (empty 2 (by decide))
          ext x
          change E.d 11 (2,127) x=0
          rw [he.elim x 0,map_zero]
        · have he : Subsingleton (E.Page 12 (1,126)) :=
            adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 12 1 126
              (by decide) (by decide) (empty 1 (by decide))
          ext x
          change E.d 12 (1,126) x=0
          rw [he.elim x 0,map_zero]
        · have he : Subsingleton (E.Page 13 (0,125)) :=
            adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 13 0 125
              (by decide) (by decide) (empty 0 (by decide))
          ext x
          change E.d 13 (0,125) x=0
          rw [he.elim x 0,map_zero]
  obtain ⟨a,ha⟩ := h323
  refine ⟨a,ha,?_⟩
  obtain ⟨_,z,hz2,hza⟩ := ha
  let A := E.ssData (13,137)
  let i := Subobject.ofLE (A.Z 998) (A.Z 2) (A.Z_anti (by decide : (2:WithTop ℕ)≤998))
  have rep4 : RepresentsOnPage E 4 (13,137) (I.realization.basis .sphere 13 137 1) (A.pageπ 2 (i z)) := by
    refine ⟨by decide,i z,?_,rfl⟩
    change (i ≫ Subobject.ofLE (A.Z 2) (A.Z 0) _ ≫ A.pageπ 0) z = _
    dsimp only [i]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have hB : A.B ⊤=A.B 2 := boundaries_top_eq_of_d_eq_zero E 4 (by change (2:ℤ)≤4; omega) (13,137) incoming_late
  intro ha0
  have hb := (subobject_cokernel_π_eq_zero_iff (A.B 998) (A.Z 998) (A.B_le_Z _) z).mp (hza.trans ha0)
  have hb' := (ModuleCat.subobjectModule A.V).monotone (A.B_mono (show (998:WithTop ℕ)≤⊤ from le_top)) hb
  rw [hB] at hb'
  apply correction_nonzero_four I rep4
  apply (subobject_cokernel_π_eq_zero_iff (A.B 2) (A.Z 2) (A.B_le_Z _) (i z)).mpr
  change (i ≫ (A.Z 2).arrow) z ∈ _
  dsimp only [i]
  rwa [Subobject.ofLE_arrow]


private theorem named_correction_survives1000 (I : Inputs D L G) :
    Derived.Survival I.realization 1000 correction := by
  classical

  have correction_label : I.realization.sphere 13 137 correction = I.realization.basis .sphere 13 137 1 := by
    have hmem : (⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
      exact List.mem_of_getElem? (i := 208) (by rfl)
    have hc := I.csv _ hmem rfl
    obtain ⟨z,hz,he⟩ := hc (1 : Fin 4)
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
  change SurvivesTo (sequence D .sphere) 1000 (13,137) _
  rw [correction_label]
  exact correction_survives1000 I


/-- Finite candidate/boundary reconstruction, including all linear
combinations.  These four claims require more than their four level-9000 rows:
use the complete basis and incoming staircase equations in the same Inputs. -/
theorem named_survive1000 (I : Inputs D L G) :
    Derived.Survival I.realization 1000 U ∧
    Derived.Survival I.realization 1000 correction ∧
    Derived.Survival I.realization 1000 P ∧
    Derived.Survival I.realization 1000 Q := by
  obtain ⟨hu,hp,hq⟩ := named_upq_survives1000 I
  exact ⟨hu,named_correction_survives1000 I,hp,hq⟩
end

section
open CategoryTheory.Limits KIP126.Core.Algebra KIP126.Computation.Near126 in
/-- The two depth-1 T rows refute zero and one excluded E3 target.
The conclusion requires reconstruction of the whole actual E3 target group
from the basis and d2 rows, not a claim that retained trials were exhaustive. -/
private theorem candidates_raw_h226 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,134) (12,136)
    ((I.realization.basis .sphere 9 134 1)) ((I.realization.basis .sphere 12 136 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
    exact List.mem_of_getElem? (i := 226) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,134) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h227 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    ((I.realization.basis .sphere 9 134 0)) ((I.realization.basis .sphere 11 135 3) + (I.realization.basis .sphere 11 135 4)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
    exact List.mem_of_getElem? (i := 227) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h228 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    ((I.realization.basis .sphere 9 134 4)) ((I.realization.basis .sphere 11 135 4)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
    exact List.mem_of_getElem? (i := 228) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h251 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,134) (10,135)
    ((I.realization.basis .sphere 8 134 1)) ((I.realization.basis .sphere 10 135 3)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
    exact List.mem_of_getElem? (i := 251) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,134) (10,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h252 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (10,135) (13,137)
    ((I.realization.basis .sphere 10 135 0)) ((I.realization.basis .sphere 13 137 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
    exact List.mem_of_getElem? (i := 252) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (10,135) (13,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h253 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    ((I.realization.basis .sphere 10 135 1)) ((I.realization.basis .sphere 12 136 1) + (I.realization.basis .sphere 12 136 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
    exact List.mem_of_getElem? (i := 253) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h254 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    ((I.realization.basis .sphere 10 135 2)) ((I.realization.basis .sphere 12 136 3) + (I.realization.basis .sphere 12 136 4)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
    exact List.mem_of_getElem? (i := 254) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h255 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    ((I.realization.basis .sphere 10 135 4)) ((I.realization.basis .sphere 12 136 4)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
    exact List.mem_of_getElem? (i := 255) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h174 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 3 (6,132) (I.realization.basis .sphere 6 132 0) := by
  classical
  have hh := I.results ⟨.sphere,.reaches,3,6,132,[0],6,132,[],"S0_AdamsE2_ss",2574⟩ (by
    exact List.mem_of_getElem? (i := 174) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem candidates_raw_h224 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (9,134) (I.realization.basis .sphere 9 134 2) := by
  classical
  have hh := I.results ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
    exact List.mem_of_getElem? (i := 224) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem candidates_raw_h225 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 7 (9,134) (I.realization.basis .sphere 9 134 3) := by
  classical
  have hh := I.results ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
    exact List.mem_of_getElem? (i := 225) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [3]=true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem candidates_raw (I : Inputs D L G) :
    HasNonzeroDifferential (sequence D .sphere) 3 (6,132) (9,134)
      (I.realization.basis .sphere 6 132 0) (I.realization.basis .sphere 9 134 3) ∨
    HasNonzeroDifferential (sequence D .sphere) 3 (6,132) (9,134)
      (I.realization.basis .sphere 6 132 0) (I.realization.basis .sphere 9 134 3 + I.realization.basis .sphere 9 134 2) := by
  classical
  let E := sequence D .sphere
  have h226 : HasDifferential E 3 (9,134) (12,136)
      ((I.realization.basis .sphere 9 134 1)) ((I.realization.basis .sphere 12 136 0)) := candidates_raw_h226 I
  have h227 : HasDifferential E 2 (9,134) (11,135)
      ((I.realization.basis .sphere 9 134 0)) ((I.realization.basis .sphere 11 135 3) + (I.realization.basis .sphere 11 135 4)) := candidates_raw_h227 I
  have h228 : HasDifferential E 2 (9,134) (11,135)
      ((I.realization.basis .sphere 9 134 4)) ((I.realization.basis .sphere 11 135 4)) := candidates_raw_h228 I
  have h251 : HasDifferential E 2 (8,134) (10,135)
      ((I.realization.basis .sphere 8 134 1)) ((I.realization.basis .sphere 10 135 3)) := candidates_raw_h251 I
  have h252 : HasDifferential E 3 (10,135) (13,137)
      ((I.realization.basis .sphere 10 135 0)) ((I.realization.basis .sphere 13 137 0)) := candidates_raw_h252 I
  have h253 : HasDifferential E 2 (10,135) (12,136)
      ((I.realization.basis .sphere 10 135 1)) ((I.realization.basis .sphere 12 136 1) + (I.realization.basis .sphere 12 136 2)) := candidates_raw_h253 I
  have h254 : HasDifferential E 2 (10,135) (12,136)
      ((I.realization.basis .sphere 10 135 2)) ((I.realization.basis .sphere 12 136 3) + (I.realization.basis .sphere 12 136 4)) := candidates_raw_h254 I
  have h255 : HasDifferential E 2 (10,135) (12,136)
      ((I.realization.basis .sphere 10 135 4)) ((I.realization.basis .sphere 12 136 4)) := candidates_raw_h255 I
  have h174 : ReachesPage E 3 (6,132) (I.realization.basis .sphere 6 132 0) := candidates_raw_h174 I
  have h224 : ReachesPage E 1000 (9,134) (I.realization.basis .sphere 9 134 2) := candidates_raw_h224 I
  have h225 : ReachesPage E 7 (9,134) (I.realization.basis .sphere 9 134 3) := candidates_raw_h225 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 173) (by rfl))
  change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 134 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 135 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 135 i.val at hg
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 136 i.val at hk
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 9 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 9 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 9 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 9 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 9 134 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 11 135 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 11 135 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 11 135 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 11 135 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 11 135 4 := hf 4
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 10 135 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 10 135 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 10 135 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 10 135 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 10 135 4 := hg 4
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 12 136 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 12 136 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 12 136 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 12 136 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 12 136 4 := hk 4
  have dg0 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h252
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have dg3 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 3)=0 := by
    have hd : E.d 2 (8,134) (I.realization.basis .sphere 8 134 1)=I.realization.basis .sphere 10 135 3 := h251.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(8,134)) ⟨_,hd⟩
  have dg1 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 1)=I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2 := h253.eq_on_page_two.2
  have dg2 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 2)=I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4 := h254.eq_on_page_two.2
  have dg4 : E.d 2 (10,135) (I.realization.basis .sphere 10 135 4)=I.realization.basis .sphere 12 136 4 := h255.eq_on_page_two.2
  have incoming (x : E.Page 2 (10,135)) : k (E.d 2 (10,135) x) 0=0 := by
    have all (a : Fin 5 →₀ F2) : k (E.d 2 (10,135) (g.symm a)) 0=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hc ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change k (E.d 2 (10,135) (g.symm (Finsupp.single i 1))) 0=0
          rw [hg]
          fin_cases i
          all_goals dsimp only
          all_goals simp only [dg0,dg1,dg2,dg3,dg4,map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hk0,←hk1,←hk2,←hk3,←hk4,LinearEquiv.apply_symm_apply]
          all_goals norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using all (g x)
  obtain ⟨_,b1,t,hb1,ht,hd1⟩ := h226
  have db1 : E.d 3 (9,134) b1=t := hd1
  have tn : t≠0 := by
    intro ht0
    obtain ⟨_,z,hz,hzt⟩ := ht
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (10,135) z).mp (hzt.trans ht0)
    change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫ (E.ssData (12,136)).pageπ 0) z ∈ LinearMap.range (E.d 2 (10,135)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫ (E.ssData (12,136)).pageπ 0) z = I.realization.basis .sphere 12 136 0 at hz
    rw [hz] at hh
    obtain ⟨u,hu⟩ := hh
    have hh := incoming u
    rw [hu,←hk0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  obtain ⟨b2late,hb2late⟩ := h224
  obtain ⟨b3late,hb3late⟩ := h225
  obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000) hb2late
  obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤7) hb3late
  have db2 : E.d 3 (9,134) b2=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) hb2 ⟨b2late,hb2late⟩
  have db3 : E.d 3 (9,134) b3=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) hb3 ⟨b3late,hb3late⟩
  have hrep2 {p : ℤ × ℤ} {r : ℤ} {x : E.Page 2 p} {a : E.Page r p} (hr : 2≤r) (ha : RepresentsOnPage E r p x a) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have d1 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 1)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb1) ⟨b1,hb1⟩
  have d2 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb2) ⟨b2,hb2⟩
  have d3 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 3)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb3) ⟨b3,hb3⟩
  have d0 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 0)=I.realization.basis .sphere 11 135 3+I.realization.basis .sphere 11 135 4 := h227.eq_on_page_two.2
  have d4 : E.d 2 (9,134) (I.realization.basis .sphere 9 134 4)=I.realization.basis .sphere 11 135 4 := h228.eq_on_page_two.2
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  have f2_expand {N : ℕ} (f : Fin N →₀ F2) :
      f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
    exact FinitePageCalculus.f2_expand f
  have frame (y : E.Page 3 (9,134)) (hy : E.d 3 (9,134) y=0) : y=0 ∨ y=b2 ∨ y=b3 ∨ y=b3+b2 := by
    let A := E.ssData (9,134)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance y
    let x : E.Page 2 (9,134) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
    have hx : RepresentsOnPage E 3 (9,134) x y := ⟨by decide,z,rfl,hz⟩
    have dx : E.d 2 (9,134) x=0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hx) ⟨y,hx⟩
    let c : Fin 5 → F2 := e x
    have hcoef := congrArg e.symm (f2_expand (e x))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
    have hd := congrArg (E.d 2 (9,134)) hcoef
    rw [dx] at hd
    simp only [map_add,apply_ite,map_zero] at hd
    simp only [d0,d1,d2,d3,d4,ite_self,zero_add,add_zero] at hd
    have c0 : c 0=0 := by
      by_contra h0
      simp only [h0,ite_false] at hd
      by_cases h4 : c 4=0
      all_goals simp only [h4,ite_true,ite_false] at hd
      all_goals have hh := congrArg (fun z => f z 3) hd
      all_goals simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hf3,←hf4,LinearEquiv.apply_symm_apply] at hh
      all_goals norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    have c4 : c 4=0 := by
      by_contra h4
      simp only [c0,h4,ite_true,ite_false,zero_add] at hd
      have hh := congrArg (fun z => f z 4) hd
      simp only [map_zero,Finsupp.zero_apply,←hf4,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply] at hh
    have hform : y=(if c 1=0 then 0 else b1)+((if c 2=0 then 0 else b2)+(if c 3=0 then 0 else b3)) := by
      apply represents_unique hx
      rw [hcoef]
      simp only [c0,c4,ite_true,zero_add,add_zero]
      exact hadd (hif (c 1) hb1) (hadd (hif (c 2) hb2) (hif (c 3) hb3))
    have c1 : c 1=0 := by
      by_contra h1
      have hh := congrArg (E.d 3 (9,134)) hform
      simp only [hy,map_add,apply_ite,map_zero,db1,db2,db3,h1,ite_false,ite_self,zero_add,add_zero] at hh
      exact tn hh.symm
    simp only [c1,ite_true,zero_add] at hform
    by_cases h2 : c 2=0 <;> by_cases h3 : c 3=0
    · exact Or.inl (by simpa only [h2,h3,ite_true,zero_add] using hform)
    · exact Or.inr (Or.inr (Or.inl (by simpa only [h2,h3,ite_true,ite_false,zero_add] using hform)))
    · exact Or.inr (Or.inl (by simpa only [h2,h3,ite_true,ite_false,add_zero] using hform))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [h2,h3,ite_false,add_comm] using hform)))
  have n659 : ¬ HasDifferential E 3 (6,132) (9,134) (I.realization.basis .sphere 6 132 0) (0) := by
    have hh := I.results ⟨.sphere,.refutation,3,6,132,[0],9,134,[],"proofs.db/log",2047477⟩ (by
      exact List.mem_of_getElem? (i := 659) (by rfl))
    dsimp only [Statement] at hh
    obtain ⟨x,hx,y,hy,hh⟩ := hh
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 9 134 []=true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hh
    exact hh
  have n660 : ¬ HasDifferential E 3 (6,132) (9,134) (I.realization.basis .sphere 6 132 0) (I.realization.basis .sphere 9 134 2) := by
    have hh := I.results ⟨.sphere,.refutation,3,6,132,[0],9,134,[2],"proofs.db/log",2047478⟩ (by
      exact List.mem_of_getElem? (i := 660) (by rfl))
    dsimp only [Statement] at hh
    obtain ⟨x,hx,y,hy,hh⟩ := hh
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hh
    exact hh
  obtain ⟨xr,hxr⟩ := h174
  let yr : E.Page 3 (9,134) := E.d 3 (6,132) xr
  have hd : E.d 3 (6,132) xr=yr := rfl
  have hyn : yr≠0 := by
    intro hz
    apply n659
    refine ⟨rfl,xr,0,hxr,RepresentsOnPage.zero (by decide),?_⟩
    change E.d 3 (6,132) xr=0
    exact hd.trans hz
  have hdy : E.d 3 (9,134) yr=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(6,132)) ⟨xr,hd⟩
  rcases frame yr hdy with h|h|h|h
  · exact (hyn h).elim
  · apply (n660 ?_).elim
    refine ⟨rfl,xr,yr,hxr,?_,?_⟩
    · rw [h]; exact hb2
    · exact hd
  · left
    refine ⟨rfl,xr,yr,hxr,?_,hd,hyn⟩
    rw [h]; exact hb3
  · right
    refine ⟨rfl,xr,yr,hxr,?_,hd,hyn⟩
    rw [h]; exact hadd hb3 hb2


private theorem source_label (I : Inputs D L G) :
    I.realization.sphere 6 132 (atom .x_126_6) = I.realization.basis .sphere 6 132 0 := by
  classical
  have hc := I.csv (⟨.sphere,6,132,["368,1", "0,4,69,2"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 138) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0:Fin 2)
  have heq : (atom .x_126_6)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨368,by decide⟩ = projection (monomialOfString "368,1")
    have hs : "368,1" ≠ "" := by decide
    have hp : (("368,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [368, 1] := by
      have split : "368,1".splitOn "," = ["368", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem candidate_label (I : Inputs D L G) :
    I.realization.sphere 9 134 (d3Candidate) = I.realization.basis .sphere 9 134 3 := by
  classical
  have hc := I.csv (⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 173) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (3:Fin 5)
  have heq : (d3Candidate)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨18,by decide⟩ * generator ⟨190,by decide⟩ = projection (monomialOfString "18,1,190,1")
    have hs : "18,1,190,1" ≠ "" := by decide
    have hp : (("18,1,190,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [18, 1, 190, 1] := by
      have split : "18,1,190,1".splitOn "," = ["18", "1", "190", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem h6b_label (I : Inputs D L G) :
    I.realization.sphere 9 134 (mulAt dataH6 B) = I.realization.basis .sphere 9 134 2 := by
  classical
  have hc := I.csv (⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 173) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (2:Fin 5)
  have heq : (mulAt dataH6 B)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨69,by decide⟩ * generator ⟨82,by decide⟩ = projection (monomialOfString "69,1,82,1")
    have hs : "69,1,82,1" ≠ "" := by decide
    have hp : (("69,1,82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69, 1, 82, 1] := by
      have split : "69,1,82,1".splitOn "," = ["69", "1", "82", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he

theorem d3_x_126_6_candidates (I : Inputs D L G) :
    Derived.Differential I.realization 3 (atom .x_126_6) d3Candidate ∨
      Derived.Differential I.realization 3 (atom .x_126_6) d3OtherCandidate := by
  classical

  have other : I.realization.sphere 9 134 d3OtherCandidate =
      I.realization.basis .sphere 9 134 3 + I.realization.basis .sphere 9 134 2 := by
    change I.realization.sphere 9 134 (d3Candidate + mulAt dataH6 B) = _
    rw [map_add,candidate_label I,h6b_label I]
  unfold Derived.Differential
  rw [source_label I,candidate_label I,other]
  exact candidates_raw I
end

section
open CategoryTheory.Limits KIP126.Core.Algebra KIP126.Computation.Near126 in
/-- The six d4 root refutations, d4([1])=[3], and the reconstructed E4
source/target groups yield precisely this E5 component.  Nonzero is on E5. -/
private theorem high_incoming2_zero_h415 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (19,146) (23,149)
    ((I.realization.basis .sphere 19 146 0)) ((I.realization.basis .sphere 23 149 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,19,146,[0],23,149,[0],"S0_AdamsE2_ss",3636⟩ (by
    exact List.mem_of_getElem? (i := 415) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (19,146) (23,149) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 19 146 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 23 149 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_incoming2_zero_h425 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (20,147) (23,149)
    ((I.realization.basis .sphere 20 147 2)) ((I.realization.basis .sphere 23 149 1)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,20,147,[2],23,149,[1],"S0_AdamsE2_ss",3753⟩ (by
    exact List.mem_of_getElem? (i := 425) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (20,147) (23,149) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 20 147 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 23 149 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_incoming2_zero (I : Inputs D L G) :
    (sequence D .sphere).d 2 (23,149) = 0 := by
  classical
  let E := sequence D .sphere
  have h415 : HasDifferential E 4 (19,146) (23,149)
      ((I.realization.basis .sphere 19 146 0)) ((I.realization.basis .sphere 23 149 0)) := high_incoming2_zero_h415 I
  have h425 : HasDifferential E 3 (20,147) (23,149)
      ((I.realization.basis .sphere 20 147 2)) ((I.realization.basis .sphere 23 149 1)) := high_incoming2_zero_h425 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,23,149,["549,1", "0,5,500,1"]⟩ (by
    exact List.mem_of_getElem? (i := 272) (by rfl))
  change E.Page 2 (23,149) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 23 149 i.val at he
  have d0 : E.d 2 (23,149) (I.realization.basis .sphere 23 149 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h415
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hy
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hy⟩
  have d1 : E.d 2 (23,149) (I.realization.basis .sphere 23 149 1) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h425
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hy
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hy⟩
  have hall (a : Fin 2 →₀ F2) : E.d 2 (23,149) (e.symm a)=0 := by
    induction a using Finsupp.induction with
    | zero => simp
    | @single_add i c a hi hc ih =>
      rw [map_add,map_add,ih,add_zero]
      fin_cases c
      · simp
      · change E.d 2 (23,149) (e.symm (Finsupp.single i 1))=0
        rw [he i]
        fin_cases i
        · exact d0
        · exact d1
  ext x
  change E.d 2 (23,149) x=0
  simpa only [LinearEquiv.symm_apply_apply] using hall (e x)


private theorem high_incoming3_zero_h440 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (19,146) (22,148)
    ((I.realization.basis .sphere 19 146 4)) ((I.realization.basis .sphere 22 148 1)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,19,146,[4],22,148,[1],"S0_AdamsE2_ss",3814⟩ (by
    exact List.mem_of_getElem? (i := 440) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (19,146) (22,148) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 19 146 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 22 148 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_incoming3_zero_h441 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (19,146) (22,148)
    ((I.realization.basis .sphere 19 146 1) + (I.realization.basis .sphere 19 146 4)) ((I.realization.basis .sphere 22 148 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,19,146,[1, 4],22,148,[0],"S0_AdamsE2_ss",3815⟩ (by
    exact List.mem_of_getElem? (i := 441) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (19,146) (22,148) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 19 146 [1, 4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 22 148 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_incoming3_zero (I : Inputs D L G) :
    (sequence D .sphere).d 3 (22,148) = 0 := by
  classical
  let E := sequence D .sphere
  have h440 : HasDifferential E 3 (19,146) (22,148)
      ((I.realization.basis .sphere 19 146 4)) ((I.realization.basis .sphere 22 148 1)) := high_incoming3_zero_h440 I
  have h441 : HasDifferential E 3 (19,146) (22,148)
      ((I.realization.basis .sphere 19 146 1) + (I.realization.basis .sphere 19 146 4)) ((I.realization.basis .sphere 22 148 0)) := high_incoming3_zero_h441 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,22,148,["0,1,530,1", "0,4,500,1"]⟩ (by
    exact List.mem_of_getElem? (i := 267) (by rfl))
  change E.Page 2 (22,148) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 22 148 i.val at he
  obtain ⟨_,x0,y0,hx0,hy0,hd0⟩ := h441
  obtain ⟨_,x1,y1,hx1,hy1,hd1⟩ := h440
  have dy0 : E.d 3 (22,148) y0=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(19,146)) ⟨x0,hd0⟩
  have dy1 : E.d 3 (22,148) y1=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(19,146)) ⟨x1,hd1⟩
  ext z
  change E.d 3 (22,148) z=0
  let vv : Fin 2 → E.Page 3 (22,148) := ![y0,y1]
  have hv (i : Fin 2) : RepresentsOnPage E 3 (22,148) (e.symm (Finsupp.single i 1)) (vv i) := by
    rw [he i]
    fin_cases i
    · exact hy0
    · exact hy1
  obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e vv hv z
  simp only [Fin.sum_univ_succ] at hc
  change z=(if c 0=0 then 0 else y0)+((if c 1=0 then 0 else y1)+0) at hc
  rw [hc]
  by_cases h0 : c 0=0 <;> by_cases h1 : c 1=0
  all_goals simp only [h0,h1,ite_true,ite_false,map_zero,map_add,dy0,dy1,add_zero]


private theorem high_component_raw_h407 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (18,145) (21,147)
    ((I.realization.basis .sphere 18 145 4)) ((I.realization.basis .sphere 21 147 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,18,145,[4],21,147,[2],"S0_AdamsE2_ss",3565⟩ (by
    exact List.mem_of_getElem? (i := 407) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (18,145) (21,147) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 18 145 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 21 147 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_component_raw_h430 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (21,147) (25,150)
    ((I.realization.basis .sphere 21 147 1)) ((I.realization.basis .sphere 25 150 3)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,21,147,[1],25,150,[3],"S0_AdamsE2_ss",3749⟩ (by
    exact List.mem_of_getElem? (i := 430) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (21,147) (25,150) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_component_raw_h464 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (25,150) (27,151)
    ((I.realization.basis .sphere 25 150 1)) ((I.realization.basis .sphere 27 151 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,25,150,[1],27,151,[0],"S0_AdamsE2_ss",3995⟩ (by
    exact List.mem_of_getElem? (i := 464) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (25,150) (27,151) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 25 150 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 27 151 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_component_raw_h431 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 4 (21,147) (I.realization.basis .sphere 21 147 0) := by
  classical
  have hh := I.results ⟨.sphere,.reaches,4,21,147,[0],21,147,[],"S0_AdamsE2_ss",3750⟩ (by
    exact List.mem_of_getElem? (i := 431) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem high_component_raw_h462 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (25,150) (I.realization.basis .sphere 25 150 2) := by
  classical
  have hh := I.results ⟨.sphere,.reaches,1000,25,150,[2],25,150,[],"S0_AdamsE2_ss",3993⟩ (by
    exact List.mem_of_getElem? (i := 462) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 25 150 [2]=true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem high_component_raw_h463 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (25,150) (I.realization.basis .sphere 25 150 0 + I.realization.basis .sphere 25 150 1) := by
  classical
  have hh := I.results ⟨.sphere,.reaches,1000,25,150,[0, 1],25,150,[],"S0_AdamsE2_ss",3994⟩ (by
    exact List.mem_of_getElem? (i := 463) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 25 150 [0, 1]=true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem high_component_raw_zero4
    (I : Inputs D L G) {x : (sequence D .sphere).Page 2 (25,150)} (hx : RepresentsOnPage (sequence D .sphere) 4 (25,150) x 0) : x=0  := by
  classical
  let E := sequence D .sphere
  have hrep2 {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (hr : 2≤r) (ha : RepresentsOnPage E r p x a) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _

  by_contra hn
  obtain ⟨x3,h3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hx
  have n3 : x3≠0 := represents_next_nonzero_of_incoming_zero_at (E:=E) (r:=2) (p:=(25,150))
    (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) (high_incoming2_zero I)
    h3 (hrep2 (by decide) hx) hn
  have n4 : (0 : E.Page 4 (25,150))≠0 := represents_next_nonzero_of_incoming_zero_at (E:=E) (r:=3) (p:=(25,150))
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) (high_incoming3_zero I) hx h3 n3
  exact n4 rfl

private theorem high_component_raw_n661
    (I : Inputs D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (0)  := by
  classical
  let E := sequence D .sphere

  have hh := I.results ⟨.sphere,.refutation,4,21,147,[0],25,150,[],"proofs.db/log",154532⟩ (by
    exact List.mem_of_getElem? (i := 661) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 []=true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_raw_n662
    (I : Inputs D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (I.realization.basis .sphere 25 150 3)  := by
  classical
  let E := sequence D .sphere

  have hh := I.results ⟨.sphere,.refutation,4,21,147,[0],25,150,[3],"proofs.db/log",154533⟩ (by
    exact List.mem_of_getElem? (i := 662) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [3]=true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_raw_n663
    (I : Inputs D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (I.realization.basis .sphere 25 150 2)  := by
  classical
  let E := sequence D .sphere

  have hh := I.results ⟨.sphere,.refutation,4,21,147,[0],25,150,[2],"proofs.db/log",154534⟩ (by
    exact List.mem_of_getElem? (i := 663) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [2]=true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_raw_n664
    (I : Inputs D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (I.realization.basis .sphere 25 150 2 + I.realization.basis .sphere 25 150 3)  := by
  classical
  let E := sequence D .sphere

  have hh := I.results ⟨.sphere,.refutation,4,21,147,[0],25,150,[2, 3],"proofs.db/log",154535⟩ (by
    exact List.mem_of_getElem? (i := 664) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [2, 3]=true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_raw_n665
    (I : Inputs D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (I.realization.basis .sphere 25 150 0 + I.realization.basis .sphere 25 150 1)  := by
  classical
  let E := sequence D .sphere

  have hh := I.results ⟨.sphere,.refutation,4,21,147,[0],25,150,[0, 1],"proofs.db/log",154536⟩ (by
    exact List.mem_of_getElem? (i := 665) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [0, 1]=true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_raw_n666
    (I : Inputs D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (I.realization.basis .sphere 25 150 0 + I.realization.basis .sphere 25 150 1 + I.realization.basis .sphere 25 150 3)  := by
  classical
  let E := sequence D .sphere

  have hh := I.results ⟨.sphere,.refutation,4,21,147,[0],25,150,[0, 1, 3],"proofs.db/log",154537⟩ (by
    exact List.mem_of_getElem? (i := 666) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [0, 1, 3]=true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_page_four (I : Inputs D L G) :
    ∃ e : (sequence D .sphere).Page 2 (25,150) ≃ₗ[ℤ] (Fin 4 →₀ F2),
    ∃ a b c : (sequence D .sphere).Page 4 (25,150),
    ∃ u v : (sequence D .sphere).Page 4 (21,147),
    (∀ i : Fin 4, e.symm (Finsupp.single i 1)=I.realization.basis .sphere 25 150 i.val) ∧
    RepresentsOnPage (sequence D .sphere) 4 (25,150)
      (I.realization.basis .sphere 25 150 0+I.realization.basis .sphere 25 150 1) a ∧
    RepresentsOnPage (sequence D .sphere) 4 (25,150) (I.realization.basis .sphere 25 150 2) b ∧
    RepresentsOnPage (sequence D .sphere) 4 (25,150) (I.realization.basis .sphere 25 150 3) c ∧
    RepresentsOnPage (sequence D .sphere) 4 (21,147) (I.realization.basis .sphere 21 147 0) u ∧
    (∀ z : (sequence D .sphere).Page 4 (25,150),
      z=0 ∨ z=c ∨ z=b ∨ z=b+c ∨ z=a ∨ z=a+c ∨ z=a+b ∨ z=a+b+c) ∧
    (sequence D .sphere).d 4 (21,147) v=c ∧
    (∀ z : (sequence D .sphere).Page 4 (21,147), z=0 ∨ z=u ∨ z=v ∨ z=u+v) ∧
    ((sequence D .sphere).d 4 (21,147) u=a+b ∨
      (sequence D .sphere).d 4 (21,147) u=a+b+c) := by
  classical
  let E := sequence D .sphere
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    as_aux_lemma =>
      exact represents_add_tail (by assumption) (by assumption)
  have hrep2 {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (hr : 2≤r) (ha : RepresentsOnPage E r p x a) : RepresentsOnPage E 2 p x x := by
    as_aux_lemma =>
      exact represents_two_self _
  have h407 : HasDifferential E 3 (18,145) (21,147)
      ((I.realization.basis .sphere 18 145 4)) ((I.realization.basis .sphere 21 147 2)) := high_component_raw_h407 I
  have h430 : HasDifferential E 4 (21,147) (25,150)
      ((I.realization.basis .sphere 21 147 1)) ((I.realization.basis .sphere 25 150 3)) := high_component_raw_h430 I
  have h464 : HasDifferential E 2 (25,150) (27,151)
      ((I.realization.basis .sphere 25 150 1)) ((I.realization.basis .sphere 27 151 0)) := high_component_raw_h464 I
  have h431 : ReachesPage E 4 (21,147) (I.realization.basis .sphere 21 147 0) := high_component_raw_h431 I
  have h462 : ReachesPage E 1000 (25,150) (I.realization.basis .sphere 25 150 2) := high_component_raw_h462 I
  have h463 : ReachesPage E 1000 (25,150) (I.realization.basis .sphere 25 150 0 + I.realization.basis .sphere 25 150 1) := high_component_raw_h463 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,25,150,["559,1", "558,1", "13,4,51,1", "8,2,9,1,13,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 281) (by rfl))
  change E.Page 2 (25,150) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 25 150 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,27,151,["0,1,557,1", "0,2,17,1,260,1"]⟩ (by
    exact List.mem_of_getElem? (i := 289) (by rfl))
  change E.Page 2 (27,151) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 27 151 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,21,147,["530,1", "1,1,510,1", "0,3,500,1"]⟩ (by
    exact List.mem_of_getElem? (i := 262) (by rfl))
  change E.Page 2 (21,147) ≃ₗ[ℤ] (Fin 3 →₀ F2) at g
  change ∀ i : Fin 3, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 21 147 i.val at hg
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.realization.basis .sphere 25 150 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.realization.basis .sphere 25 150 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.realization.basis .sphere 25 150 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.realization.basis .sphere 25 150 3 := he 3
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 27 151 0 := hf 0
  obtain ⟨aLate,haLate⟩ := h463
  obtain ⟨bLate,hbLate⟩ := h462
  obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) haLate
  obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) hbLate
  obtain ⟨_,v,c,hv,hc,dvc⟩ := h430
  have dvc' : E.d 4 (21,147) v=c := dvc
  obtain ⟨u,hu⟩ := h431
  have hg2zero : RepresentsOnPage E 4 (21,147) (I.realization.basis .sphere 21 147 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h407
  have sourceFrame (z : E.Page 4 (21,147)) : z=0 ∨ z=u ∨ z=v ∨ z=u+v := by
    as_aux_lemma =>
      let vv : Fin 3 → E.Page 4 (21,147) := ![u,v,0]
      have hh (i : Fin 3) : RepresentsOnPage E 4 (21,147) (g.symm (Finsupp.single i 1)) (vv i) := by
        as_aux_lemma =>
          rw [hg i]
          fin_cases i
          · exact hu
          · exact hv
          · exact hg2zero
      obtain ⟨cs,hcs⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤4) g vv hh z
      simp only [Fin.sum_univ_succ] at hcs
      change z=(if cs 0=0 then 0 else u)+((if cs 1=0 then 0 else v)+((if cs 2=0 then 0 else 0)+0)) at hcs
      simp only [ite_self,add_zero] at hcs
      by_cases h0 : cs 0=0 <;> by_cases h1 : cs 1=0
      · exact Or.inl (by simpa only [h0,h1,ite_true,zero_add] using hcs)
      · exact Or.inr (Or.inr (Or.inl (by simpa only [h0,h1,ite_true,ite_false,zero_add] using hcs)))
      · exact Or.inr (Or.inl (by simpa only [h0,h1,ite_true,ite_false,add_zero] using hcs))
      · exact Or.inr (Or.inr (Or.inr (by simpa only [h0,h1,ite_false] using hcs)))
  have d1 : E.d 2 (25,150) (I.realization.basis .sphere 25 150 1)=I.realization.basis .sphere 27 151 0 := h464.eq_on_page_two.2
  have da : E.d 2 (25,150) (I.realization.basis .sphere 25 150 0+I.realization.basis .sphere 25 150 1)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 (by decide) ha) ⟨a,ha⟩
  have d0 : E.d 2 (25,150) (I.realization.basis .sphere 25 150 0)=I.realization.basis .sphere 27 151 0 := by
    as_aux_lemma =>
      have hh := da
      rw [map_add,d1] at hh
      have ff : I.realization.basis .sphere 27 151 0+I.realization.basis .sphere 27 151 0=0 := by
        as_aux_lemma =>
          rw [←hf0,←map_add f.symm]
          have zz : Finsupp.single (0:Fin 2) (1:F2)+Finsupp.single 0 1=0 := by
            as_aux_lemma =>
              ext i
              simp only [Finsupp.add_apply,Finsupp.zero_apply]
              exact CharTwo.add_self_eq_zero _
          rw [zz,map_zero]
      exact add_right_cancel (hh.trans ff.symm)
  have d2 : E.d 2 (25,150) (I.realization.basis .sphere 25 150 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 (by decide) hb) ⟨b,hb⟩
  have d3 : E.d 2 (25,150) (I.realization.basis .sphere 25 150 3)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 (by decide) hc) ⟨c,hc⟩
  have targetFrame (z : E.Page 4 (25,150)) :
      z=0 ∨ z=c ∨ z=b ∨ z=b+c ∨ z=a ∨ z=a+c ∨ z=a+b ∨ z=a+b+c := by
    as_aux_lemma =>
      apply fourth_frame_of_four_basis_at (E := E) (p := (25,150)) (q := (27,151)) (by rfl) (by change (2:ℤ)≤2; omega) e f a b c
      · simpa only [he0,he1] using ha
      · simpa only [he2] using hb
      · simpa only [he3] using hc
      · change E.d 2 (25,150) (e.symm (Finsupp.single 0 1))=f.symm (Finsupp.single 0 1)
        rw [he0]
        exact d0.trans hf0.symm
      · change E.d 2 (25,150) (e.symm (Finsupp.single 1 1))=f.symm (Finsupp.single 0 1)
        rw [he1]
        exact d1.trans hf0.symm
      · simpa only [he2] using d2
      · simpa only [he3] using d3
  have n661 : ¬ HasDifferential E 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (0)  := high_component_raw_n661 I
  have n662 : ¬ HasDifferential E 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (I.realization.basis .sphere 25 150 3)  := high_component_raw_n662 I
  have n663 : ¬ HasDifferential E 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (I.realization.basis .sphere 25 150 2)  := high_component_raw_n663 I
  have n664 : ¬ HasDifferential E 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (I.realization.basis .sphere 25 150 2 + I.realization.basis .sphere 25 150 3)  := high_component_raw_n664 I
  have n665 : ¬ HasDifferential E 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (I.realization.basis .sphere 25 150 0 + I.realization.basis .sphere 25 150 1)  := high_component_raw_n665 I
  have n666 : ¬ HasDifferential E 4 (21,147) (25,150) (I.realization.basis .sphere 21 147 0) (I.realization.basis .sphere 25 150 0 + I.realization.basis .sphere 25 150 1 + I.realization.basis .sphere 25 150 3)  := high_component_raw_n666 I
  have hdu : E.d 4 (21,147) u=a+b ∨ E.d 4 (21,147) u=a+b+c := by
    as_aux_lemma =>
      rcases targetFrame (E.d 4 (21,147) u) with hh|hh|hh|hh|hh|hh|hh|hh
      · apply (n661 ?_).elim
        exact ⟨rfl,u,_,hu,(RepresentsOnPage.zero (by decide)),hh⟩
      · apply (n662 ?_).elim
        exact ⟨rfl,u,_,hu,(hc),hh⟩
      · apply (n663 ?_).elim
        exact ⟨rfl,u,_,hu,(hb),hh⟩
      · apply (n664 ?_).elim
        exact ⟨rfl,u,_,hu,(hadd hb hc),hh⟩
      · apply (n665 ?_).elim
        exact ⟨rfl,u,_,hu,(ha),hh⟩
      · apply (n666 ?_).elim
        exact ⟨rfl,u,_,hu,(hadd ha hc),hh⟩
      · exact Or.inl hh
      · exact Or.inr hh
  exact ⟨e,a,b,c,u,v,he,ha,hb,hc,hu,targetFrame,dvc',sourceFrame,hdu⟩

private theorem high_component_raw (I : Inputs D L G) :
  ∃ y : (sequence D .sphere).Page 5 (25,150),
    RepresentsOnPage (sequence D .sphere) 5 (25,150)
      (I.realization.basis .sphere 25 150 2) y ∧ y≠0 ∧
    ∀ z : (sequence D .sphere).Page 5 (25,150), z=0 ∨ z=y := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,a,b,c,u,v,he,ha,hb,hc,hu,targetFrame,dvc',sourceFrame,hdu⟩ := high_component_page_four I
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1)=I.realization.basis .sphere 25 150 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1)=I.realization.basis .sphere 25 150 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1)=I.realization.basis .sphere 25 150 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1)=I.realization.basis .sphere 25 150 3 := he 3
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := represents_add_tail hx hy
  have zero4 {x : E.Page 2 (25,150)} (hx : RepresentsOnPage E 4 (25,150) x 0) : x=0 :=
    high_component_raw_zero4 I hx
  have inj4 {x y : E.Page 2 (25,150)} {a b : E.Page 4 (25,150)}
      (hx : RepresentsOnPage E 4 (25,150) x a) (hy : RepresentsOnPage E 4 (25,150) y b)
      (hab : a=b) : x=y := by
    as_aux_lemma =>
      apply sub_eq_zero.mp
      apply zero4
      simpa only [hab,sub_self] using represents_sub_tail hx hy
  obtain ⟨aLate,haLate⟩ := high_component_raw_h463 I
  obtain ⟨bLate,hbLate⟩ := high_component_raw_h462 I
  have hc0 : RepresentsOnPage E 5 (25,150) (I.realization.basis .sphere 25 150 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4;omega)
      (by decide : (4:ℤ)<5) (high_component_raw_h430 I)
  obtain ⟨a5,ha5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤1000) haLate
  obtain ⟨b5,hb5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤1000) hbLate
  have bb2 : I.realization.basis .sphere 25 150 2+I.realization.basis .sphere 25 150 2=0 := by
    as_aux_lemma =>
      rw [←he2,←map_add e.symm]
      have zz : Finsupp.single (2:Fin 4) (1:F2)+Finsupp.single 2 1=0 := by
        as_aux_lemma =>
          ext i
          simp only [Finsupp.add_apply,Finsupp.zero_apply]
          exact CharTwo.add_self_eq_zero _
      rw [zz,map_zero]
  have bb5 : b5+b5=0 := by
    as_aux_lemma =>
      apply represents_unique (hadd hb5 hb5)
      rw [bb2]
      exact RepresentsOnPage.zero (by decide)
  have eqab : a5=b5 := by
    as_aux_lemma =>
      have hh : a5+b5=0 := by
        as_aux_lemma =>
          rcases hdu with hh|hh
          · have hd : HasDifferential E 4 (21,147) (25,150)
                (I.realization.basis .sphere 21 147 0)
                (I.realization.basis .sphere 25 150 0+I.realization.basis .sphere 25 150 1+I.realization.basis .sphere 25 150 2) :=
              ⟨rfl,u,a+b,hu,hadd ha hb,hh⟩
            exact represents_unique (hadd ha5 hb5)
              (differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) hd)
          · have hd : HasDifferential E 4 (21,147) (25,150)
                (I.realization.basis .sphere 21 147 0)
                (I.realization.basis .sphere 25 150 0+I.realization.basis .sphere 25 150 1+I.realization.basis .sphere 25 150 2+I.realization.basis .sphere 25 150 3) :=
              ⟨rfl,u,a+b+c,hu,hadd (hadd ha hb) hc,hh⟩
            have heq := represents_unique (hadd (hadd ha5 hb5) hc0)
              (differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) hd)
            simpa only [add_zero] using heq
      exact add_right_cancel (hh.trans bb5.symm)
  have bn5 : b5≠0 := by
    as_aux_lemma =>
      apply represents_next_nonzero_of_not_incoming_at
        (r := 4) (p := (25,150)) (q := (21,147)) (by rfl)
        (by change (2:ℤ)≤4; omega) (by decide : (2:ℤ)≤4) hb5 hb
      intro q hq
      change E.d 4 (21,147) q=b at hq
      rcases sourceFrame q with hqf|hqf|hqf|hqf
      · rw [hqf,map_zero] at hq
        have heq := inj4 hb (RepresentsOnPage.zero (by decide)) hq.symm
        have hco := congrArg (fun z => e z 2) heq
        rw [←he2,LinearEquiv.apply_symm_apply,map_zero] at hco
        norm_num [Finsupp.single_apply] at hco
      · rw [hqf] at hq
        rcases hdu with hdu|hdu
        · have heq := inj4 (hadd ha hb) hb (hdu.symm.trans hq)
          have hco := congrArg (fun z => e z 0) heq
          simp only [map_add,←he0,←he1,←he2,LinearEquiv.apply_symm_apply,Finsupp.add_apply] at hco
          norm_num [Finsupp.single_apply,Fin.ext_iff] at hco
        · have heq := inj4 (hadd (hadd ha hb) hc) hb (hdu.symm.trans hq)
          have hco := congrArg (fun z => e z 0) heq
          simp only [map_add,←he0,←he1,←he2,←he3,LinearEquiv.apply_symm_apply,Finsupp.add_apply] at hco
          norm_num [Finsupp.single_apply,Fin.ext_iff] at hco
      · rw [hqf,dvc'] at hq
        have heq := inj4 hc hb hq
        have hco := congrArg (fun z => e z 2) heq
        simp only [←he2,←he3,LinearEquiv.apply_symm_apply] at hco
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hco
      · rw [hqf,map_add,dvc'] at hq
        rcases hdu with hdu|hdu
        · rw [hdu] at hq
          have heq := inj4 (hadd (hadd ha hb) hc) hb hq
          have hco := congrArg (fun z => e z 0) heq
          simp only [map_add,←he0,←he1,←he2,←he3,LinearEquiv.apply_symm_apply,Finsupp.add_apply] at hco
          norm_num [Finsupp.single_apply,Fin.ext_iff] at hco
        · rw [hdu] at hq
          have heq := inj4 (hadd (hadd (hadd ha hb) hc) hc) hb hq
          have hco := congrArg (fun z => e z 0) heq
          simp only [map_add,←he0,←he1,←he2,←he3,LinearEquiv.apply_symm_apply,Finsupp.add_apply] at hco
          norm_num [Finsupp.single_apply,Fin.ext_iff] at hco
  refine ⟨b5,hb5,bn5,?_⟩
  intro z
  let A := E.ssData (25,150)
  haveI : Epi (A.pageπ 3) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨q,hq⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 3)).mp inferInstance z
  let x : E.Page 2 (25,150) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) q
  have hx : RepresentsOnPage E 5 (25,150) x z := ⟨by decide,q,rfl,hq⟩
  obtain ⟨z4,hz4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hx
  rcases targetFrame z4 with hh|hh|hh|hh|hh|hh|hh|hh
  · have hx2 := inj4 hz4 (RepresentsOnPage.zero (by decide)) hh
    rw [hx2] at hx
    have hz := represents_unique hx (RepresentsOnPage.zero (by decide))
    left
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hc) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hc0)
    left
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hb) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hb5)
    right
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hadd hb hc) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hadd hb5 hc0)
    right
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (ha) hh
    rw [hx2] at hx
    have hz := represents_unique hx (ha5)
    right
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hadd ha hc) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hadd ha5 hc0)
    right
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hadd ha hb) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hadd ha5 hb5)
    left
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hadd (hadd ha hb) hc) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hadd (hadd ha5 hb5) hc0)
    left
    simpa only [eqab,bb5,add_zero] using hz


private theorem high_basis_label (I : Inputs D L G) :
    I.realization.sphere 25 150 highClass = I.realization.basis .sphere 25 150 2 := by
  classical
  have hc := I.csv (⟨.sphere,25,150,["559,1","558,1","13,4,51,1","8,2,9,1,13,1,80,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 281) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (2:Fin 4)
  have heq : highClass=z := by
    apply Subtype.ext
    rw [hz]
    change ((generator ⟨13,by decide⟩ * generator ⟨13,by decide⟩) *
      (generator ⟨13,by decide⟩ * generator ⟨13,by decide⟩)) * generator ⟨51,by decide⟩ =
        projection (monomialOfString "13,4,51,1")
    have hs : "13,4,51,1" ≠ "" := by decide
    have hp : (("13,4,51,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [13,4,51,1] := by
      have split : "13,4,51,1".splitOn "," = ["13","4","51","1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
  rw [heq]
  exact he

theorem high125_component (I : Inputs D L G) :
    Derived.High125Component I.realization := by
  classical

  unfold Derived.High125Component
  rw [high_basis_label I]
  exact high_component_raw I
end

section

private theorem tail_af26_h469 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (26,151) (28,152)
    (I.realization.basis .sphere 26 151 0) (I.realization.basis .sphere 28 152 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,26,151,[0],28,152,[1],"S0_AdamsE2_ss",4092⟩ (by
    exact List.mem_of_getElem? (i := 469) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (26,151) (28,152) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 26 151 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 28 152 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af26 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (26,151)) := by
  classical
  let E := sequence D .sphere
  have h469 : HasDifferential E 2 (26,151) (28,152)
      (I.realization.basis .sphere 26 151 0) (I.realization.basis .sphere 28 152 1) := tail_af26_h469 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,26,151,["0,1,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 286) (by rfl))
  change E.Page 2 (26,151) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 26 151 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 26 151 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,28,152,["8,3,166,1", "0,3,17,1,260,1"]⟩ (by
    exact List.mem_of_getElem? (i := 294) (by rfl))
  change E.Page 2 (28,152) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 28 152 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 28 152 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 28 152 1 := hf 1
  have hd0 : E.d 2 (26,151) (I.realization.basis .sphere 26 151 0) =
      I.realization.basis .sphere 28 152 1 := h469.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (26,151)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(26,151)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af26 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (26,151)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (26,151))
  exact tail_af26 I

private theorem tail_af27_h480 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (27,152) (29,153)
    (I.realization.basis .sphere 27 152 0) (I.realization.basis .sphere 29 153 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,27,152,[0],29,153,[0],"S0_AdamsE2_ss",4163⟩ (by
    exact List.mem_of_getElem? (i := 480) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (27,152) (29,153) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 27 152 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 29 153 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af27_h479 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (27,152) (29,153)
    (I.realization.basis .sphere 27 152 1) (I.realization.basis .sphere 29 153 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,27,152,[1],29,153,[2],"S0_AdamsE2_ss",4162⟩ (by
    exact List.mem_of_getElem? (i := 479) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (27,152) (29,153) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 27 152 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 29 153 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af27 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (27,152)) := by
  classical
  let E := sequence D .sphere
  have h480 : HasDifferential E 2 (27,152) (29,153)
      (I.realization.basis .sphere 27 152 0) (I.realization.basis .sphere 29 153 0) := tail_af27_h480 I
  have h479 : HasDifferential E 2 (27,152) (29,153)
      (I.realization.basis .sphere 27 152 1) (I.realization.basis .sphere 29 153 2) := tail_af27_h479 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,27,152,["8,3,167,1", "0,2,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 290) (by rfl))
  change E.Page 2 (27,152) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 27 152 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 27 152 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 27 152 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,29,153,["8,3,9,1,13,1,51,1", "8,4,118,1", "0,4,17,1,260,1"]⟩ (by
    exact List.mem_of_getElem? (i := 298) (by rfl))
  change E.Page 2 (29,153) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 29 153 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 29 153 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 29 153 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 29 153 2 := hf 2
  have hd0 : E.d 2 (27,152) (I.realization.basis .sphere 27 152 0) =
      I.realization.basis .sphere 29 153 0 := h480.eq_on_page_two.2
  have hd1 : E.d 2 (27,152) (I.realization.basis .sphere 27 152 1) =
      I.realization.basis .sphere 29 153 2 := h479.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (27,152)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(27,152)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, hd1, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 2) hx
    simp only [map_add, map_zero, ←hf2, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, ←hf2, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af27 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (27,152)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (27,152))
  exact tail_af27 I

private theorem tail_af28_h492 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (28,153) (30,154)
    (I.realization.basis .sphere 28 153 0) (I.realization.basis .sphere 30 154 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,28,153,[0],30,154,[0],"S0_AdamsE2_ss",4266⟩ (by
    exact List.mem_of_getElem? (i := 492) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (28,153) (30,154) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 28 153 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 30 154 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af28_h491 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (28,153) (30,154)
    (I.realization.basis .sphere 28 153 3) (I.realization.basis .sphere 30 154 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,28,153,[3],30,154,[1],"S0_AdamsE2_ss",4265⟩ (by
    exact List.mem_of_getElem? (i := 491) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (28,153) (30,154) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 28 153 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 30 154 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af28_h490 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (26,152) (28,153)
    (I.realization.basis .sphere 26 152 1) (I.realization.basis .sphere 28 153 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,26,152,[1],28,153,[1],"S0_AdamsE2_ss",4264⟩ (by
    exact List.mem_of_getElem? (i := 490) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (26,152) (28,153) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 26 152 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 28 153 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af28_h489 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (26,152) (28,153)
    (I.realization.basis .sphere 26 152 0) (I.realization.basis .sphere 28 153 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,26,152,[0],28,153,[2],"S0_AdamsE2_ss",4263⟩ (by
    exact List.mem_of_getElem? (i := 489) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (26,152) (28,153) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 26 152 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 28 153 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af28 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (28,153)) := by
  classical
  let E := sequence D .sphere
  have h492 : HasDifferential E 2 (28,153) (30,154)
      (I.realization.basis .sphere 28 153 0) (I.realization.basis .sphere 30 154 0) := tail_af28_h492 I
  have h491 : HasDifferential E 2 (28,153) (30,154)
      (I.realization.basis .sphere 28 153 3) (I.realization.basis .sphere 30 154 1) := tail_af28_h491 I
  have h490 : HasDifferential E 2 (26,152) (28,153)
      (I.realization.basis .sphere 26 152 1) (I.realization.basis .sphere 28 153 1) := tail_af28_h490 I
  have h489 : HasDifferential E 2 (26,152) (28,153)
      (I.realization.basis .sphere 26 152 0) (I.realization.basis .sphere 28 153 2) := tail_af28_h489 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,28,153,["64,1,146,1", "8,2,9,1,13,4", "8,3,17,1,80,1", "0,3,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 295) (by rfl))
  change E.Page 2 (28,153) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 28 153 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.realization.basis .sphere 28 153 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.realization.basis .sphere 28 153 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.realization.basis .sphere 28 153 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.realization.basis .sphere 28 153 3 := he 3
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,30,154,["1,2,64,1,137,1", "0,5,17,1,260,1"]⟩ (by
    exact List.mem_of_getElem? (i := 302) (by rfl))
  change E.Page 2 (30,154) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 30 154 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 30 154 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 30 154 1 := hf 1
  have hd0 : E.d 2 (28,153) (I.realization.basis .sphere 28 153 0) =
      I.realization.basis .sphere 30 154 0 := h492.eq_on_page_two.2
  have hd3 : E.d 2 (28,153) (I.realization.basis .sphere 28 153 3) =
      I.realization.basis .sphere 30 154 1 := h491.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 5 (28,153) (I.realization.basis .sphere 28 153 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h490
  have hd1 : E.d 2 (28,153) (I.realization.basis .sphere 28 153 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  have hz2 : RepresentsOnPage E 5 (28,153) (I.realization.basis .sphere 28 153 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h489
  have hd2 : E.d 2 (28,153) (I.realization.basis .sphere 28 153 2) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz2
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz2⟩
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (28,153)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  generalize hc2 : e x 2 = c2 at hxe
  generalize hc3 : e x 3 = c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(28,153)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he3, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he2]
    simpa only [zero_add] using (hz2)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he2, he3, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he3, hd1, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1, he2]
    simpa only [zero_add] using (represents_add_tail (hz1) hz2)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he3, hd0, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, hd0, hd2, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he3, hd0, hd1, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af28 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (28,153)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (28,153))
  exact tail_af28 I

private theorem stem125_af29_four_h498 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (27,153) (29,154)
    (I.realization.basis .sphere 27 153 0) (I.realization.basis .sphere 29 154 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,27,153,[0],29,154,[0],"S0_AdamsE2_ss",4337⟩ (by
    exact List.mem_of_getElem? (i := 498) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (27,153) (29,154) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 27 153 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 29 154 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af29_four_h499 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (29,154) (32,156)
    (I.realization.basis .sphere 29 154 1) (I.realization.basis .sphere 32 156 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,29,154,[1],32,156,[0],"S0_AdamsE2_ss",4338⟩ (by
    exact List.mem_of_getElem? (i := 499) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (29,154) (32,156) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 29 154 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 32 156 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af29_four_h506 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (28,154) (30,155)
    (I.realization.basis .sphere 28 154 0) (I.realization.basis .sphere 30 155 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,28,154,[0],30,155,[1],"S0_AdamsE2_ss",4411⟩ (by
    exact List.mem_of_getElem? (i := 506) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (28,154) (30,155) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 28 154 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 30 155 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af29_four_h507 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (30,155) (32,156)
    (I.realization.basis .sphere 30 155 0) (I.realization.basis .sphere 32 156 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,30,155,[0],32,156,[1],"S0_AdamsE2_ss",4412⟩ (by
    exact List.mem_of_getElem? (i := 507) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (30,155) (32,156) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 30 155 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 32 156 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af29_four (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (29,154)) := by
  classical
  let E := sequence D .sphere
  have h498 : HasDifferential E 2 (27,153) (29,154)
      (I.realization.basis .sphere 27 153 0) (I.realization.basis .sphere 29 154 0) := stem125_af29_four_h498 I
  have h499 : HasDifferential E 3 (29,154) (32,156)
      (I.realization.basis .sphere 29 154 1) (I.realization.basis .sphere 32 156 0) := stem125_af29_four_h499 I
  have h506 : HasDifferential E 2 (28,154) (30,155)
      (I.realization.basis .sphere 28 154 0) (I.realization.basis .sphere 30 155 1) := stem125_af29_four_h506 I
  have h507 : HasDifferential E 2 (30,155) (32,156)
      (I.realization.basis .sphere 30 155 0) (I.realization.basis .sphere 32 156 1) := stem125_af29_four_h507 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,29,154,["0,1,64,1,146,1", "0,4,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 299) (by rfl))
  change E.Page 2 (29,154) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 29 154 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,30,155,["8,2,258,1", "0,5,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 303) (by rfl))
  change E.Page 2 (30,155) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 30 155 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,32,156,["8,2,17,1,147,1", "8,6,13,2"]⟩ (by
    exact List.mem_of_getElem? (i := 310) (by rfl))
  change E.Page 2 (32,156) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 32 156 i.val at hg
  have d20 : E.d 2 (30,155) (I.realization.basis .sphere 30 155 0) =
      I.realization.basis .sphere 32 156 1 := h507.eq_on_page_two.2
  have d21 : E.d 2 (30,155) (I.realization.basis .sphere 30 155 1) = 0 := by
    have hd : E.d 2 (28,154) (I.realization.basis .sphere 28 154 0) =
      I.realization.basis .sphere 30 155 1 := h506.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(28,154)) ⟨_,hd⟩
  have hc (x : E.Page 2 (30,155)) : g (E.d 2 (30,155) x) 0 = 0 := by
    have hall (a : Fin 2 →₀ F2) : g (E.d 2 (30,155) (f.symm a)) 0 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (30,155) (f.symm (Finsupp.single i 1))) 0 = 0
          rw [hf i]
          fin_cases i
          · rw [d20]
            rw [show I.realization.basis .sphere 32 156 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm, LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · rw [d21]
            exact congrArg (fun z : Fin 2 →₀ F2 => z 0) g.map_zero
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h499
  have hd' : E.d 3 (29,154) a = b := hd
  have hbne : b ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (30,155) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (32,156)).Z_anti bot_le) ≫
      (E.ssData (32,156)).pageπ 0) z ∈ LinearMap.range (E.d 2 (30,155)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (32,156)).Z_anti bot_le) ≫
      (E.ssData (32,156)).pageπ 0) z = I.realization.basis .sphere 32 156 0 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := hc u
    rw [hu] at hzero
    rw [show I.realization.basis .sphere 32 156 0 = g.symm (Finsupp.single 0 1) from (hg 0).symm, LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  have hz : RepresentsOnPage E 3 (29,154) (I.realization.basis .sphere 29 154 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h498
  have frame (q : E.Page 3 (29,154)) : q=0 ∨ q=a := by
    let vv : Fin 2 → E.Page 3 (29,154) := ![0,a]
    have hv (i : Fin 2) : RepresentsOnPage E 3 (29,154) (e.symm (Finsupp.single i 1)) (vv i) := by
      rw [he i]
      fin_cases i
      · exact hz
      · exact ha
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e vv hv q
    simp only [Fin.sum_univ_succ] at hc
    change q = (if c 0=0 then 0 else 0) + ((if c 1=0 then 0 else a)+0) at hc
    by_cases h : c 1=0
    · exact Or.inl (by simpa only [h,ite_true,ite_self,add_zero] using hc)
    · exact Or.inr (by simpa only [h,ite_false,ite_self,add_zero,zero_add] using hc)
  have hker (q : E.Page 3 (29,154)) (hq : E.d 3 (29,154) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((29,154)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [hker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (29,154)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem stem125_e5_zero_af29 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (29,154)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (29,154))
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 5 29 154
    (by decide) (by decide) (stem125_af29_four I)

private theorem tail_af30_h507 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (30,155) (32,156)
    (I.realization.basis .sphere 30 155 0) (I.realization.basis .sphere 32 156 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,30,155,[0],32,156,[1],"S0_AdamsE2_ss",4412⟩ (by
    exact List.mem_of_getElem? (i := 507) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (30,155) (32,156) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 30 155 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 32 156 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af30_h506 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (28,154) (30,155)
    (I.realization.basis .sphere 28 154 0) (I.realization.basis .sphere 30 155 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,28,154,[0],30,155,[1],"S0_AdamsE2_ss",4411⟩ (by
    exact List.mem_of_getElem? (i := 506) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (28,154) (30,155) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 28 154 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 30 155 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af30 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (30,155)) := by
  classical
  let E := sequence D .sphere
  have h507 : HasDifferential E 2 (30,155) (32,156)
      (I.realization.basis .sphere 30 155 0) (I.realization.basis .sphere 32 156 1) := tail_af30_h507 I
  have h506 : HasDifferential E 2 (28,154) (30,155)
      (I.realization.basis .sphere 28 154 0) (I.realization.basis .sphere 30 155 1) := tail_af30_h506 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,30,155,["8,2,258,1", "0,5,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 303) (by rfl))
  change E.Page 2 (30,155) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 30 155 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 30 155 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 30 155 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,32,156,["8,2,17,1,147,1", "8,6,13,2"]⟩ (by
    exact List.mem_of_getElem? (i := 310) (by rfl))
  change E.Page 2 (32,156) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 32 156 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 32 156 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 32 156 1 := hf 1
  have hd0 : E.d 2 (30,155) (I.realization.basis .sphere 30 155 0) =
      I.realization.basis .sphere 32 156 1 := h507.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 5 (30,155) (I.realization.basis .sphere 30 155 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h506
  have hd1 : E.d 2 (30,155) (I.realization.basis .sphere 30 155 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (30,155)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(30,155)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af30 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (30,155)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (30,155))
  exact tail_af30 I

private theorem stem125_af31_five_h501 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (29,155) (31,156)
    (I.realization.basis .sphere 29 155 0) (I.realization.basis .sphere 31 156 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,29,155,[0],31,156,[1],"S0_AdamsE2_ss",4414⟩ (by
    exact List.mem_of_getElem? (i := 501) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (29,155) (31,156) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 29 155 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 31 156 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af31_five_h502 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (29,155) (31,156)
    (I.realization.basis .sphere 29 155 1) (I.realization.basis .sphere 31 156 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,29,155,[1],31,156,[2],"S0_AdamsE2_ss",4415⟩ (by
    exact List.mem_of_getElem? (i := 502) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (29,155) (31,156) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 29 155 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 31 156 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af31_five_h514 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (31,156) (35,159)
    (I.realization.basis .sphere 31 156 0) (I.realization.basis .sphere 35 159 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,31,156,[0],35,159,[0],"S0_AdamsE2_ss",4503⟩ (by
    exact List.mem_of_getElem? (i := 514) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (31,156) (35,159) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 31 156 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 35 159 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af31_five_h525 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (33,158) (35,159)
    (I.realization.basis .sphere 33 158 0) (I.realization.basis .sphere 35 159 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,33,158,[0],35,159,[1],"S0_AdamsE2_ss",4671⟩ (by
    exact List.mem_of_getElem? (i := 525) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (33,158) (35,159) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 33 158 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 35 159 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af31_five_hd3zero
    (I : Inputs D L G) : (sequence D .sphere).d 3 (32,157) = 0  := by
  classical
  let E := sequence D .sphere
  have h525 : HasDifferential E 2 (33,158) (35,159)
      (I.realization.basis .sphere 33 158 0) (I.realization.basis .sphere 35 159 1) := stem125_af31_five_h525 I
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,33,158,["8,1,453,1"]⟩ (by
    exact List.mem_of_getElem? (i := 314) (by rfl))
  change E.Page 2 (33,158) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 33 158 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,35,159,["42,1,224,1", "8,7,20,1"]⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  change E.Page 2 (35,159) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 35 159 i.val at hg
  obtain ⟨z,hz⟩ := I.basis ⟨.sphere,32,157,[]⟩ (by
    exact List.mem_of_getElem? (i := 311) (by rfl))
  change E.Page 2 (32,157) ≃ₗ[ℤ] (Fin 0 →₀ F2) at z
  change ∀ i : Fin 0, z.symm (Finsupp.single i 1) = I.realization.basis .sphere 32 157 i.val at hz
  have d20 : E.d 2 (33,158) (I.realization.basis .sphere 33 158 0) =
      I.realization.basis .sphere 35 159 1 := h525.eq_on_page_two.2
  have hc (x : E.Page 2 (33,158)) : g (E.d 2 (33,158) x) 0 = 0 := by
    have hall (a : Fin 1 →₀ F2) : g (E.d 2 (33,158) (f.symm a)) 0 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (33,158) (f.symm (Finsupp.single i 1))) 0 = 0
          rw [hf i]
          fin_cases i
          rw [d20]
          rw [show I.realization.basis .sphere 35 159 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm, LinearEquiv.apply_symm_apply]
          norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)

  have hp (q : E.Page 3 (32,157)) : q = 0 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) z
      (fun i : Fin 0 => i.elim0) (fun i => i.elim0) q
    simpa only [Fin.sum_univ_zero] using hc
  ext q
  simpa only [hp q,map_zero] using (E.d 3 (32,157)).hom.map_zero

private theorem stem125_af31_target_nonzero (I : Inputs D L G)
    {b : (sequence D .sphere).Page 4 (35,159)}
    (hb : RepresentsOnPage (sequence D .sphere) 4 (35,159)
      (I.realization.basis .sphere 35 159 0) b) : b ≠ 0 := by
  classical
  let E := sequence D .sphere
  have h525 : HasDifferential E 2 (33,158) (35,159)
      (I.realization.basis .sphere 33 158 0) (I.realization.basis .sphere 35 159 1) := stem125_af31_five_h525 I
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,33,158,["8,1,453,1"]⟩ (by
    exact List.mem_of_getElem? (i := 314) (by rfl))
  change E.Page 2 (33,158) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 33 158 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,35,159,["42,1,224,1", "8,7,20,1"]⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  change E.Page 2 (35,159) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 35 159 i.val at hg
  obtain ⟨z,hz⟩ := I.basis ⟨.sphere,32,157,[]⟩ (by
    exact List.mem_of_getElem? (i := 311) (by rfl))
  change E.Page 2 (32,157) ≃ₗ[ℤ] (Fin 0 →₀ F2) at z
  change ∀ i : Fin 0, z.symm (Finsupp.single i 1) = I.realization.basis .sphere 32 157 i.val at hz
  have d20 : E.d 2 (33,158) (I.realization.basis .sphere 33 158 0) =
      I.realization.basis .sphere 35 159 1 := h525.eq_on_page_two.2
  have hc (x : E.Page 2 (33,158)) : g (E.d 2 (33,158) x) 0 = 0 := by
    as_aux_lemma =>
      have hall (a : Fin 1 →₀ F2) : g (E.d 2 (33,158) (f.symm a)) 0 = 0 := by
        as_aux_lemma =>
          induction a using Finsupp.induction with
          | zero => simp
          | @single_add i c a hi hci ih =>
            rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
            fin_cases c
            · simp
            · change g (E.d 2 (33,158) (f.symm (Finsupp.single i 1))) 0 = 0
              rw [hf i]
              fin_cases i
              rw [d20]
              rw [show I.realization.basis .sphere 35 159 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm, LinearEquiv.apply_symm_apply]
              norm_num [Finsupp.single_apply,Fin.ext_iff]
      simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  have hd3zero : E.d 3 (32,157) = 0  := stem125_af31_five_hd3zero I
  obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hb
  have hb3ne : b3 ≠ 0 := by
    apply represents_next_nonzero_of_not_incoming_at
      (r := 2) (p := (35,159)) (q := (33,158)) (by rfl)
      (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) hb3 (represents_two_self _)
    intro u hu
    change E.d 2 (33,158) u=I.realization.basis .sphere 35 159 0 at hu
    have hzero := hc u
    rw [hu] at hzero
    rw [show I.realization.basis .sphere 35 159 0 = g.symm (Finsupp.single 0 1) from (hg 0).symm,
      LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  exact represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) hd3zero hb hb3 hb3ne

private theorem stem125_af31_five (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (31,156)) := by
  classical
  let E := sequence D .sphere
  have h501 : HasDifferential E 2 (29,155) (31,156)
      (I.realization.basis .sphere 29 155 0) (I.realization.basis .sphere 31 156 1) := stem125_af31_five_h501 I
  have h502 : HasDifferential E 2 (29,155) (31,156)
      (I.realization.basis .sphere 29 155 1) (I.realization.basis .sphere 31 156 2) := stem125_af31_five_h502 I
  have h514 : HasDifferential E 4 (31,156) (35,159)
      (I.realization.basis .sphere 31 156 0) (I.realization.basis .sphere 35 159 0) := stem125_af31_five_h514 I
  have h525 : HasDifferential E 2 (33,158) (35,159)
      (I.realization.basis .sphere 33 158 0) (I.realization.basis .sphere 35 159 1) := stem125_af31_five_h525 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,31,156,["8,1,17,2,113,1", "8,5,13,1,32,1", "0,6,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 307) (by rfl))
  change E.Page 2 (31,156) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 31 156 i.val at he
  obtain ⟨_,a,b,ha,hb,hd⟩ := h514
  have hd' : E.d 4 (31,156) a = b := hd
  have hbne : b ≠ 0 := stem125_af31_target_nonzero I hb
  have hz1 : RepresentsOnPage E 4 (31,156) (I.realization.basis .sphere 31 156 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h501
  have hz2 : RepresentsOnPage E 4 (31,156) (I.realization.basis .sphere 31 156 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h502
  have frame (q : E.Page 4 (31,156)) : q=0 ∨ q=a := by
    as_aux_lemma =>
      let vv : Fin 3 → E.Page 4 (31,156) := ![a,0,0]
      have hv (i : Fin 3) : RepresentsOnPage E 4 (31,156) (e.symm (Finsupp.single i 1)) (vv i) := by
        as_aux_lemma =>
          rw [he i]
          fin_cases i
          · exact ha
          · exact hz1
          · exact hz2
      obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤4) e vv hv q
      simp only [Fin.sum_univ_succ] at hc
      change q = (if c 0=0 then 0 else a) + ((if c 1=0 then 0 else 0)+((if c 2=0 then 0 else 0)+0)) at hc
      by_cases h : c 0=0
      · exact Or.inl (by simpa only [h,ite_true,ite_self,add_zero] using hc)
      · exact Or.inr (by simpa only [h,ite_false,ite_self,add_zero,zero_add] using hc)
  exact choice_next_zero_of_single_frame_nonzero_differential
    (E := E) (r := 4) (by decide) (by change (2:ℤ)≤4; omega)
    a (fun h => hbne (hd'.symm.trans h)) frame


private theorem stem125_e5_zero_af31 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (31,156)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (31,156))
  exact stem125_af31_five I

private theorem tail_af32 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (32,157)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,32,157,[]⟩ (by
    exact List.mem_of_getElem? (i := 311) (by rfl))
  change E.Page 2 (32,157) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 32 157 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af32 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (32,157)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (32,157))
  exact tail_af32 I

private theorem tail_af33_h525 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (33,158) (35,159)
    (I.realization.basis .sphere 33 158 0) (I.realization.basis .sphere 35 159 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,33,158,[0],35,159,[1],"S0_AdamsE2_ss",4671⟩ (by
    exact List.mem_of_getElem? (i := 525) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (33,158) (35,159) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 33 158 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 35 159 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af33 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (33,158)) := by
  classical
  let E := sequence D .sphere
  have h525 : HasDifferential E 2 (33,158) (35,159)
      (I.realization.basis .sphere 33 158 0) (I.realization.basis .sphere 35 159 1) := tail_af33_h525 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,33,158,["8,1,453,1"]⟩ (by
    exact List.mem_of_getElem? (i := 314) (by rfl))
  change E.Page 2 (33,158) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 33 158 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 33 158 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,35,159,["42,1,224,1", "8,7,20,1"]⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  change E.Page 2 (35,159) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 35 159 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 35 159 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 35 159 1 := hf 1
  have hd0 : E.d 2 (33,158) (I.realization.basis .sphere 33 158 0) =
      I.realization.basis .sphere 35 159 1 := h525.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (33,158)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(33,158)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af33 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (33,158)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (33,158))
  exact tail_af33 I

private theorem tail_af34_h531 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (31,157) (34,159)
    (I.realization.basis .sphere 31 157 0) (I.realization.basis .sphere 34 159 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,31,157,[0],34,159,[0],"S0_AdamsE2_ss",4764⟩ (by
    exact List.mem_of_getElem? (i := 531) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (31,157) (34,159) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 31 157 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 34 159 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af34_h530 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (32,158) (34,159)
    (I.realization.basis .sphere 32 158 0) (I.realization.basis .sphere 34 159 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,32,158,[0],34,159,[1],"S0_AdamsE2_ss",4763⟩ (by
    exact List.mem_of_getElem? (i := 530) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (32,158) (34,159) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 32 158 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 34 159 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af34 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (34,159)) := by
  classical
  let E := sequence D .sphere
  have h531 : HasDifferential E 3 (31,157) (34,159)
      (I.realization.basis .sphere 31 157 0) (I.realization.basis .sphere 34 159 0) := tail_af34_h531 I
  have h530 : HasDifferential E 2 (32,158) (34,159)
      (I.realization.basis .sphere 32 158 0) (I.realization.basis .sphere 34 159 1) := tail_af34_h530 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,34,159,["8,4,137,1", "8,6,45,1"]⟩ (by
    exact List.mem_of_getElem? (i := 318) (by rfl))
  change E.Page 2 (34,159) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 34 159 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 34 159 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 34 159 1 := he 1
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) h531
  · exact differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h530

private theorem stem125_e5_zero_af34 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (34,159)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (34,159))
  exact tail_af34 I

private theorem tail_af35 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (35,160)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,35,160,[]⟩ (by
    exact List.mem_of_getElem? (i := 323) (by rfl))
  change E.Page 2 (35,160) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 35 160 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af35 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (35,160)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (35,160))
  exact tail_af35 I

private theorem tail_af36_h541 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (36,161) (38,162)
    (I.realization.basis .sphere 36 161 0) (I.realization.basis .sphere 38 162 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,36,161,[0],38,162,[1],"S0_AdamsE2_ss",4930⟩ (by
    exact List.mem_of_getElem? (i := 541) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (36,161) (38,162) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 36 161 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 38 162 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af36_h540 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (33,159) (36,161)
    (I.realization.basis .sphere 33 159 0) (I.realization.basis .sphere 36 161 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,33,159,[0],36,161,[1],"S0_AdamsE2_ss",4929⟩ (by
    exact List.mem_of_getElem? (i := 540) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (33,159) (36,161) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 33 159 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 36 161 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af36 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (36,161)) := by
  classical
  let E := sequence D .sphere
  have h541 : HasDifferential E 2 (36,161) (38,162)
      (I.realization.basis .sphere 36 161 0) (I.realization.basis .sphere 38 162 1) := tail_af36_h541 I
  have h540 : HasDifferential E 3 (33,159) (36,161)
      (I.realization.basis .sphere 33 159 0) (I.realization.basis .sphere 36 161 1) := tail_af36_h540 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,36,161,["8,1,488,1", "1,1,42,1,224,1"]⟩ (by
    exact List.mem_of_getElem? (i := 326) (by rfl))
  change E.Page 2 (36,161) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 36 161 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 36 161 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 36 161 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,38,162,["8,2,297,1", "8,4,16,1,17,2"]⟩ (by
    exact List.mem_of_getElem? (i := 334) (by rfl))
  change E.Page 2 (38,162) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 38 162 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 38 162 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 38 162 1 := hf 1
  have hd0 : E.d 2 (36,161) (I.realization.basis .sphere 36 161 0) =
      I.realization.basis .sphere 38 162 1 := h541.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 5 (36,161) (I.realization.basis .sphere 36 161 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) h540
  have hd1 : E.d 2 (36,161) (I.realization.basis .sphere 36 161 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (36,161)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(36,161)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af36 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (36,161)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (36,161))
  exact tail_af36 I

private theorem tail_af37_h547 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (37,162) (39,163)
    (I.realization.basis .sphere 37 162 0) (I.realization.basis .sphere 39 163 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,37,162,[0],39,163,[0],"S0_AdamsE2_ss",5028⟩ (by
    exact List.mem_of_getElem? (i := 547) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (37,162) (39,163) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 37 162 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 39 163 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af37_h546 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (35,161) (37,162)
    (I.realization.basis .sphere 35 161 0) (I.realization.basis .sphere 37 162 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,35,161,[0],37,162,[1],"S0_AdamsE2_ss",5027⟩ (by
    exact List.mem_of_getElem? (i := 546) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (35,161) (37,162) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 35 161 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 37 162 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af37 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (37,162)) := by
  classical
  let E := sequence D .sphere
  have h547 : HasDifferential E 2 (37,162) (39,163)
      (I.realization.basis .sphere 37 162 0) (I.realization.basis .sphere 39 163 0) := tail_af37_h547 I
  have h546 : HasDifferential E 2 (35,161) (37,162)
      (I.realization.basis .sphere 35 161 0) (I.realization.basis .sphere 37 162 1) := tail_af37_h546 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,37,162,["8,2,298,1", "8,5,88,1"]⟩ (by
    exact List.mem_of_getElem? (i := 330) (by rfl))
  change E.Page 2 (37,162) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 37 162 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 37 162 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 37 162 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,39,163,["0,1,8,2,297,1"]⟩ (by
    exact List.mem_of_getElem? (i := 339) (by rfl))
  change E.Page 2 (39,163) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 39 163 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 39 163 0 := hf 0
  have hd0 : E.d 2 (37,162) (I.realization.basis .sphere 37 162 0) =
      I.realization.basis .sphere 39 163 0 := h547.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 5 (37,162) (I.realization.basis .sphere 37 162 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h546
  have hd1 : E.d 2 (37,162) (I.realization.basis .sphere 37 162 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (37,162)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(37,162)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af37 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (37,162)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (37,162))
  exact tail_af37 I

private theorem stem125_e5_zero_26_to_37 (I : Inputs D L G)
    (s : ℕ) (hs : 26 ≤ s) (hs' : s ≤ 37) :
    Subsingleton ((sequence D .sphere).Page 5 (s,(s : ℤ)+125)) := by
  classical

  interval_cases s
  · exact stem125_e5_zero_af26 I
  · exact stem125_e5_zero_af27 I
  · exact stem125_e5_zero_af28 I
  · exact stem125_e5_zero_af29 I
  · exact stem125_e5_zero_af30 I
  · exact stem125_e5_zero_af31 I
  · exact stem125_e5_zero_af32 I
  · exact stem125_e5_zero_af33 I
  · exact stem125_e5_zero_af34 I
  · exact stem125_e5_zero_af35 I
  · exact stem125_e5_zero_af36 I
  · exact stem125_e5_zero_af37 I

private theorem stem125_af38_four_h552 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (38,163) (41,165)
    ((I.realization.basis .sphere 38 163 0)) ((I.realization.basis .sphere 41 165 1) + (I.realization.basis .sphere 41 165 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,38,163,[0],41,165,[1, 2],"S0_AdamsE2_ss",5143⟩ (by
    exact List.mem_of_getElem? (i := 552) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (38,163) (41,165) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 38 163 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 41 165 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af38_four_h557 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (39,164) (43,167)
    ((I.realization.basis .sphere 39 164 0)) ((I.realization.basis .sphere 43 167 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,39,164,[0],43,167,[0],"S0_AdamsE2_ss",5217⟩ (by
    exact List.mem_of_getElem? (i := 557) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (39,164) (43,167) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 39 164 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 43 167 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af38_four_hd2zero
    (I : Inputs D L G) : (sequence D .sphere).d 2 (39,164) = 0  := by
  classical
  let E := sequence D .sphere
  have h557 : HasDifferential E 4 (39,164) (43,167)
      ((I.realization.basis .sphere 39 164 0)) ((I.realization.basis .sphere 43 167 0)) := stem125_af38_four_h557 I
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,39,164,["0,2,8,2,298,1"]⟩ (by
    exact List.mem_of_getElem? (i := 340) (by rfl))
  change E.Page 2 (39,164) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 39 164 i.val at hf
  have d20 : E.d 2 (39,164) (I.realization.basis .sphere 39 164 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h557
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hx
    rw [← hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide : (2:ℤ)<4) hx2 ⟨x,hx⟩

  have hall (a : Fin 1 →₀ F2) : E.d 2 (39,164) (f.symm a) = 0 := by
    induction a using Finsupp.induction with
    | zero => simp
    | @single_add i c a hi hci ih =>
      rw [map_add,map_add,ih,add_zero]
      fin_cases c
      · simp
      · change E.d 2 (39,164) (f.symm (Finsupp.single i 1)) = 0
        rw [hf i]
        fin_cases i
        exact d20
  ext x
  change E.d 2 (39,164) x = 0
  simpa only [LinearEquiv.symm_apply_apply] using hall (f x)

private theorem stem125_af38_four (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (38,163)) := by
  classical
  let E := sequence D .sphere
  have h552 : HasDifferential E 3 (38,163) (41,165)
      ((I.realization.basis .sphere 38 163 0)) ((I.realization.basis .sphere 41 165 1) + (I.realization.basis .sphere 41 165 2)) := stem125_af38_four_h552 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,38,163,["0,1,8,2,298,1"]⟩ (by
    exact List.mem_of_getElem? (i := 335) (by rfl))
  change E.Page 2 (38,163) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 38 163 i.val at he
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,41,165,["16,1,403,1", "8,3,223,1", "0,1,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 347) (by rfl))
  change E.Page 2 (41,165) ≃ₗ[ℤ] (Fin 3 →₀ F2) at g
  change ∀ i : Fin 3, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 41 165 i.val at hg
  have hd2zero : E.d 2 (39,164) = 0  := stem125_af38_four_hd2zero I
  obtain ⟨_,a,b,ha,hb,hd⟩ := h552
  have hd' : E.d 3 (38,163) a = b := hd
  obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hb
  have hb2ne : b2 ≠ 0 := by
    as_aux_lemma =>
      intro hb0
      have hh := hb2.eq_on_page_two
      rw [hb0] at hh
      have ht := congrArg (fun x => g x 1) hh
      rw [map_add,Finsupp.add_apply] at ht
      rw [show I.realization.basis .sphere 41 165 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm,
        show I.realization.basis .sphere 41 165 2 = g.symm (Finsupp.single 2 1) from (hg 2).symm,
        LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at ht
      norm_num [Finsupp.single_apply,Fin.ext_iff] at ht
  have hbne : b ≠ 0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) hd2zero hb hb2 hb2ne
  have frame (q : E.Page 3 (38,163)) : q=0 ∨ q=a := by
    as_aux_lemma =>
      apply generated_one (by decide : (2:ℤ)≤3) e a
      rw [he 0]
      change RepresentsOnPage E 3 (38,163) (I.realization.basis .sphere 38 163 0) a
      exact ha
  exact choice_next_zero_of_single_frame_nonzero_differential
    (E := E) (r := 3) (by decide) (by change (2:ℤ)≤3; omega)
    a (fun h => hbne (hd'.symm.trans h)) frame


private theorem stem125_e5_zero_af38 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (38,163)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (38,163))
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 5 38 163
    (by decide) (by decide) (stem125_af38_four I)

private theorem tail_af40_three_h563 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (40,165) (42,166)
    (I.realization.basis .sphere 40 165 0) (I.realization.basis .sphere 42 166 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,40,165,[0],42,166,[1],"S0_AdamsE2_ss",5327⟩ (by
    exact List.mem_of_getElem? (i := 563) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (40,165) (42,166) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 40 165 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 42 166 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af40_three_h562 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (38,164) (40,165)
    (I.realization.basis .sphere 38 164 0) (I.realization.basis .sphere 40 165 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,38,164,[0],40,165,[1],"S0_AdamsE2_ss",5326⟩ (by
    exact List.mem_of_getElem? (i := 562) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (38,164) (40,165) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 38 164 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 40 165 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af40_three (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 3 (40,165)) := by
  classical
  let E := sequence D .sphere
  have h563 : HasDifferential E 2 (40,165) (42,166)
      (I.realization.basis .sphere 40 165 0) (I.realization.basis .sphere 42 166 1) := tail_af40_three_h563 I
  have h562 : HasDifferential E 2 (38,164) (40,165)
      (I.realization.basis .sphere 38 164 0) (I.realization.basis .sphere 40 165 1) := tail_af40_three_h562 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,40,165,["17,1,403,1", "8,6,55,1"]⟩ (by
    exact List.mem_of_getElem? (i := 343) (by rfl))
  change E.Page 2 (40,165) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 40 165 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 40 165 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 40 165 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,42,166,["0,1,16,1,403,1", "0,2,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 352) (by rfl))
  change E.Page 2 (42,166) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 42 166 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 42 166 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 42 166 1 := hf 1
  have hd0 : E.d 2 (40,165) (I.realization.basis .sphere 40 165 0) =
      I.realization.basis .sphere 42 166 1 := h563.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 3 (40,165) (I.realization.basis .sphere 40 165 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h562
  have hd1 : E.d 2 (40,165) (I.realization.basis .sphere 40 165 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  apply third_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (40,165)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(40,165)) (r:=3) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem tail_af39_h557 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (39,164) (43,167)
    (I.realization.basis .sphere 39 164 0) (I.realization.basis .sphere 43 167 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,39,164,[0],43,167,[0],"S0_AdamsE2_ss",5217⟩ (by
    exact List.mem_of_getElem? (i := 557) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (39,164) (43,167) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 39 164 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 43 167 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af39_h567 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (41,166) (44,168)
    (I.realization.basis .sphere 41 166 0) (I.realization.basis .sphere 44 168 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,41,166,[0],44,168,[0],"S0_AdamsE2_ss",5441⟩ (by
    exact List.mem_of_getElem? (i := 567) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (41,166) (44,168) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 41 166 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 44 168 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af39_h568 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (41,166) (43,167)
    (I.realization.basis .sphere 41 166 1) (I.realization.basis .sphere 43 167 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,41,166,[1],43,167,[1],"S0_AdamsE2_ss",5442⟩ (by
    exact List.mem_of_getElem? (i := 568) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (41,166) (43,167) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 41 166 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 43 167 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af39 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (39,164)) := by
  classical
  let E := sequence D .sphere
  have h557 : HasDifferential E 4 (39,164) (43,167)
      (I.realization.basis .sphere 39 164 0) (I.realization.basis .sphere 43 167 0) := tail_af39_h557 I
  have h567 : HasDifferential E 3 (41,166) (44,168)
      (I.realization.basis .sphere 41 166 0) (I.realization.basis .sphere 44 168 0) := tail_af39_h567 I
  have h568 : HasDifferential E 2 (41,166) (43,167)
      (I.realization.basis .sphere 41 166 1) (I.realization.basis .sphere 43 167 1) := tail_af39_h568 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,39,164,["0,2,8,2,298,1"]⟩ (by
    exact List.mem_of_getElem? (i := 340) (by rfl))
  change E.Page 2 (39,164) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 39 164 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 39 164 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,41,166,["1,1,685,1", "0,1,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 348) (by rfl))
  change E.Page 2 (41,166) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 41 166 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 41 166 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 41 166 1 := hf 1
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,43,167,["0,2,16,1,403,1", "0,3,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 356) (by rfl))
  change E.Page 2 (43,167) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 43 167 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 43 167 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 43 167 1 := hg 1
  have d21 : E.d 2 (41,166) (I.realization.basis .sphere 41 166 1) =
      I.realization.basis .sphere 43 167 1 := h568.eq_on_page_two.2
  have d20 : E.d 2 (41,166) (I.realization.basis .sphere 41 166 0) = 0 := by
    obtain ⟨_,xr,yr,hxr,_,_⟩ := h567
    obtain ⟨z,hz⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hxr
    rw [←hz.eq_on_page_two] at hz
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hz ⟨xr,hxr⟩
  have incoming_zero (x : E.Page 2 (41,166)) : g (E.d 2 (41,166) x) 0 = 0 := by
    have hall (a : Fin 2 →₀ F2) : g (E.d 2 (41,166) (f.symm a)) 0 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (41,166) (f.symm (Finsupp.single i 1))) 0 = 0
          fin_cases i
          · change g (E.d 2 (41,166) (f.symm (Finsupp.single 0 1))) 0 = 0
            simp only [hf0,d20,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (41,166) (f.symm (Finsupp.single 1 1))) 0 = 0
            rw [hf1,d21,←hg1,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h557
  have hd' : E.d 4 (39,164) a = b := hd
  obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hb
  have hb3ne : b3 ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb3
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (41,166) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (43,167)).Z_anti bot_le) ≫
      (E.ssData (43,167)).pageπ 0) z ∈ LinearMap.range (E.d 2 (41,166)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (43,167)).Z_anti bot_le) ≫
      (E.ssData (43,167)).pageπ 0) z = I.realization.basis .sphere 43 167 0 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming_zero u
    rw [hu,←hg0,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  have in3 : E.d 3 ((43,167)-E.diffDeg 3) = 0 := by
    ext x
    change E.d 3 (40,165) x = 0
    rw [(tail_af40_three I).elim x 0,map_zero]
  have hbne : b ≠ 0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤3; omega) (by decide) in3 hb hb3 hb3ne
  have frame (q : E.Page 4 (39,164)) : q=0 ∨ q=a := by
    have hv (i : Fin 1) : RepresentsOnPage E 4 (39,164) (e.symm (Finsupp.single i 1)) a := by
      rw [he i]
      fin_cases i
      exact ha
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤4) e (fun _=>a) hv q
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hc
    by_cases hz : c 0=0
    · exact Or.inl (by simpa only [hz,ite_true] using hc)
    · exact Or.inr (by simpa only [hz,ite_false] using hc)
  have ker (q : E.Page 4 (39,164)) (hq : E.d 4 (39,164) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 4 ((39,164)-E.diffDeg 4)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [ker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 4 (39,164)
    (by change (2:ℤ)≤4; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem stem125_e5_zero_af39 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (39,164)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (39,164))
  exact tail_af39 I

private theorem tail_af40_h563 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (40,165) (42,166)
    (I.realization.basis .sphere 40 165 0) (I.realization.basis .sphere 42 166 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,40,165,[0],42,166,[1],"S0_AdamsE2_ss",5327⟩ (by
    exact List.mem_of_getElem? (i := 563) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (40,165) (42,166) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 40 165 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 42 166 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af40_h562 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (38,164) (40,165)
    (I.realization.basis .sphere 38 164 0) (I.realization.basis .sphere 40 165 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,38,164,[0],40,165,[1],"S0_AdamsE2_ss",5326⟩ (by
    exact List.mem_of_getElem? (i := 562) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (38,164) (40,165) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 38 164 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 40 165 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af40 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (40,165)) := by
  classical
  let E := sequence D .sphere
  have h563 : HasDifferential E 2 (40,165) (42,166)
      (I.realization.basis .sphere 40 165 0) (I.realization.basis .sphere 42 166 1) := tail_af40_h563 I
  have h562 : HasDifferential E 2 (38,164) (40,165)
      (I.realization.basis .sphere 38 164 0) (I.realization.basis .sphere 40 165 1) := tail_af40_h562 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,40,165,["17,1,403,1", "8,6,55,1"]⟩ (by
    exact List.mem_of_getElem? (i := 343) (by rfl))
  change E.Page 2 (40,165) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 40 165 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 40 165 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 40 165 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,42,166,["0,1,16,1,403,1", "0,2,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 352) (by rfl))
  change E.Page 2 (42,166) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 42 166 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 42 166 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 42 166 1 := hf 1
  have hd0 : E.d 2 (40,165) (I.realization.basis .sphere 40 165 0) =
      I.realization.basis .sphere 42 166 1 := h563.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 5 (40,165) (I.realization.basis .sphere 40 165 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h562
  have hd1 : E.d 2 (40,165) (I.realization.basis .sphere 40 165 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (40,165)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(40,165)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af40 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (40,165)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (40,165))
  exact tail_af40 I

private theorem tail_af41_four_h567 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (41,166) (44,168)
    (I.realization.basis .sphere 41 166 0) (I.realization.basis .sphere 44 168 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,41,166,[0],44,168,[0],"S0_AdamsE2_ss",5441⟩ (by
    exact List.mem_of_getElem? (i := 567) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (41,166) (44,168) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 41 166 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 44 168 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af41_four_h568 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (41,166) (43,167)
    (I.realization.basis .sphere 41 166 1) (I.realization.basis .sphere 43 167 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,41,166,[1],43,167,[1],"S0_AdamsE2_ss",5442⟩ (by
    exact List.mem_of_getElem? (i := 568) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (41,166) (43,167) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 41 166 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 43 167 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af41_four_h574 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (42,167) (44,168)
    (I.realization.basis .sphere 42 167 0) (I.realization.basis .sphere 44 168 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,42,167,[0],44,168,[1],"S0_AdamsE2_ss",5540⟩ (by
    exact List.mem_of_getElem? (i := 574) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (42,167) (44,168) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 42 167 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 44 168 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af41_four (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (41,166)) := by
  classical
  let E := sequence D .sphere
  have h567 : HasDifferential E 3 (41,166) (44,168)
      (I.realization.basis .sphere 41 166 0) (I.realization.basis .sphere 44 168 0) := tail_af41_four_h567 I
  have h568 : HasDifferential E 2 (41,166) (43,167)
      (I.realization.basis .sphere 41 166 1) (I.realization.basis .sphere 43 167 1) := tail_af41_four_h568 I
  have h574 : HasDifferential E 2 (42,167) (44,168)
      (I.realization.basis .sphere 42 167 0) (I.realization.basis .sphere 44 168 1) := tail_af41_four_h574 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,41,166,["1,1,685,1", "0,1,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 348) (by rfl))
  change E.Page 2 (41,166) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 41 166 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 41 166 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 41 166 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,42,167,["0,2,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 353) (by rfl))
  change E.Page 2 (42,167) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 42 167 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 42 167 0 := hf 0
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,44,168,["8,5,110,1", "0,4,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 360) (by rfl))
  change E.Page 2 (44,168) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 44 168 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 44 168 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 44 168 1 := hg 1
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,43,167,["0,2,16,1,403,1", "0,3,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 356) (by rfl))
  change E.Page 2 (43,167) ≃ₗ[ℤ] (Fin 2 →₀ F2) at k
  change ∀ i : Fin 2, k.symm (Finsupp.single i 1) = I.realization.basis .sphere 43 167 i.val at hk
  have hk0 : k.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 43 167 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 43 167 1 := hk 1
  have d20 : E.d 2 (42,167) (I.realization.basis .sphere 42 167 0) =
      I.realization.basis .sphere 44 168 1 := h574.eq_on_page_two.2
  have incoming_zero (x : E.Page 2 (42,167)) : g (E.d 2 (42,167) x) 0 = 0 := by
    have hall (a : Fin 1 →₀ F2) : g (E.d 2 (42,167) (f.symm a)) 0 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · fin_cases i
          change g (E.d 2 (42,167) (f.symm (Finsupp.single 0 1))) 0 = 0
          rw [hf0,d20,←hg1,LinearEquiv.apply_symm_apply]
          norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h567
  have hd' : E.d 3 (41,166) a = b := hd
  have hbne : b ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (42,167) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (44,168)).Z_anti bot_le) ≫
      (E.ssData (44,168)).pageπ 0) z ∈ LinearMap.range (E.d 2 (42,167)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (44,168)).Z_anti bot_le) ≫
      (E.ssData (44,168)).pageπ 0) z = I.realization.basis .sphere 44 168 0 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming_zero u
    rw [hu,←hg0,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  have hn : E.d 2 (41,166) (e.symm (Finsupp.single 1 1)) ≠ 0 := by
    rw [he1]
    have hh : E.d 2 (41,166) (I.realization.basis .sphere 41 166 1) =
      I.realization.basis .sphere 43 167 1 := h568.eq_on_page_two.2
    rw [hh,←hk1]
    intro hz
    have hz' := congrArg k hz
    simpa using hz'
  have frame : ∀ q : E.Page 3 (41,166), q=0 ∨ q=a :=
    frame_after_second (by change (2:ℤ)≤2; omega) (by decide) e (he0.symm ▸ ha) hn
  have ker (q : E.Page 3 (41,166)) (hq : E.d 3 (41,166) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((41,166)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [ker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (41,166)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem stem125_e5_zero_af41 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (41,166)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (41,166))
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 5 41 166
    (by decide) (by decide) (tail_af41_four I)

private theorem tail_af42_h574 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (42,167) (44,168)
    (I.realization.basis .sphere 42 167 0) (I.realization.basis .sphere 44 168 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,42,167,[0],44,168,[1],"S0_AdamsE2_ss",5540⟩ (by
    exact List.mem_of_getElem? (i := 574) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (42,167) (44,168) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 42 167 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 44 168 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af42 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (42,167)) := by
  classical
  let E := sequence D .sphere
  have h574 : HasDifferential E 2 (42,167) (44,168)
      (I.realization.basis .sphere 42 167 0) (I.realization.basis .sphere 44 168 1) := tail_af42_h574 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,42,167,["0,2,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 353) (by rfl))
  change E.Page 2 (42,167) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 42 167 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 42 167 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,44,168,["8,5,110,1", "0,4,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 360) (by rfl))
  change E.Page 2 (44,168) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 44 168 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 44 168 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 44 168 1 := hf 1
  have hd0 : E.d 2 (42,167) (I.realization.basis .sphere 42 167 0) =
      I.realization.basis .sphere 44 168 1 := h574.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (42,167)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(42,167)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af42 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (42,167)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (42,167))
  exact tail_af42 I

private theorem stem125_af43 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (43,168)) := by
  classical
  let E := sequence D .sphere
  have one_cases {p : ℤ × ℤ} (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2))
      (a : E.Page 2 p) : a=0 ∨ a=e.symm (Finsupp.single 0 1) := by
    have hc : e a = Finsupp.single 0 (e a 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have ht : e a 0 = 0 ∨ e a 0 = 1 := by
      generalize e a 0 = c
      fin_cases c <;> simp
    rcases ht with ht|ht
    · left
      apply e.injective
      rw [hc]
      simp only [ht,Finsupp.single_zero,map_zero]
    · right
      apply e.injective
      rw [hc]
      simp only [ht,LinearEquiv.apply_symm_apply]
  have two_cases {p : ℤ × ℤ} (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Core.Algebra.F2))
      (a : E.Page 2 p) : a=0 ∨ a=e.symm (Finsupp.single 0 1) ∨
        a=e.symm (Finsupp.single 1 1) ∨ a=e.symm (Finsupp.single 0 1)+e.symm (Finsupp.single 1 1) := by
    have hc : e a = Finsupp.single 0 (e a 0) + Finsupp.single 1 (e a 1) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have h0 : e a 0 = 0 ∨ e a 0 = 1 := by generalize e a 0=c; fin_cases c <;> simp
    have h1 : e a 1 = 0 ∨ e a 1 = 1 := by generalize e a 1=c; fin_cases c <;> simp
    rcases h0 with h0|h0 <;> rcases h1 with h1|h1
    · left
      apply e.injective
      rw [hc]
      simp only [h0,h1,Finsupp.single_zero,add_zero,map_zero]
    · right; right; left
      apply e.injective
      rw [hc]
      simp only [h0,h1,Finsupp.single_zero,zero_add,LinearEquiv.apply_symm_apply]
    · right; left
      apply e.injective
      rw [hc]
      simp only [h0,h1,Finsupp.single_zero,add_zero,LinearEquiv.apply_symm_apply]
    · right; right; right
      apply e.injective
      rw [hc]
      simp only [h0,h1,map_add,LinearEquiv.apply_symm_apply]
  have nonzero_basis {p : ℤ × ℤ} {n : ℕ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin n →₀ KIP126.Core.Algebra.F2)) (i : Fin n) :
      e.symm (Finsupp.single i 1) ≠ 0 := by
    intro hz
    have hh := congrArg (fun z => e z i) hz
    simpa using hh
  have at_two {p : ℤ × ℤ} {r : ℤ} {a : E.Page 2 p} {b : E.Page r p}
      (hr : 2≤r) (hb : RepresentsOnPage E r p a b) : RepresentsOnPage E 2 p a a := by
    obtain ⟨c,hc⟩ := represents_before (by decide : (2:ℤ)≤2) hr hb
    rw [←hc.eq_on_page_two] at hc
    exact hc
  have row578 : HasDifferential E 3 (42,168) (45,170)
      (I.realization.basis .sphere 42 168 0) (I.realization.basis .sphere 45 170 0) := by
    have hh := I.results _ (List.mem_of_getElem? (i := 578) (by rfl))
    dsimp only [Statement] at hh
    obtain ⟨u,hu,v,hv,h⟩ := hh
    change HasDifferential E 3 (42,168) (45,170) u v at h
    change I.realization.decode .sphere 42 168 [0] = some u at hu
    change I.realization.decode .sphere 45 170 [0] = some v at hv
    have vx : Raw.coordinatesValid Raw.degrees .sphere 42 168 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 45 170 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hu hv
    rw [←hu,←hv] at h
    exact h
  have row582 : HasDifferential E 4 (43,168) (47,171)
      (I.realization.basis .sphere 43 168 0) (I.realization.basis .sphere 47 171 0) := by
    have hh := I.results _ (List.mem_of_getElem? (i := 582) (by rfl))
    dsimp only [Statement] at hh
    obtain ⟨u,hu,v,hv,h⟩ := hh
    change HasDifferential E 4 (43,168) (47,171) u v at h
    change I.realization.decode .sphere 43 168 [0] = some u at hu
    change I.realization.decode .sphere 47 171 [0] = some v at hv
    have vx : Raw.coordinatesValid Raw.degrees .sphere 43 168 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 47 171 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hu hv
    rw [←hu,←hv] at h
    exact h
  have row583 : HasDifferential E 2 (43,168) (45,169)
      (I.realization.basis .sphere 43 168 1) (I.realization.basis .sphere 45 169 0) := by
    have hh := I.results _ (List.mem_of_getElem? (i := 583) (by rfl))
    dsimp only [Statement] at hh
    obtain ⟨u,hu,v,hv,h⟩ := hh
    change HasDifferential E 2 (43,168) (45,169) u v at h
    change I.realization.decode .sphere 43 168 [1] = some u at hu
    change I.realization.decode .sphere 45 169 [0] = some v at hv
    have vx : Raw.coordinatesValid Raw.degrees .sphere 43 168 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 45 169 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hu hv
    rw [←hu,←hv] at h
    exact h
  have row589 : HasDifferential E 2 (44,169) (46,170)
      (I.realization.basis .sphere 44 169 0) (I.realization.basis .sphere 46 170 0) := by
    have hh := I.results _ (List.mem_of_getElem? (i := 589) (by rfl))
    dsimp only [Statement] at hh
    obtain ⟨u,hu,v,hv,h⟩ := hh
    change HasDifferential E 2 (44,169) (46,170) u v at h
    change I.realization.decode .sphere 44 169 [0] = some u at hu
    change I.realization.decode .sphere 46 170 [0] = some v at hv
    have vx : Raw.coordinatesValid Raw.degrees .sphere 44 169 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 46 170 [0] = true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hu hv
    rw [←hu,←hv] at h
    exact h
  obtain ⟨e43_168,h43_168⟩ := I.basis ⟨.sphere,43,168,["8,5,111,1", "0,3,17,1,403,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (43,168) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Core.Algebra.F2) at e43_168
  change ∀i : Fin 2, e43_168.symm (Finsupp.single i 1) = I.realization.basis .sphere 43 168 i.val at h43_168
  obtain ⟨e44_169,h44_169⟩ := I.basis ⟨.sphere,44,169,["0,4,17,1,403,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (44,169) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2) at e44_169
  change ∀i : Fin 1, e44_169.symm (Finsupp.single i 1) = I.realization.basis .sphere 44 169 i.val at h44_169
  obtain ⟨e45_169,h45_169⟩ := I.basis ⟨.sphere,45,169,["0,5,685,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (45,169) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2) at e45_169
  change ∀i : Fin 1, e45_169.symm (Finsupp.single i 1) = I.realization.basis .sphere 45 169 i.val at h45_169
  obtain ⟨e45_170,h45_170⟩ := I.basis ⟨.sphere,45,170,["0,5,17,1,403,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (45,170) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2) at e45_170
  change ∀i : Fin 1, e45_170.symm (Finsupp.single i 1) = I.realization.basis .sphere 45 170 i.val at h45_170
  obtain ⟨e46_170,h46_170⟩ := I.basis ⟨.sphere,46,170,["0,6,685,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (46,170) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2) at e46_170
  change ∀i : Fin 1, e46_170.symm (Finsupp.single i 1) = I.realization.basis .sphere 46 170 i.val at h46_170
  obtain ⟨e47_171,h47_171⟩ := I.basis ⟨.sphere,47,171,["8,3,253,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (47,171) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2) at e47_171
  change ∀i : Fin 1, e47_171.symm (Finsupp.single i 1) = I.realization.basis .sphere 47 171 i.val at h47_171
  have h43_168_0 : e43_168.symm (Finsupp.single 0 1) = I.realization.basis .sphere 43 168 0 := h43_168 0
  have h43_168_1 : e43_168.symm (Finsupp.single 1 1) = I.realization.basis .sphere 43 168 1 := h43_168 1
  have h44_169_0 : e44_169.symm (Finsupp.single 0 1) = I.realization.basis .sphere 44 169 0 := h44_169 0
  have h45_169_0 : e45_169.symm (Finsupp.single 0 1) = I.realization.basis .sphere 45 169 0 := h45_169 0
  have h45_170_0 : e45_170.symm (Finsupp.single 0 1) = I.realization.basis .sphere 45 170 0 := h45_170 0
  have h46_170_0 : e46_170.symm (Finsupp.single 0 1) = I.realization.basis .sphere 46 170 0 := h46_170 0
  have h47_171_0 : e47_171.symm (Finsupp.single 0 1) = I.realization.basis .sphere 47 171 0 := h47_171 0
  have d44 : E.d 2 (44,169) (I.realization.basis .sphere 44 169 0) = I.realization.basis .sphere 46 170 0 := row589.eq_on_page_two.choose_spec
  have n46 : I.realization.basis .sphere 46 170 0 ≠ 0 := by
    rw [←h46_170_0]
    exact nonzero_basis e46_170 0
  have zero44 : Subsingleton (E.Page 3 (44,169)) := by
    have ker (a : E.Page 2 (44,169)) (ha : E.d 2 (44,169) a=0) : a=0 := by
      rcases one_cases e44_169 a with hz|hz
      · exact hz
      · rw [h44_169_0] at hz
        exact (n46 (by simpa only [hz,d44] using ha)).elim
    let S := E.pageShortComplex 2 ((44,169)-E.diffDeg 2)
    have hex : S.Exact := S.moduleCat_exact_iff.mpr (by
      intro a ha
      exact ⟨0,by rw [ker a ha,map_zero]⟩)
    exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 2 (44,169)
      (by change (2:ℤ)≤2; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hex))
  obtain ⟨_,u3,v3,hu3,hv3,huv3⟩ := row578
  have d45 : E.d 2 (45,170) (I.realization.basis .sphere 45 170 0) = 0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (at_two (by decide) hv3) ⟨v3,hv3⟩
  have in2 : E.d 2 ((47,171)-E.diffDeg 2) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change E.d 2 (45,170) a=0
    rcases one_cases e45_170 a with ha|ha
    · rw [ha,map_zero]
    · rw [ha,h45_170_0,d45]
  have in3 : E.d 3 ((47,171)-E.diffDeg 3) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change E.d 3 (44,169) a=0
    rw [zero44.elim a 0,map_zero]
  obtain ⟨_,x4,y4,hx4,hy4,hxy4⟩ := row582
  have hxy : E.d 4 (43,168) x4=y4 := hxy4
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hy4
  have n47 : I.realization.basis .sphere 47 171 0 ≠ 0 := by
    rw [←h47_171_0]
    exact nonzero_basis e47_171 0
  have ny3 : y3 ≠ 0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) in2 hy3 (at_two (by decide) hy4) n47
  have ny4 : y4 ≠ 0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) in3 hy4 hy3 ny3
  have dx0 : E.d 2 (43,168) (I.realization.basis .sphere 43 168 0)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (at_two (by decide) hx4) ⟨x4,hx4⟩
  have dx1 : E.d 2 (43,168) (I.realization.basis .sphere 43 168 1) = I.realization.basis .sphere 45 169 0 := row583.eq_on_page_two.choose_spec
  have nx1 : I.realization.basis .sphere 45 169 0 ≠ 0 := by
    rw [←h45_169_0]
    exact nonzero_basis e45_169 0
  have ker2 (a : E.Page 2 (43,168)) (ha : E.d 2 (43,168) a=0) :
      a=0 ∨ a=I.realization.basis .sphere 43 168 0 := by
    rcases two_cases e43_168 a with hz|hz|hz|hz
    · exact Or.inl hz
    · exact Or.inr (hz.trans h43_168_0)
    · rw [h43_168_1] at hz
      exact (nx1 (by simpa only [hz,dx1] using ha)).elim
    · rw [h43_168_0,h43_168_1] at hz
      exact (nx1 (by simpa only [hz,map_add,dx0,dx1,zero_add] using ha)).elim
  obtain ⟨_,z4,hz4,hz4x⟩ := hx4
  let A := E.ssData (43,168)
  let z3 := (Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide))) z4
  let x3 := A.pageπ 1 z3
  have hdown : (Subobject.ofLE (A.Z 1) (A.Z 0) (A.Z_anti (by decide)) ≫ A.pageπ 0) z3 = I.realization.basis .sphere 43 168 0 := by
    change ((Subobject.ofLE (A.Z 2) (A.Z 1) _) ≫ Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0) z4 = _
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz4
  have hz3 : RepresentsOnPage E 3 (43,168) (I.realization.basis .sphere 43 168 0) x3 := by
    exact ⟨by decide,z3,hdown,rfl⟩
  have frame3 (a : E.Page 3 (43,168)) : a=0 ∨ a=x3 := by
    apply next_page_two_of_kernel E 2 (by change (2:ℤ)≤2; omega) (43,168) z3
    intro q hq
    have hc := ker2 q hq
    change q=0 ∨ q=(Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0) z3
    rwa [hdown]
  have frame4 (a : E.Page 4 (43,168)) : a=0 ∨ a=x4 := by
    have h := next_page_two_of_kernel E 3 (by change (2:ℤ)≤3; omega) (43,168) z4 (by
      intro q hq
      exact frame3 q) a
    change a=0 ∨ a=A.pageπ 2 z4 at h
    change A.pageπ 2 z4=x4 at hz4x
    rwa [hz4x] at h
  have ker4 (a : E.Page 4 (43,168)) (ha : E.d 4 (43,168) a=0) : a=0 := by
    rcases frame4 a with hz|hz
    · exact hz
    · exact (ny4 (by simpa only [hz,hxy] using ha)).elim
  let S := E.pageShortComplex 4 ((43,168)-E.diffDeg 4)
  have hex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro a ha
    exact ⟨0,by rw [ker4 a ha,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 4 (43,168)
    (by change (2:ℤ)≤4; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hex))

private theorem stem125_e5_zero_af43 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (43,168)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (43,168))
  exact stem125_af43 I

private theorem tail_af44_h589 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (44,169) (46,170)
    (I.realization.basis .sphere 44 169 0) (I.realization.basis .sphere 46 170 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,44,169,[0],46,170,[0],"S0_AdamsE2_ss",5772⟩ (by
    exact List.mem_of_getElem? (i := 589) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (44,169) (46,170) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 44 169 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 46 170 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af44 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (44,169)) := by
  classical
  let E := sequence D .sphere
  have h589 : HasDifferential E 2 (44,169) (46,170)
      (I.realization.basis .sphere 44 169 0) (I.realization.basis .sphere 46 170 0) := tail_af44_h589 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,44,169,["0,4,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 361) (by rfl))
  change E.Page 2 (44,169) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 44 169 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 44 169 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,46,170,["0,6,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 368) (by rfl))
  change E.Page 2 (46,170) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 46 170 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 46 170 0 := hf 0
  have hd0 : E.d 2 (44,169) (I.realization.basis .sphere 44 169 0) =
      I.realization.basis .sphere 46 170 0 := h589.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (44,169)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(44,169)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af44 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (44,169)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (44,169))
  exact tail_af44 I

private theorem tail_af45_h594 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (42,168) (45,170)
    (I.realization.basis .sphere 42 168 0) (I.realization.basis .sphere 45 170 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,42,168,[0],45,170,[0],"S0_AdamsE2_ss",5862⟩ (by
    exact List.mem_of_getElem? (i := 594) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (42,168) (45,170) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 42 168 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 45 170 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af45 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (45,170)) := by
  classical
  let E := sequence D .sphere
  have h594 : HasDifferential E 3 (42,168) (45,170)
      (I.realization.basis .sphere 42 168 0) (I.realization.basis .sphere 45 170 0) := tail_af45_h594 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,45,170,["0,5,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 365) (by rfl))
  change E.Page 2 (45,170) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 45 170 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 45 170 0 := he 0
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) h594

private theorem stem125_e5_zero_af45 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (45,170)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (45,170))
  exact tail_af45 I

private theorem tail_af46_h598 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (42,168) (46,171)
    (I.realization.basis .sphere 42 168 2) (I.realization.basis .sphere 46 171 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,42,168,[2],46,171,[0],"S0_AdamsE2_ss",5977⟩ (by
    exact List.mem_of_getElem? (i := 598) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (42,168) (46,171) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 42 168 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 46 171 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af46 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (46,171)) := by
  classical
  let E := sequence D .sphere
  have h598 : HasDifferential E 4 (42,168) (46,171)
      (I.realization.basis .sphere 42 168 2) (I.realization.basis .sphere 46 171 0) := tail_af46_h598 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,46,171,["8,2,17,1,200,1"]⟩ (by
    exact List.mem_of_getElem? (i := 369) (by rfl))
  change E.Page 2 (46,171) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 46 171 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 46 171 0 := he 0
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h598

private theorem stem125_e5_zero_af46 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (46,171)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (46,171))
  exact tail_af46 I

private theorem stem125_e5_zero_38_to_46 (I : Inputs D L G)
    (s : ℕ) (hs : 38 ≤ s) (hs' : s ≤ 46) :
    Subsingleton ((sequence D .sphere).Page 5 (s,(s : ℤ)+125)) := by
  classical

  interval_cases s
  · exact stem125_e5_zero_af38 I
  · exact stem125_e5_zero_af39 I
  · exact stem125_e5_zero_af40 I
  · exact stem125_e5_zero_af41 I
  · exact stem125_e5_zero_af42 I
  · exact stem125_e5_zero_af43 I
  · exact stem125_e5_zero_af44 I
  · exact stem125_e5_zero_af45 I
  · exact stem125_e5_zero_af46 I

private theorem tail_af47 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (47,172)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,47,172,[]⟩ (by
    exact List.mem_of_getElem? (i := 374) (by rfl))
  change E.Page 2 (47,172) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 47 172 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af47 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (47,172)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (47,172))
  exact tail_af47 I

private theorem tail_af48 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (48,173)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,48,173,[]⟩ (by
    exact List.mem_of_getElem? (i := 377) (by rfl))
  change E.Page 2 (48,173) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 48 173 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af48 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (48,173)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (48,173))
  exact tail_af48 I

private theorem tail_af49_h609 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (45,171) (49,174)
    (I.realization.basis .sphere 45 171 0) (I.realization.basis .sphere 49 174 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,45,171,[0],49,174,[0],"S0_AdamsE2_ss",6296⟩ (by
    exact List.mem_of_getElem? (i := 609) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (45,171) (49,174) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 45 171 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 49 174 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af49 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (49,174)) := by
  classical
  let E := sequence D .sphere
  have h609 : HasDifferential E 4 (45,171) (49,174)
      (I.realization.basis .sphere 45 171 0) (I.realization.basis .sphere 49 174 0) := tail_af49_h609 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,49,174,["8,1,607,1"]⟩ (by
    exact List.mem_of_getElem? (i := 380) (by rfl))
  change E.Page 2 (49,174) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 49 174 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 49 174 0 := he 0
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h609

private theorem stem125_e5_zero_af49 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (49,174)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (49,174))
  exact tail_af49 I

private theorem tail_af50 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (50,175)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,50,175,[]⟩ (by
    exact List.mem_of_getElem? (i := 384) (by rfl))
  change E.Page 2 (50,175) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 50 175 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af50 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (50,175)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (50,175))
  exact tail_af50 I

private theorem tail_af51 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (51,176)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,51,176,[]⟩ (by
    exact List.mem_of_getElem? (i := 387) (by rfl))
  change E.Page 2 (51,176) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 51 176 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af51 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (51,176)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (51,176))
  exact tail_af51 I

private theorem stem125_af52 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (52,177)) := by
  classical
  let E := sequence D .sphere
  have empty (s t : ℕ) (hd : (⟨.sphere,s,t,[]⟩ : Raw.Degree) ∈ Raw.degrees)
      (r : ℤ) (hr : 2 ≤ r) : Subsingleton (E.Page r (s,t)) := by
    obtain ⟨e,_⟩ := I.basis _ hd
    change E.Page 2 (s,t) ≃ₗ[ℤ] (Fin 0 →₀ KIP126.Core.Algebra.F2) at e
    have he : Subsingleton (E.Page 2 (s,t)) := e.injective.subsingleton
    exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r s t
      (by decide) hr he
  have h54 : Subsingleton (E.Page 2 (54,179)) :=
    empty 54 179 (by simp [Raw.degrees]) 2 (by decide)
  have h53 : Subsingleton (E.Page 3 (53,178)) :=
    empty 53 178 (by simp [Raw.degrees]) 3 (by decide)
  have in2 : E.d 2 ((56,180)-E.diffDeg 2) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change E.d 2 (54,179) x=0
    rw [h54.elim x 0,map_zero]
  have in3 : E.d 3 ((56,180)-E.diffDeg 3) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change E.d 3 (53,178) x=0
    rw [h53.elim x 0,map_zero]
  have hrow := I.results _ (List.mem_of_getElem? (i := 618) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential E 4 (52,177) (56,180) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 52 177 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 56 180 [0] = true := rfl
  change I.realization.decode .sphere 52 177 [0] = some a at ha
  change I.realization.decode .sphere 56 180 [0] = some b at hb
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  obtain ⟨_,x,y,hx,hy,hxy⟩ := h
  have hxy' : E.d 4 (52,177) x=y := hxy
  obtain ⟨eT,heT⟩ := I.basis ⟨.sphere,56,180,["8,1,661,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (56,180) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2) at eT
  change ∀i : Fin 1, eT.symm (Finsupp.single i 1) = I.realization.basis .sphere 56 180 i.val at heT
  have hn : I.realization.basis .sphere 56 180 0 ≠ 0 := by
    have h0 := heT (0 : Fin 1)
    change eT.symm (Finsupp.single (0 : Fin 1) 1) = I.realization.basis .sphere 56 180 0 at h0
    rw [←h0]
    intro hz
    have hc := congrArg (fun z => eT z (0 : Fin 1)) hz
    simpa using hc
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hy
  have hy2 : RepresentsOnPage E 2 (56,180)
      (I.realization.basis .sphere 56 180 0) (I.realization.basis .sphere 56 180 0) := by
    obtain ⟨y2,hy2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hy
    rw [←hy2.eq_on_page_two] at hy2
    exact hy2
  have hn3 : y3 ≠ 0 := represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)≤2) in2 hy3 hy2 hn
  have hn4 : y ≠ 0 := represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤3; omega)
    (by decide : (2:ℤ)≤3) in3 hy hy3 hn3
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,52,177,["8,2,469,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (52,177) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Core.Algebra.F2) at e
  change ∀i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 52 177 i.val at he
  have frame (a : E.Page 4 (52,177)) : a=0 ∨ a=x := by
    have hv (i : Fin 1) : RepresentsOnPage E 4 (52,177) (e.symm (Finsupp.single i 1)) x := by
      rw [he i]
      fin_cases i
      exact hx
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤4) e (fun _ => x) hv a
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hc
    by_cases hcz : c 0=0
    · exact Or.inl (by simpa only [hcz,ite_true] using hc)
    · exact Or.inr (by simpa only [hcz,ite_false] using hc)
  have ker (a : E.Page 4 (52,177)) (ha : E.d 4 (52,177) a=0) : a=0 := by
    rcases frame a with hz|hz
    · exact hz
    · exact (hn4 (by simpa only [hz,hxy'] using ha)).elim
  let S := E.pageShortComplex 4 ((52,177)-E.diffDeg 4)
  have hex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro a ha
    exact ⟨0,by rw [ker a ha,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 4 (52,177)
    (by change (2:ℤ)≤4; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hex))

private theorem stem125_e5_zero_af52 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (52,177)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (52,177))
  exact stem125_af52 I

private theorem tail_af53 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (53,178)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,53,178,[]⟩ (by
    exact List.mem_of_getElem? (i := 393) (by rfl))
  change E.Page 2 (53,178) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 53 178 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af53 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (53,178)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (53,178))
  exact tail_af53 I

private theorem tail_af54 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (54,179)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,54,179,[]⟩ (by
    exact List.mem_of_getElem? (i := 396) (by rfl))
  change E.Page 2 (54,179) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 54 179 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af54 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (54,179)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (54,179))
  exact tail_af54 I

private theorem tail_af55_h626 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (55,180) (57,181)
    (I.realization.basis .sphere 55 180 0) (I.realization.basis .sphere 57 181 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,55,180,[0],57,181,[0],"S0_AdamsE2_ss",7007⟩ (by
    exact List.mem_of_getElem? (i := 626) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (55,180) (57,181) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 55 180 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 57 181 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af55 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (55,180)) := by
  classical
  let E := sequence D .sphere
  have h626 : HasDifferential E 2 (55,180) (57,181)
      (I.realization.basis .sphere 55 180 0) (I.realization.basis .sphere 57 181 0) := tail_af55_h626 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,55,180,["16,1,554,1"]⟩ (by
    exact List.mem_of_getElem? (i := 399) (by rfl))
  change E.Page 2 (55,180) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 55 180 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 55 180 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,57,181,["0,1,8,1,661,1"]⟩ (by
    exact List.mem_of_getElem? (i := 408) (by rfl))
  change E.Page 2 (57,181) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 57 181 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 57 181 0 := hf 0
  have hd0 : E.d 2 (55,180) (I.realization.basis .sphere 55 180 0) =
      I.realization.basis .sphere 57 181 0 := h626.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (55,180)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(55,180)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af55 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (55,180)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (55,180))
  exact tail_af55 I

private theorem tail_af56_h629 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (56,181) (58,182)
    (I.realization.basis .sphere 56 181 0) (I.realization.basis .sphere 58 182 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,56,181,[0],58,182,[0],"S0_AdamsE2_ss",7162⟩ (by
    exact List.mem_of_getElem? (i := 629) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (56,181) (58,182) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 56 181 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 58 182 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af56 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (56,181)) := by
  classical
  let E := sequence D .sphere
  have h629 : HasDifferential E 2 (56,181) (58,182)
      (I.realization.basis .sphere 56 181 0) (I.realization.basis .sphere 58 182 0) := tail_af56_h629 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,56,181,["0,1,16,1,554,1"]⟩ (by
    exact List.mem_of_getElem? (i := 404) (by rfl))
  change E.Page 2 (56,181) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 56 181 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 56 181 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,58,182,["0,2,8,1,661,1"]⟩ (by
    exact List.mem_of_getElem? (i := 413) (by rfl))
  change E.Page 2 (58,182) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 58 182 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 58 182 0 := hf 0
  have hd0 : E.d 2 (56,181) (I.realization.basis .sphere 56 181 0) =
      I.realization.basis .sphere 58 182 0 := h629.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (56,181)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(56,181)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af56 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (56,181)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (56,181))
  exact tail_af56 I

private theorem tail_af57_h633 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (54,180) (57,182)
    (I.realization.basis .sphere 54 180 0) (I.realization.basis .sphere 57 182 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,54,180,[0],57,182,[0],"S0_AdamsE2_ss",7247⟩ (by
    exact List.mem_of_getElem? (i := 633) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (54,180) (57,182) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 54 180 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 57 182 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af57 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (57,182)) := by
  classical
  let E := sequence D .sphere
  have h633 : HasDifferential E 3 (54,180) (57,182)
      (I.realization.basis .sphere 54 180 0) (I.realization.basis .sphere 57 182 0) := tail_af57_h633 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,57,182,["0,2,16,1,554,1"]⟩ (by
    exact List.mem_of_getElem? (i := 409) (by rfl))
  change E.Page 2 (57,182) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 57 182 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 57 182 0 := he 0
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) h633

private theorem stem125_e5_zero_af57 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (57,182)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (57,182))
  exact tail_af57 I

private theorem tail_af58 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (58,183)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,58,183,[]⟩ (by
    exact List.mem_of_getElem? (i := 414) (by rfl))
  change E.Page 2 (58,183) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 58 183 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af58 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (58,183)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (58,183))
  exact tail_af58 I

private theorem tail_af59 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (59,184)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,59,184,[]⟩ (by
    exact List.mem_of_getElem? (i := 417) (by rfl))
  change E.Page 2 (59,184) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 59 184 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af59 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (59,184)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (59,184))
  exact tail_af59 I

private theorem tail_af60 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (60,185)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,60,185,[]⟩ (by
    exact List.mem_of_getElem? (i := 420) (by rfl))
  change E.Page 2 (60,185) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 60 185 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af60 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (60,185)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (60,185))
  exact tail_af60 I

private theorem tail_af61 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (61,186)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,61,186,[]⟩ (by
    exact List.mem_of_getElem? (i := 423) (by rfl))
  change E.Page 2 (61,186) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 61 186 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af61 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (61,186)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (61,186))
  exact tail_af61 I

private theorem tail_af62 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (62,187)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,62,187,[]⟩ (by
    exact List.mem_of_getElem? (i := 426) (by rfl))
  change E.Page 2 (62,187) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 62 187 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af62 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (62,187)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (62,187))
  exact tail_af62 I

private theorem tail_af63 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (63,188)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,63,188,[]⟩ (by
    exact List.mem_of_getElem? (i := 429) (by rfl))
  change E.Page 2 (63,188) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 63 188 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af63 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (63,188)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (63,188))
  exact tail_af63 I

private theorem tail_af64 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (64,189)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,64,189,[]⟩ (by
    exact List.mem_of_getElem? (i := 432) (by rfl))
  change E.Page 2 (64,189) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 64 189 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af64 (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (64,189)) := by
  classical
  change Subsingleton ((sequence D .sphere).Page 5 (64,189))
  exact tail_af64 I

private theorem stem125_e5_zero_47_to_64 (I : Inputs D L G)
    (s : ℕ) (hs : 47 ≤ s) (hs' : s ≤ 64) :
    Subsingleton ((sequence D .sphere).Page 5 (s,(s : ℤ)+125)) := by
  classical

  interval_cases s
  · exact stem125_e5_zero_af47 I
  · exact stem125_e5_zero_af48 I
  · exact stem125_e5_zero_af49 I
  · exact stem125_e5_zero_af50 I
  · exact stem125_e5_zero_af51 I
  · exact stem125_e5_zero_af52 I
  · exact stem125_e5_zero_af53 I
  · exact stem125_e5_zero_af54 I
  · exact stem125_e5_zero_af55 I
  · exact stem125_e5_zero_af56 I
  · exact stem125_e5_zero_af57 I
  · exact stem125_e5_zero_af58 I
  · exact stem125_e5_zero_af59 I
  · exact stem125_e5_zero_af60 I
  · exact stem125_e5_zero_af61 I
  · exact stem125_e5_zero_af62 I
  · exact stem125_e5_zero_af63 I
  · exact stem125_e5_zero_af64 I

/-- This is a finite, record-derived assertion.  There are 38 staircase
rows in this range, all at levels 2,3,4,9996,9997,9998; certification must
prove their equations and local basis completeness before deriving this.
Empty components use `I.basis` on explicitly included empty degrees. -/
theorem stem125_e5_zero_finite (I : Inputs D L G)
    (s : ℕ) (hs : 26 ≤ s) (hs' : s ≤ 64) :
    Subsingleton ((sequence D .sphere).Page 5 (s,(s : ℤ)+125)) := by
  by_cases h37 : s ≤ 37
  · exact stem125_e5_zero_26_to_37 I s hs h37
  · by_cases h46 : s ≤ 46
    · exact stem125_e5_zero_38_to_46 I s (by omega) h46
    · exact stem125_e5_zero_47_to_64 I s (by omega) hs'
end

section
open CategoryTheory.Limits KIP126.Core.Algebra KIP126.Computation.Near126 in
/-- The AF15 source is NONZERO on E5: the selected S0_ss3152 equation is
d5(h1*x124,14)=d0^2*[Delta Delta1 g]. Nonzero follows from reconstruction
of both E5 components, not from the equation alone. In particular it would
be false to extend `stem125_e5_zero_finite` down to all s>=15, s!=25. -/
private theorem af17_three_h387 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (17,142) (19,143)
    (I.realization.basis .sphere 17 142 1) (I.realization.basis .sphere 19 143 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,17,142,[1],19,143,[1],"S0_AdamsE2_ss",3320⟩ (by
    exact List.mem_of_getElem? (i := 387) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (17,142) (19,143) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 17 142 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 19 143 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af17_three_h386 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (15,141) (17,142)
    (I.realization.basis .sphere 15 141 0) (I.realization.basis .sphere 17 142 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,15,141,[0],17,142,[0],"S0_AdamsE2_ss",3319⟩ (by
    exact List.mem_of_getElem? (i := 386) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (15,141) (17,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 141 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 142 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af17_three (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 3 (17,142)) := by
  classical
  let E := sequence D .sphere
  have h387 : HasDifferential E 2 (17,142) (19,143)
      (I.realization.basis .sphere 17 142 1) (I.realization.basis .sphere 19 143 1) := af17_three_h387 I
  have h386 : HasDifferential E 2 (15,141) (17,142)
      (I.realization.basis .sphere 15 141 0) (I.realization.basis .sphere 17 142 0) := af17_three_h386 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,17,142,["0,2,67,1,107,1", "0,3,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 240) (by rfl))
  change E.Page 2 (17,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 17 142 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 17 142 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 17 142 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,19,143,["8,1,293,1", "0,5,440,1"]⟩ (by
    exact List.mem_of_getElem? (i := 251) (by rfl))
  change E.Page 2 (19,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 19 143 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 19 143 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 19 143 1 := hf 1
  have hd1 : E.d 2 (17,142) (I.realization.basis .sphere 17 142 1) =
      I.realization.basis .sphere 19 143 1 := h387.eq_on_page_two.2
  have hz0 : RepresentsOnPage E 3 (17,142) (I.realization.basis .sphere 17 142 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h386
  have hd0 : E.d 2 (17,142) (I.realization.basis .sphere 17 142 0) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hz0
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz0⟩
  apply third_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (17,142)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(17,142)) (r:=3) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, hd1, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0]
    simpa only [zero_add] using (hz0)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval


private theorem af16_d4_zero_h369 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,140) (16,141)
    (I.realization.basis .sphere 14 140 1) (I.realization.basis .sphere 16 141 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,14,140,[1],16,141,[2],"S0_AdamsE2_ss",3253⟩ (by
    exact List.mem_of_getElem? (i := 369) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,140) (16,141) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 140 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero_h370 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (12,138) (16,141)
    (I.realization.basis .sphere 12 138 3) (I.realization.basis .sphere 16 141 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,12,138,[3],16,141,[1],"S0_AdamsE2_ss",3254⟩ (by
    exact List.mem_of_getElem? (i := 370) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (12,138) (16,141) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero_h371 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (16,141) (18,142)
    (I.realization.basis .sphere 16 141 0) (I.realization.basis .sphere 18 142 0 + I.realization.basis .sphere 18 142 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,16,141,[0],18,142,[0, 1],"S0_AdamsE2_ss",3255⟩ (by
    exact List.mem_of_getElem? (i := 371) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (16,141) (18,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 16 141 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 142 [0, 1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero_h372 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (16,141) (18,142)
    (I.realization.basis .sphere 16 141 3) (I.realization.basis .sphere 18 142 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,16,141,[3],18,142,[1],"S0_AdamsE2_ss",3256⟩ (by
    exact List.mem_of_getElem? (i := 372) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (16,141) (18,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 16 141 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 142 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero (I : Inputs D L G) : (sequence D .sphere).d 4 (16,141)=0 := by
  classical
  let E := sequence D .sphere
  have h369 : HasDifferential E 2 (14,140) (16,141)
      (I.realization.basis .sphere 14 140 1) (I.realization.basis .sphere 16 141 2) := af16_d4_zero_h369 I
  have h370 : HasDifferential E 4 (12,138) (16,141)
      (I.realization.basis .sphere 12 138 3) (I.realization.basis .sphere 16 141 1) := af16_d4_zero_h370 I
  have h371 : HasDifferential E 2 (16,141) (18,142)
      (I.realization.basis .sphere 16 141 0) (I.realization.basis .sphere 18 142 0 + I.realization.basis .sphere 18 142 1) := af16_d4_zero_h371 I
  have h372 : HasDifferential E 2 (16,141) (18,142)
      (I.realization.basis .sphere 16 141 3) (I.realization.basis .sphere 18 142 1) := af16_d4_zero_h372 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,16,141,["473,1", "1,1,448,1", "0,1,67,1,107,1", "0,2,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 232) (by rfl))
  change E.Page 2 (16,141) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 141 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.realization.basis .sphere 16 141 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.realization.basis .sphere 16 141 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.realization.basis .sphere 16 141 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.realization.basis .sphere 16 141 3 := he 3
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,18,142,["0,1,472,1", "0,4,440,1"]⟩ (by
    exact List.mem_of_getElem? (i := 245) (by rfl))
  change E.Page 2 (18,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 18 142 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 18 142 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 18 142 1 := hf 1
  obtain ⟨_,u,v,hu,hv,hd⟩ := h370
  have hd' : E.d 4 (12,138) u=v := hd
  have hdv : E.d 4 (16,141) v=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=4) (p:=(12,138)) ⟨u,hd'⟩
  have hv2 : RepresentsOnPage E 2 (16,141) (I.realization.basis .sphere 16 141 1)
      (I.realization.basis .sphere 16 141 1) := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hv
    rw [←hb.eq_on_page_two] at hb
    exact hb
  have hd1 : E.d 2 (16,141) (I.realization.basis .sphere 16 141 1)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hv2 ⟨v,hv⟩
  have hz2 : RepresentsOnPage E 4 (16,141) (I.realization.basis .sphere 16 141 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h369
  have hd2 : E.d 2 (16,141) (I.realization.basis .sphere 16 141 2)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hz2
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz2⟩
  have hd0 : E.d 2 (16,141) (I.realization.basis .sphere 16 141 0) =
      I.realization.basis .sphere 18 142 0 + I.realization.basis .sphere 18 142 1 := h371.eq_on_page_two.2
  have hd3 : E.d 2 (16,141) (I.realization.basis .sphere 16 141 3) =
      I.realization.basis .sphere 18 142 1 := h372.eq_on_page_two.2
  apply fourth_d_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (16,141)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact ⟨0,RepresentsOnPage.zero (by decide),map_zero _⟩
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he3, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he2]
    exact ⟨0,hz2,map_zero _⟩
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he2, he3, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    exact ⟨v,hv,hdv⟩
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he3, hd1, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1, he2]
    exact ⟨v+0,represents_add_tail hv hz2,by rw [map_add,hdv,map_zero,add_zero]⟩
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, hd0, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he3, hd0, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, hd0, hd2, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he3, hd0, hd1, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval


private theorem af15_d5_target_nonzero_h397 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 5 (13,139) (18,143)
    (I.realization.basis .sphere 13 139 0) (I.realization.basis .sphere 18 143 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,5,13,139,[0],18,143,[0],"S0_AdamsE2_ss",3391⟩ (by
    exact List.mem_of_getElem? (i := 397) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (13,139) (18,143) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 139 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 143 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af15_d5_target_nonzero_h398 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (18,143) (20,144)
    (I.realization.basis .sphere 18 143 1) (I.realization.basis .sphere 20 144 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,18,143,[1],20,144,[1],"S0_AdamsE2_ss",3392⟩ (by
    exact List.mem_of_getElem? (i := 398) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (18,143) (20,144) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 18 143 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 20 144 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af15_d5_target_nonzero (I : Inputs D L G)
    (y : (sequence D .sphere).Page 5 (20,144))
    (hy : RepresentsOnPage (sequence D .sphere) 5 (20,144)
      (I.realization.basis .sphere 20 144 0) y) : y ≠ 0 := by
  classical
  let E := sequence D .sphere
  have h397 : HasDifferential E 5 (13,139) (18,143)
      (I.realization.basis .sphere 13 139 0) (I.realization.basis .sphere 18 143 0) := af15_d5_target_nonzero_h397 I
  have h398 : HasDifferential E 2 (18,143) (20,144)
      (I.realization.basis .sphere 18 143 1) (I.realization.basis .sphere 20 144 1) := af15_d5_target_nonzero_h398 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,18,143,["8,2,209,1", "0,4,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 246) (by rfl))
  change E.Page 2 (18,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 18 143 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 18 143 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 18 143 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,20,144,["8,2,212,1", "0,6,440,1"]⟩ (by
    exact List.mem_of_getElem? (i := 256) (by rfl))
  change E.Page 2 (20,144) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 20 144 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 20 144 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 20 144 1 := hf 1
  obtain ⟨_,u,v,hu,hv,hd⟩ := h397
  have hb0 : RepresentsOnPage E 2 (18,143) (I.realization.basis .sphere 18 143 0)
      (I.realization.basis .sphere 18 143 0) := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hv
    rw [←hb.eq_on_page_two] at hb
    exact hb
  have hd0 : E.d 2 (18,143) (I.realization.basis .sphere 18 143 0)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb0 ⟨v,hv⟩
  have hd1 : E.d 2 (18,143) (I.realization.basis .sphere 18 143 1)=I.realization.basis .sphere 20 144 1 := h398.eq_on_page_two.2
  have hcoord (x : E.Page 2 (18,143)) : f (E.d 2 (18,143) x) 0=0 := by
    have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [Finsupp.single_apply]
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    fin_cases c0 <;> fin_cases c1
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe]
      simp only [map_add,map_zero,he0,he1,hd0,hd1,zero_add,add_zero,←hf1,LinearEquiv.apply_symm_apply]
      norm_num [Finsupp.single_apply,Fin.ext_iff]
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe]
      simp only [map_add,map_zero,he0,he1,hd0,hd1,zero_add,add_zero,←hf1,LinearEquiv.apply_symm_apply]
      norm_num [Finsupp.single_apply,Fin.ext_iff]
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe]
      simp only [map_add,map_zero,he0,he1,hd0,hd1,zero_add,add_zero,←hf1,LinearEquiv.apply_symm_apply]
      norm_num [Finsupp.single_apply,Fin.ext_iff]
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
      rw [hxe]
      simp only [map_add,map_zero,he0,he1,hd0,hd1,zero_add,add_zero,←hf1,LinearEquiv.apply_symm_apply]
      norm_num [Finsupp.single_apply,Fin.ext_iff]
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) hy
  have ny3 : y3 ≠ 0 := by
    intro hz
    obtain ⟨_,zz,hzz,hzzy⟩ := hy3
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (18,143) zz).mp (hzzy.trans hz)
    change (Subobject.ofLE _ _ ((E.ssData (20,144)).Z_anti bot_le) ≫ (E.ssData (20,144)).pageπ 0) zz ∈ LinearMap.range (E.d 2 (18,143)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (20,144)).Z_anti bot_le) ≫ (E.ssData (20,144)).pageπ 0) zz = I.realization.basis .sphere 20 144 0 at hzz
    rw [hzz] at hh
    obtain ⟨q,hq⟩ := hh
    have hh := hcoord q
    rw [hq,←hf0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  have in3 : E.d 3 ((20,144)-E.diffDeg 3)=0 := by
    ext a
    change E.d 3 (17,142) a=0
    rw [(af17_three I).elim a 0,map_zero]
  have in4 : E.d 4 ((20,144)-E.diffDeg 4)=0 := af16_d4_zero I
  obtain ⟨y4,hy4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy
  have ny4 : y4 ≠ 0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) in3 hy4 hy3 ny3
  exact represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤4; omega) (by decide : (2:ℤ)≤4) in4 hy hy4 ny4

private theorem stem125_af15_nonzero_d5_h356 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 5 (15,140) (20,144)
    (I.realization.basis .sphere 15 140 2) (I.realization.basis .sphere 20 144 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,5,15,140,[2],20,144,[0],"S0_AdamsE2_ss",3152⟩ (by
    exact List.mem_of_getElem? (i := 356) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (15,140) (20,144) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 140 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 20 144 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

theorem stem125_af15_nonzero_d5 (I : Inputs D L G) :
    ∃ (x : Page D .sphere 15 140) (y : Page D .sphere 20 144),
      I.realization.decode .sphere 15 140 [2] = some x ∧
      I.realization.decode .sphere 20 144 [0] = some y ∧
      HasNonzeroDifferential (sequence D .sphere) 5 (15,140) (20,144) x y := by
  classical

  let E := sequence D .sphere
  have h356 : HasDifferential E 5 (15,140) (20,144)
      (I.realization.basis .sphere 15 140 2) (I.realization.basis .sphere 20 144 0) := stem125_af15_nonzero_d5_h356 I
  refine ⟨I.realization.basis .sphere 15 140 2,I.realization.basis .sphere 20 144 0,?_,?_,?_⟩
  · have h : Raw.coordinatesValid Raw.degrees .sphere 15 140 [2] = true := rfl
    simp only [Realization.decode,h,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  · have h : Raw.coordinatesValid Raw.degrees .sphere 20 144 [0] = true := rfl
    simp only [Realization.decode,h,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  · obtain ⟨hp,xr,yr,hxr,hyr,hd⟩ := h356
    exact ⟨hp,xr,yr,hxr,hyr,hd,af15_d5_target_nonzero I yr hyr⟩
end

section
open CategoryTheory.Limits KIP126.Core.Algebra KIP126.Computation.Near126 in
/-- The AF18 target is NONZERO on E5: S0_ss3083/3391 give
d5(h1*x125,12,2)=d0^2*x97,10. It disappears on E6. Its synthetic lifts
require a separate torsion and higher-filtration argument at weight130;
they cannot be discarded by declaring the classical E5 component zero. -/
private theorem af15_three_for_incoming_h359 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (13,140) (15,141)
    ((I.realization.basis .sphere 13 140 4)) ((I.realization.basis .sphere 15 141 1)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,13,140,[4],15,141,[1],"S0_AdamsE2_ss",3257⟩ (by
    exact List.mem_of_getElem? (i := 359) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (13,140) (15,141) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 140 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 141 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af15_three_for_incoming_h360 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (15,141) (17,142)
    ((I.realization.basis .sphere 15 141 0)) ((I.realization.basis .sphere 17 142 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,15,141,[0],17,142,[0],"S0_AdamsE2_ss",3258⟩ (by
    exact List.mem_of_getElem? (i := 360) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (15,141) (17,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 141 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 142 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af15_three_for_incoming (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 3 (15,141)) := by
  classical
  let E := sequence D .sphere
  have h359 : HasDifferential E 2 (13,140) (15,141)
      ((I.realization.basis .sphere 13 140 4)) ((I.realization.basis .sphere 15 141 1)) := af15_three_for_incoming_h359 I
  have h360 : HasDifferential E 2 (15,141) (17,142)
      ((I.realization.basis .sphere 15 141 0)) ((I.realization.basis .sphere 17 142 0)) := af15_three_for_incoming_h360 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,15,141,["0,1,68,1,107,1", "0,13,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 225) (by rfl))
  change E.Page 2 (15,141) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 15 141 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,17,142,["0,2,67,1,107,1", "0,3,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 240) (by rfl))
  change E.Page 2 (17,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 17 142 i.val at hf
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 15 141 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 15 141 1 := he 1
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 17 142 0 := hf 0
  have hd0 : E.d 2 (15,141) (I.realization.basis .sphere 15 141 0) =
      I.realization.basis .sphere 17 142 0 := h360.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 3 (15,141) (I.realization.basis .sphere 15 141 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h359
  have hd1 : E.d 2 (15,141) (I.realization.basis .sphere 15 141 1)=0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h359
    have hd' : E.d 2 (13,140) x=y := hd
    have heq := hy.eq_on_page_two
    rw [heq]
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(13,140)) ⟨x,hd'⟩
  apply third_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (15,141)
  intro x hx
  have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) := by
    ext i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,zero_add] at hxe
    rw [hxe]
    exact RepresentsOnPage.zero (by decide)
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,he1] at hxe
    rw [hxe]
    exact hz1
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero,he0] at hxe
    rw [hxe,hd0] at hx
    have hh := congrArg (fun y => f y 0) hx
    rw [←hf0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    rw [map_add,he0,he1] at hxe
    rw [hxe,map_add,hd0,hd1,add_zero] at hx
    have hh := congrArg (fun y => f y 0) hx
    rw [←hf0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh


private theorem af14_d4_zero_for_incoming_h344 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,139) (14,140)
    ((I.realization.basis .sphere 12 139 2)) ((I.realization.basis .sphere 14 140 3)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,12,139,[2],14,140,[3],"S0_AdamsE2_ss",3155⟩ (by
    exact List.mem_of_getElem? (i := 344) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,139) (14,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 139 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 140 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af14_d4_zero_for_incoming_h345 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (10,137) (14,140)
    ((I.realization.basis .sphere 10 137 4)) ((I.realization.basis .sphere 14 140 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,10,137,[4],14,140,[0],"S0_AdamsE2_ss",3156⟩ (by
    exact List.mem_of_getElem? (i := 345) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (10,137) (14,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 140 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af14_d4_zero_for_incoming_h346 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 5 (9,136) (14,140)
    ((I.realization.basis .sphere 9 136 0)) ((I.realization.basis .sphere 14 140 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,5,9,136,[0],14,140,[2],"S0_AdamsE2_ss",3157⟩ (by
    exact List.mem_of_getElem? (i := 346) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (9,136) (14,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 140 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af14_d4_zero_for_incoming_h347 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,140) (16,141)
    ((I.realization.basis .sphere 14 140 1)) ((I.realization.basis .sphere 16 141 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,14,140,[1],16,141,[2],"S0_AdamsE2_ss",3158⟩ (by
    exact List.mem_of_getElem? (i := 347) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,140) (16,141) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 140 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af14_d4_zero_for_incoming (I : Inputs D L G) :
    (sequence D .sphere).d 4 (14,140) = 0 := by
  classical
  let E := sequence D .sphere
  have h344 : HasDifferential E 2 (12,139) (14,140)
      ((I.realization.basis .sphere 12 139 2)) ((I.realization.basis .sphere 14 140 3)) := af14_d4_zero_for_incoming_h344 I
  have h345 : HasDifferential E 4 (10,137) (14,140)
      ((I.realization.basis .sphere 10 137 4)) ((I.realization.basis .sphere 14 140 0)) := af14_d4_zero_for_incoming_h345 I
  have h346 : HasDifferential E 5 (9,136) (14,140)
      ((I.realization.basis .sphere 9 136 0)) ((I.realization.basis .sphere 14 140 2)) := af14_d4_zero_for_incoming_h346 I
  have h347 : HasDifferential E 2 (14,140) (16,141)
      ((I.realization.basis .sphere 14 140 1)) ((I.realization.basis .sphere 16 141 2)) := af14_d4_zero_for_incoming_h347 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,14,140,["457,1", "68,1,107,1", "1,1,3,1,335,1", "0,12,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 218) (by rfl))
  change E.Page 2 (14,140) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 140 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,16,141,["473,1", "1,1,448,1", "0,1,67,1,107,1", "0,2,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 232) (by rfl))
  change E.Page 2 (16,141) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 141 i.val at hf
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.realization.basis .sphere 14 140 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.realization.basis .sphere 14 140 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.realization.basis .sphere 14 140 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.realization.basis .sphere 14 140 3 := he 3
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = I.realization.basis .sphere 16 141 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = I.realization.basis .sphere 16 141 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = I.realization.basis .sphere 16 141 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = I.realization.basis .sphere 16 141 3 := hf 3
  obtain ⟨_,u0,v0,hu0,hv0,hd0'⟩ := h345
  have hd0'': E.d 4 (10,137) u0=v0 := hd0'
  have hv0d : E.d 4 (14,140) v0=0 := IsPageBoundary.d_eq_zero (E:=E) (r:=4) (p:=(10,137)) ⟨u0,hd0''⟩
  obtain ⟨_,u2,v2,hu2,hv2,hd2'⟩ := h346
  obtain ⟨v24,hv24⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hv2
  have hv24d : E.d 4 (14,140) v24=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤4; omega) (by decide) hv24 ⟨v2,hv2⟩
  have hz3 : RepresentsOnPage E 4 (14,140) (I.realization.basis .sphere 14 140 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h344
  have hd0 : E.d 2 (14,140) (I.realization.basis .sphere 14 140 0)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hv0
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨v0,hv0⟩
  have hd2 : E.d 2 (14,140) (I.realization.basis .sphere 14 140 2)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hv2
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨v2,hv2⟩
  have hd3 : E.d 2 (14,140) (I.realization.basis .sphere 14 140 3)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hz3
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz3⟩
  have hd1 : E.d 2 (14,140) (I.realization.basis .sphere 14 140 1) =
      I.realization.basis .sphere 16 141 2 := h347.eq_on_page_two.2
  apply fourth_d_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (14,140)
  intro x hx
  have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) := by
    ext i
    fin_cases i <;> simp [Finsupp.single_apply]
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe]
    exact ⟨0,RepresentsOnPage.zero (by decide),map_zero _⟩
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe]
    exact ⟨0,hz3,map_zero _⟩
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe]
    exact ⟨v24,hv24,hv24d⟩
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe]
    exact ⟨v24 + 0,(represents_add_tail hv24 hz3),by simp only [map_add,hv24d,map_zero,add_zero]⟩
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe]
    exact ⟨v0,hv0,hv0d⟩
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe]
    exact ⟨v0 + 0,(represents_add_tail hv0 hz3),by simp only [map_add,hv0d,map_zero,add_zero]⟩
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe]
    exact ⟨v0 + v24,(represents_add_tail hv0 hv24),by simp only [map_add,hv0d, hv24d,map_zero,add_zero]⟩
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe]
    exact ⟨v0 + v24 + 0,(represents_add_tail (represents_add_tail hv0 hv24) hz3),by simp only [map_add,hv0d, hv24d,map_zero,add_zero]⟩
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero,he0,he1,he2,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh


private theorem af18_d5_target_nonzero_h373 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,141) (16,142)
    ((I.realization.basis .sphere 14 141 2)) ((I.realization.basis .sphere 16 142 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,14,141,[2],16,142,[2],"S0_AdamsE2_ss",3321⟩ (by
    exact List.mem_of_getElem? (i := 373) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,141) (16,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 141 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 142 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af18_d5_target_nonzero_h374 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (13,140) (16,142)
    ((I.realization.basis .sphere 13 140 0)) ((I.realization.basis .sphere 16 142 1)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,13,140,[0],16,142,[1],"S0_AdamsE2_ss",3322⟩ (by
    exact List.mem_of_getElem? (i := 374) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,140) (16,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 140 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 142 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af18_d5_target_nonzero_h375 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 6 (10,137) (16,142)
    ((I.realization.basis .sphere 10 137 2) + (I.realization.basis .sphere 10 137 4)) ((I.realization.basis .sphere 16 142 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,6,10,137,[2, 4],16,142,[0],"S0_AdamsE2_ss",3323⟩ (by
    exact List.mem_of_getElem? (i := 375) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 6 (10,137) (16,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [2, 4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 142 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af18_d5_target_nonzero (I : Inputs D L G)
    (y : (sequence D .sphere).Page 5 (18,143))
    (hy : RepresentsOnPage (sequence D .sphere) 5 (18,143)
      (I.realization.basis .sphere 18 143 0) y) : y ≠ 0 := by
  classical
  let E := sequence D .sphere
  have h373 : HasDifferential E 2 (14,141) (16,142)
      ((I.realization.basis .sphere 14 141 2)) ((I.realization.basis .sphere 16 142 2)) := af18_d5_target_nonzero_h373 I
  have h374 : HasDifferential E 3 (13,140) (16,142)
      ((I.realization.basis .sphere 13 140 0)) ((I.realization.basis .sphere 16 142 1)) := af18_d5_target_nonzero_h374 I
  have h375 : HasDifferential E 6 (10,137) (16,142)
      ((I.realization.basis .sphere 10 137 2) + (I.realization.basis .sphere 10 137 4)) ((I.realization.basis .sphere 16 142 0)) := af18_d5_target_nonzero_h375 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,16,142,["1,2,439,1", "0,2,68,1,107,1", "0,14,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 233) (by rfl))
  change E.Page 2 (16,142) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 142 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,18,143,["8,2,209,1", "0,4,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 246) (by rfl))
  change E.Page 2 (18,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 18 143 i.val at hf
  have hd0 : E.d 2 (16,142) (I.realization.basis .sphere 16 142 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h375
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hy
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hy⟩
  have hd1 : E.d 2 (16,142) (I.realization.basis .sphere 16 142 1) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h374
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hy
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hy⟩
  have hd2 : E.d 2 (16,142) (I.realization.basis .sphere 16 142 2)=0 := by
    have hd : E.d 2 (14,141) (I.realization.basis .sphere 14 141 2)=
      I.realization.basis .sphere 16 142 2 := h373.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(14,141)) ⟨_,hd⟩
  have in2 : E.d 2 ((18,143)-E.diffDeg 2)=0 := by
    have hall (a : Fin 3 →₀ F2) : E.d 2 (16,142) (e.symm a)=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,ih,add_zero]
        fin_cases c
        · simp
        · change E.d 2 (16,142) (e.symm (Finsupp.single i 1))=0
          rw [he i]
          fin_cases i
          · exact hd0
          · exact hd1
          · exact hd2
    ext x
    change E.d 2 (16,142) x=0
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)
  have in3 : E.d 3 ((18,143)-E.diffDeg 3)=0 := by
    ext x
    change E.d 3 (15,141) x=0
    rw [(af15_three_for_incoming I).elim x 0,map_zero]
  have in4 : E.d 4 ((18,143)-E.diffDeg 4)=0 := af14_d4_zero_for_incoming I
  have n2 : I.realization.basis .sphere 18 143 0 ≠ 0 := by
    have hh : f.symm (Finsupp.single (0:Fin 2) 1)=I.realization.basis .sphere 18 143 0 := hf 0
    rw [←hh]
    intro hz
    have hh := congrArg (fun x => f x 0) hz
    norm_num [Finsupp.single_apply] at hh
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) hy
  obtain ⟨y4,hy4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy
  have hy2 : RepresentsOnPage E 2 (18,143) (I.realization.basis .sphere 18 143 0) (I.realization.basis .sphere 18 143 0) := by
    obtain ⟨y2,hy2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hy
    rw [←hy2.eq_on_page_two] at hy2
    exact hy2
  have n3 := represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)≤2) in2 hy3 hy2 n2
  have n4 := represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤3; omega)
    (by decide : (2:ℤ)≤3) in3 hy4 hy3 n3
  exact represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤4; omega)
    (by decide : (2:ℤ)≤4) in4 hy hy4 n4

private theorem stem125_af18_nonzero_incoming_d5_h397 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 5 (13,139) (18,143)
    ((I.realization.basis .sphere 13 139 0)) ((I.realization.basis .sphere 18 143 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,5,13,139,[0],18,143,[0],"S0_AdamsE2_ss",3391⟩ (by
    exact List.mem_of_getElem? (i := 397) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (13,139) (18,143) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 139 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 143 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

theorem stem125_af18_nonzero_incoming_d5 (I : Inputs D L G) :
    ∃ (x : Page D .sphere 13 139) (y : Page D .sphere 18 143),
      I.realization.decode .sphere 13 139 [0] = some x ∧
      I.realization.decode .sphere 18 143 [0] = some y ∧
      HasNonzeroDifferential (sequence D .sphere) 5 (13,139) (18,143) x y := by
  classical

  let E := sequence D .sphere
  have h397 : HasDifferential E 5 (13,139) (18,143)
      ((I.realization.basis .sphere 13 139 0)) ((I.realization.basis .sphere 18 143 0)) := stem125_af18_nonzero_incoming_d5_h397 I
  refine ⟨I.realization.basis .sphere 13 139 0,I.realization.basis .sphere 18 143 0,?_,?_,?_⟩
  · have vx : Raw.coordinatesValid Raw.degrees .sphere 13 139 [0]=true := rfl
    simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  · have vy : Raw.coordinatesValid Raw.degrees .sphere 18 143 [0]=true := rfl
    simp only [Realization.decode,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  · obtain ⟨hp,xr,yr,hx,hy,hd⟩ := h397
    refine ⟨hp,xr,yr,hx,hy,hd,?_⟩
    exact af18_d5_target_nonzero I yr hy
end

section SphereFactsProof
open CategoryTheory.Limits KIP126.Core.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

private theorem vx_empty_page (I : Inputs D L G) (s t : ℕ)
    (h : (⟨.sphere,s,t,[]⟩ : Raw.Degree) ∈ Raw.degrees) (r : ℤ) (hr : 2≤r) :
    Subsingleton ((sequence D .sphere).Page r (s,t)) := by
  classical
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,s,t,[]⟩ h
  change (sequence D .sphere).Page 2 (s,t) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  have hzero : Subsingleton ((sequence D .sphere).Page 2 (s,t)) := e.injective.subsingleton
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r s t
    (by decide) hr hzero


private theorem v_incoming2_zero_h163 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (5,130) (7,131)
    ((I.realization.basis .sphere 5 130 0)) ((I.realization.basis .sphere 7 131 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,5,130,[0],7,131,[2],"S0_AdamsE2_ss",2435⟩ (by
    exact List.mem_of_getElem? (i := 163) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,130) (7,131) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem v_incoming2_zero_h182 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 5 (7,131) (12,135)
    ((I.realization.basis .sphere 7 131 1)) ((I.realization.basis .sphere 12 135 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,5,7,131,[1],12,135,[2],"S0_AdamsE2_ss",2490⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (7,131) (12,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem v_incoming2_zero_h183 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (7,131) (10,133)
    ((I.realization.basis .sphere 7 131 0)) ((I.realization.basis .sphere 10 133 0) + (I.realization.basis .sphere 10 133 1)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,7,131,[0],10,133,[0, 1],"S0_AdamsE2_ss",2491⟩ (by
    exact List.mem_of_getElem? (i := 183) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (7,131) (10,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0, 1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem v_incoming2_zero (I : Inputs D L G) :
    (sequence D .sphere).d 2 (7,131)=0 := by
  classical
  let E := sequence D .sphere
  have h163 : HasDifferential E 2 (5,130) (7,131)
      ((I.realization.basis .sphere 5 130 0)) ((I.realization.basis .sphere 7 131 2)) := v_incoming2_zero_h163 I
  have h182 : HasDifferential E 5 (7,131) (12,135)
      ((I.realization.basis .sphere 7 131 1)) ((I.realization.basis .sphere 12 135 2)) := v_incoming2_zero_h182 I
  have h183 : HasDifferential E 3 (7,131) (10,133)
      ((I.realization.basis .sphere 7 131 0)) ((I.realization.basis .sphere 10 133 0) + (I.realization.basis .sphere 10 133 1)) := v_incoming2_zero_h183 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,7,131,["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 131 i.val at he
  have d0 : E.d 2 (7,131) (I.realization.basis .sphere 7 131 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h183
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d1 : E.d 2 (7,131) (I.realization.basis .sphere 7 131 1) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h182
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d2 : E.d 2 (7,131) (I.realization.basis .sphere 7 131 2)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(5,130)) ⟨_,h163.eq_on_page_two.2⟩
  have hall (a : Fin 3 →₀ F2) : E.d 2 (7,131) (e.symm a)=0 := by
    induction a using Finsupp.induction with
    | zero => simp
    | @single_add i c a hi hc ih =>
      rw [map_add,map_add,ih,add_zero]
      fin_cases c
      · simp
      · change E.d 2 (7,131) (e.symm (Finsupp.single i 1))=0
        rw [he i]
        fin_cases i
        · exact d0
        · exact d1
        · exact d2
  ext x
  change E.d 2 (7,131) x=0
  simpa only [LinearEquiv.symm_apply_apply] using hall (e x)


private theorem v_incoming3_zero_h170 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 5 (6,130) (11,134)
    ((I.realization.basis .sphere 6 130 0)) ((I.realization.basis .sphere 11 134 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,5,6,130,[0],11,134,[2],"S0_AdamsE2_ss",2434⟩ (by
    exact List.mem_of_getElem? (i := 170) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (6,130) (11,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 134 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem v_incoming3_zero (I : Inputs D L G) :
    (sequence D .sphere).d 3 (6,130)=0 := by
  classical
  let E := sequence D .sphere
  have h170 : HasDifferential E 5 (6,130) (11,134)
      ((I.realization.basis .sphere 6 130 0)) ((I.realization.basis .sphere 11 134 2)) := v_incoming3_zero_h170 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,6,130,["339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 136) (by rfl))
  change E.Page 2 (6,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 6 130 i.val at he
  obtain ⟨_,aLate,_,haLate,_,_⟩ := h170
  obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) haLate
  have da : E.d 3 (6,130) a=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) ha ⟨aLate,haLate⟩
  ext z
  change E.d 3 (6,130) z=0
  let vv : Fin 1 → E.Page 3 (6,130) := fun _ => a
  have hv (i : Fin 1) : RepresentsOnPage E 3 (6,130) (e.symm (Finsupp.single i 1)) (vv i) := by
    rw [he i]
    fin_cases i
    exact ha
  obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e vv hv z
  simp only [Fin.sum_univ_succ] at hc
  change z=(if c 0=0 then 0 else a)+0 at hc
  rw [hc]
  by_cases h0 : c 0=0
  all_goals simp only [h0,ite_true,ite_false,map_zero,da,add_zero]


private theorem v_incoming_zero (I : Inputs D L G) (r : ℤ) (hr : 2≤r) :
    (sequence D .sphere).d r ((9,132)-(sequence D .sphere).diffDeg r)=0 := by
  classical
  let E := sequence D .sphere
  by_cases hlate : 9<r
  · haveI : Subsingleton (E.Page r (9-r,132-(r-1))) :=
      adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r (9-r) (132-(r-1)) (by omega)
    change E.d r (9-r,132-(r-1))=0
    ext z
    rw [Subsingleton.elim z 0,map_zero]
    rfl
  · have hrhi : r≤9 := by omega
    interval_cases r
    · exact v_incoming2_zero I
    · exact v_incoming3_zero I
    · haveI : Subsingleton (E.Page 4 (5,129)) := vx_empty_page I 5 129 (by
        exact List.mem_of_getElem? (i := 125) (by rfl)) 4 (by decide)
      change E.d 4 (5,129)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 5 (4,128)) := vx_empty_page I 4 128 (by
        exact List.mem_of_getElem? (i := 117) (by rfl)) 5 (by decide)
      change E.d 5 (4,128)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 6 (3,127)) := vx_empty_page I 3 127 (by
        exact List.mem_of_getElem? (i := 106) (by rfl)) 6 (by decide)
      change E.d 6 (3,127)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 7 (2,126)) := vx_empty_page I 2 126 (by
        exact List.mem_of_getElem? (i := 98) (by rfl)) 7 (by decide)
      change E.d 7 (2,126)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 8 (1,125)) := vx_empty_page I 1 125 (by
        exact List.mem_of_getElem? (i := 88) (by rfl)) 8 (by decide)
      change E.d 8 (1,125)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 9 (0,124)) := vx_empty_page I 0 124 (by
        exact List.mem_of_getElem? (i := 75) (by rfl)) 9 (by decide)
      change E.d 9 (0,124)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl


private theorem v_never_hit (I : Inputs D L G) :
    NeverHit (sequence D .sphere) (9,132) (I.realization.sphere 9 132 KIP126.Computation.Near126.V) := by
  classical
  let E := sequence D .sphere
  intro r hr q h y hy hyn z hd
  have hq : q=(9,132)-E.diffDeg r := eq_sub_iff_add_eq.mpr h
  subst q
  have heq : (E.d r ((9,132)-E.diffDeg r) ≫ eqToHom (congrArg (E.Page r) h)) z=0 := by
    rw [v_incoming_zero I r hr]
    simp only [zero_comp]
    rfl
  exact hyn (hd.symm.trans heq)


private theorem x_incoming_zero (I : Inputs D L G) (r : ℤ) (hr : 2≤r) :
    (sequence D .sphere).d r ((8,130)-(sequence D .sphere).diffDeg r)=0 := by
  classical
  let E := sequence D .sphere
  by_cases hlate : 8<r
  · haveI : Subsingleton (E.Page r (8-r,130-(r-1))) :=
      adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r (8-r) (130-(r-1)) (by omega)
    change E.d r (8-r,130-(r-1))=0
    ext z
    rw [Subsingleton.elim z 0,map_zero]
    rfl
  · have hrhi : r≤8 := by omega
    interval_cases r
    · haveI : Subsingleton (E.Page 2 (6,129)) := vx_empty_page I 6 129 (by
        exact List.mem_of_getElem? (i := 135) (by rfl)) 2 (by decide)
      change E.d 2 (6,129)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 3 (5,128)) := vx_empty_page I 5 128 (by
        exact List.mem_of_getElem? (i := 124) (by rfl)) 3 (by decide)
      change E.d 3 (5,128)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 4 (4,127)) := vx_empty_page I 4 127 (by
        exact List.mem_of_getElem? (i := 116) (by rfl)) 4 (by decide)
      change E.d 4 (4,127)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 5 (3,126)) := vx_empty_page I 3 126 (by
        exact List.mem_of_getElem? (i := 105) (by rfl)) 5 (by decide)
      change E.d 5 (3,126)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 6 (2,125)) := vx_empty_page I 2 125 (by
        exact List.mem_of_getElem? (i := 97) (by rfl)) 6 (by decide)
      change E.d 6 (2,125)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 7 (1,124)) := vx_empty_page I 1 124 (by
        exact List.mem_of_getElem? (i := 87) (by rfl)) 7 (by decide)
      change E.d 7 (1,124)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 8 (0,123)) := vx_empty_page I 0 123 (by
        exact List.mem_of_getElem? (i := 74) (by rfl)) 8 (by decide)
      change E.d 8 (0,123)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl


private theorem x_never_hit (I : Inputs D L G) :
    NeverHit (sequence D .sphere) (8,130) (I.realization.sphere 8 130 X) := by
  classical
  let E := sequence D .sphere
  intro r hr q h y hy hyn z hd
  have hq : q=(8,130)-E.diffDeg r := eq_sub_iff_add_eq.mpr h
  subst q
  have heq : (E.d r ((8,130)-E.diffDeg r) ≫ eqToHom (congrArg (E.Page r) h)) z=0 := by
    rw [x_incoming_zero I r hr]
    simp only [zero_comp]
    rfl
  exact hyn (hd.symm.trans heq)


private theorem vx_v_first (I : Inputs D L G) :
    I.realization.sphere 9 132 (atom .x_123_9) = I.realization.basis .sphere 9 132 0 := by
  classical
  have hc := I.csv (⟨.sphere,9,132,["366,1", "0,1,352,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 171) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0:Fin 2)
  have heq : (atom .x_123_9)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨366,by decide⟩ = projection (monomialOfString "366,1")
    have hs : "366,1" ≠ "" := by decide
    have hp : (("366,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [366, 1] := by
      have split : "366,1".splitOn "," = ["366", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem vx_v_second (I : Inputs D L G) :
    I.realization.sphere 9 132 (mulAt dataH0 (atom .x_123_8)) = I.realization.basis .sphere 9 132 1 := by
  classical
  have hc := I.csv (⟨.sphere,9,132,["366,1", "0,1,352,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 171) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (1:Fin 2)
  have heq : (mulAt dataH0 (atom .x_123_8))=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨0,by decide⟩ * generator ⟨352,by decide⟩ = projection (monomialOfString "0,1,352,1")
    have hs : "0,1,352,1" ≠ "" := by decide
    have hp : (("0,1,352,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 1, 352, 1] := by
      have split : "0,1,352,1".splitOn "," = ["0", "1", "352", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem vx_x_label (I : Inputs D L G) :
    I.realization.sphere 8 130 (X) = I.realization.basis .sphere 8 130 0 := by
  classical
  have hc := I.csv (⟨.sphere,8,130,["1,1,323,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 158) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
  have heq : (X)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨1,by decide⟩ * generator ⟨323,by decide⟩ = projection (monomialOfString "1,1,323,1")
    have hs : "1,1,323,1" ≠ "" := by decide
    have hp : (("1,1,323,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1, 1, 323, 1] := by
      have split : "1,1,323,1".splitOn "," = ["1", "1", "323", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem v_survives (I : Inputs D L G) :
    SurvivesTo (sequence D .sphere) 12 (9,132) (I.realization.sphere 9 132 KIP126.Computation.Near126.V) := by
  classical
  let E := sequence D .sphere
  have hreach : ReachesPage E 12 (9,132) (I.realization.basis .sphere 9 132 0 + I.realization.basis .sphere 9 132 1) := by
    have hh := I.results ⟨.sphere,.reaches,12,9,132,[0, 1],9,132,[],"S0_AdamsE2_ss",2569⟩ (by
      exact List.mem_of_getElem? (i := 219) (by rfl))
    dsimp only [Statement] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0, 1]=true := rfl
    simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hh
    exact hh
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,132,["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 132 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1)=I.realization.basis .sphere 9 132 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1)=I.realization.basis .sphere 9 132 1 := he 1
  have hn : (I.realization.basis .sphere 9 132 0 + I.realization.basis .sphere 9 132 1)≠0 := by
    intro hh
    have hc := congrArg (fun y => e y 0) hh
    simp only [map_add,map_zero,←he0,←he1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hc
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hc
  have hlabel : I.realization.sphere 9 132 KIP126.Computation.Near126.V=I.realization.basis .sphere 9 132 0+I.realization.basis .sphere 9 132 1 := by
    change I.realization.sphere 9 132 (atom .x_123_9+mulAt dataH0 (atom .x_123_8))=_
    rw [map_add,vx_v_first I,vx_v_second I]
  rw [hlabel]
  obtain ⟨y,hy⟩ := hreach
  exact ⟨y,hy,vx_nonzero_no_incoming (by change (2:ℤ)≤2; omega) (v_incoming_zero I) hy hn⟩


private theorem x_survives (I : Inputs D L G) :
    SurvivesTo (sequence D .sphere) 6 (8,130) (I.realization.sphere 8 130 X) := by
  classical
  let E := sequence D .sphere
  have hreach : ReachesPage E 6 (8,130) (I.realization.basis .sphere 8 130 0) := by
    have hh := I.results ⟨.sphere,.reaches,6,8,130,[0],8,130,[],"S0_AdamsE2_ss",2433⟩ (by
      exact List.mem_of_getElem? (i := 197) (by rfl))
    dsimp only [Statement] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 130 [0]=true := rfl
    simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hh
    exact hh
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,8,130,["1,1,323,1"]⟩ (by
    exact List.mem_of_getElem? (i := 158) (by rfl))
  change E.Page 2 (8,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 8 130 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1)=I.realization.basis .sphere 8 130 0 := he 0
  have hn : (I.realization.basis .sphere 8 130 0)≠0 := by
    intro hh
    have hc := congrArg (fun y => e y 0) hh
    simp only [map_add,map_zero,←he0,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hc
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hc
  rw [vx_x_label I]
  obtain ⟨y,hy⟩ := hreach
  exact ⟨y,hy,vx_nonzero_no_incoming (by change (2:ℤ)≤2; omega) (x_incoming_zero I) hy hn⟩


private theorem y_incoming2_zero_h190 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
    ((I.realization.basis .sphere 7 134 1)) ((I.realization.basis .sphere 9 135 4)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,7,134,[1],9,135,[4],"S0_AdamsE2_ss",2709⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,134) (9,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero_h191 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
    ((I.realization.basis .sphere 7 134 4)) ((I.realization.basis .sphere 9 135 5)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,7,134,[4],9,135,[5],"S0_AdamsE2_ss",2710⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,134) (9,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [5] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero_h231 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    ((I.realization.basis .sphere 9 135 2)) ((I.realization.basis .sphere 13 138 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
    exact List.mem_of_getElem? (i := 231) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero_h232 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    ((I.realization.basis .sphere 9 135 1)) ((I.realization.basis .sphere 13 138 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
    exact List.mem_of_getElem? (i := 232) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero_h233 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    ((I.realization.basis .sphere 9 135 0)) ((I.realization.basis .sphere 12 137 3) + (I.realization.basis .sphere 12 137 4)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,135,[0],12,137,[3, 4],"S0_AdamsE2_ss",2792⟩ (by
    exact List.mem_of_getElem? (i := 233) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero_h234 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    ((I.realization.basis .sphere 9 135 3)) ((I.realization.basis .sphere 12 137 3)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,135,[3],12,137,[3],"S0_AdamsE2_ss",2793⟩ (by
    exact List.mem_of_getElem? (i := 234) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero (I : Inputs D L G) : (sequence D .sphere).d 2 (9,135)=0 := by
  classical
  let E := sequence D .sphere
  have h190 : HasDifferential E 2 (7,134) (9,135)
      ((I.realization.basis .sphere 7 134 1)) ((I.realization.basis .sphere 9 135 4)) := y_incoming2_zero_h190 I
  have h191 : HasDifferential E 2 (7,134) (9,135)
      ((I.realization.basis .sphere 7 134 4)) ((I.realization.basis .sphere 9 135 5)) := y_incoming2_zero_h191 I
  have h231 : HasDifferential E 4 (9,135) (13,138)
      ((I.realization.basis .sphere 9 135 2)) ((I.realization.basis .sphere 13 138 0)) := y_incoming2_zero_h231 I
  have h232 : HasDifferential E 4 (9,135) (13,138)
      ((I.realization.basis .sphere 9 135 1)) ((I.realization.basis .sphere 13 138 2)) := y_incoming2_zero_h232 I
  have h233 : HasDifferential E 3 (9,135) (12,137)
      ((I.realization.basis .sphere 9 135 0)) ((I.realization.basis .sphere 12 137 3) + (I.realization.basis .sphere 12 137 4)) := y_incoming2_zero_h233 I
  have h234 : HasDifferential E 3 (9,135) (12,137)
      ((I.realization.basis .sphere 9 135 3)) ((I.realization.basis .sphere 12 137 3)) := y_incoming2_zero_h234 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,135,["414,1", "1,1,376,1", "1,1,375,1", "0,1,394,1", "0,1,392,1", "0,7,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 174) (by rfl))
  change E.Page 2 (9,135) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 135 i.val at he
  have d0 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h233
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d1 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 1) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h232
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d2 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 2) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h231
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d3 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 3) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h234
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d4 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 4)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(7,134)) ⟨_,h190.eq_on_page_two.2⟩
  have d5 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 5)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(7,134)) ⟨_,h191.eq_on_page_two.2⟩
  have hall (a : Fin 6 →₀ F2) : E.d 2 (9,135) (e.symm a)=0 := by
    induction a using Finsupp.induction with
    | zero => simp
    | @single_add i c a hi hc ih =>
      rw [map_add,map_add,ih,add_zero]
      fin_cases c
      · simp
      · change E.d 2 (9,135) (e.symm (Finsupp.single i 1))=0
        rw [he i]
        fin_cases i
        · exact d0
        · exact d1
        · exact d2
        · exact d3
        · exact d4
        · exact d5
  ext x
  change E.d 2 (9,135) x=0
  simpa only [LinearEquiv.symm_apply_apply] using hall (e x)


private theorem y_incoming4_zero_h185 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (5,132) (7,133)
    ((I.realization.basis .sphere 5 132 0)) ((I.realization.basis .sphere 7 133 1)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,5,132,[0],7,133,[1],"S0_AdamsE2_ss",2631⟩ (by
    exact List.mem_of_getElem? (i := 185) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,132) (7,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 133 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming4_zero_h186 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 18 (7,133) (I.realization.basis .sphere 7 133 0) := by
  classical
  have hh := I.results ⟨.sphere,.reaches,18,7,133,[0],7,133,[],"S0_AdamsE2_ss",2632⟩ (by
    exact List.mem_of_getElem? (i := 186) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 133 [0]=true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem y_incoming4_zero (I : Inputs D L G) : (sequence D .sphere).d 4 (7,133)=0 := by
  classical
  let E := sequence D .sphere
  have h185 : HasDifferential E 2 (5,132) (7,133)
      ((I.realization.basis .sphere 5 132 0)) ((I.realization.basis .sphere 7 133 1)) := y_incoming4_zero_h185 I
  have h186 : ReachesPage E 18 (7,133) (I.realization.basis .sphere 7 133 0) := y_incoming4_zero_h186 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,7,133,["1,1,69,1,76,1", "0,5,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 150) (by rfl))
  change E.Page 2 (7,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 133 i.val at he
  obtain ⟨aLate,haLate⟩ := h186
  obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤18) haLate
  have da : E.d 4 (7,133) a=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<18) ha ⟨aLate,haLate⟩
  have hb : RepresentsOnPage E 4 (7,133) (I.realization.basis .sphere 7 133 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h185
  ext z
  change E.d 4 (7,133) z=0
  let vv : Fin 2 → E.Page 4 (7,133) := ![a,0]
  have hv (i : Fin 2) : RepresentsOnPage E 4 (7,133) (e.symm (Finsupp.single i 1)) (vv i) := by
    rw [he i]
    fin_cases i
    · exact ha
    · exact hb
  obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤4) e vv hv z
  simp only [Fin.sum_univ_succ] at hc
  change z=(if c 0=0 then 0 else a)+((if c 1=0 then 0 else 0)+0) at hc
  simp only [ite_self,add_zero] at hc
  rw [hc]
  by_cases h0 : c 0=0
  all_goals simp only [h0,ite_true,ite_false,map_zero,da]


private theorem y_incoming3_represented_h279 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    ((I.realization.basis .sphere 8 134 3)) ((I.realization.basis .sphere 11 136 1)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2850⟩ (by
    exact List.mem_of_getElem? (i := 279) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming3_represented_h280 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    ((I.realization.basis .sphere 8 134 2)) ((I.realization.basis .sphere 11 136 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,8,134,[2],11,136,[2],"S0_AdamsE2_ss",2851⟩ (by
    exact List.mem_of_getElem? (i := 280) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming3_represented_h207 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,134) (10,135)
    ((I.realization.basis .sphere 8 134 1)) ((I.realization.basis .sphere 10 135 3)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2705⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,134) (10,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming3_represented_h202 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (6,133) (8,134)
    ((I.realization.basis .sphere 6 133 1)) ((I.realization.basis .sphere 8 134 5)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,6,133,[1],8,134,[5],"S0_AdamsE2_ss",2700⟩ (by
    exact List.mem_of_getElem? (i := 202) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (6,133) (8,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 8 134 [5] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming3_represented_h203 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 17 (8,134) (I.realization.basis .sphere 8 134 4) := by
  classical
  have hh := I.results ⟨.sphere,.reaches,17,8,134,[4],8,134,[],"S0_AdamsE2_ss",2701⟩ (by
    exact List.mem_of_getElem? (i := 203) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [4]=true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem y_incoming3_represented_h204 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 6 (8,134) (I.realization.basis .sphere 8 134 0 + I.realization.basis .sphere 8 134 3) := by
  classical
  have hh := I.results ⟨.sphere,.reaches,6,8,134,[0, 3],8,134,[],"S0_AdamsE2_ss",2702⟩ (by
    exact List.mem_of_getElem? (i := 204) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [0, 3]=true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem y_incoming3_represented (I : Inputs D L G) :
    ∀ z : (sequence D .sphere).Page 3 (8,134),
    ∃ x : (sequence D .sphere).Page 2 (11,136),
      RepresentsOnPage (sequence D .sphere) 3 (11,136) x ((sequence D .sphere).d 3 (8,134) z) ∧
      ∀ (e : (sequence D .sphere).Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2)),
      (∀ i : Fin 5, e.symm (Finsupp.single i 1)=I.realization.basis .sphere 11 136 i.val) → e x 3=0 := by
  classical
  let E := sequence D .sphere
  have h279 : HasDifferential E 3 (8,134) (11,136)
      ((I.realization.basis .sphere 8 134 3)) ((I.realization.basis .sphere 11 136 1)) := y_incoming3_represented_h279 I
  have h280 : HasDifferential E 3 (8,134) (11,136)
      ((I.realization.basis .sphere 8 134 2)) ((I.realization.basis .sphere 11 136 2)) := y_incoming3_represented_h280 I
  have h207 : HasDifferential E 2 (8,134) (10,135)
      ((I.realization.basis .sphere 8 134 1)) ((I.realization.basis .sphere 10 135 3)) := y_incoming3_represented_h207 I
  have h202 : HasDifferential E 2 (6,133) (8,134)
      ((I.realization.basis .sphere 6 133 1)) ((I.realization.basis .sphere 8 134 5)) := y_incoming3_represented_h202 I
  have h203 : ReachesPage E 17 (8,134) (I.realization.basis .sphere 8 134 4) := y_incoming3_represented_h203 I
  have h204 : ReachesPage E 6 (8,134) (I.realization.basis .sphere 8 134 0 + I.realization.basis .sphere 8 134 3) := y_incoming3_represented_h204 I
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,8,134,["395,1", "394,1", "393,1", "392,1", "69,1,85,1", "0,6,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 162) (by rfl))
  change E.Page 2 (8,134) ≃ₗ[ℤ] (Fin 6 →₀ F2) at f
  change ∀ i : Fin 6, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 8 134 i.val at hf
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 135 i.val at hk
  have hf0 : f.symm (Finsupp.single (0:Fin 6) 1)=I.realization.basis .sphere 8 134 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 6) 1)=I.realization.basis .sphere 8 134 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 6) 1)=I.realization.basis .sphere 8 134 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 6) 1)=I.realization.basis .sphere 8 134 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 6) 1)=I.realization.basis .sphere 8 134 4 := hf 4
  have hf5 : f.symm (Finsupp.single (5:Fin 6) 1)=I.realization.basis .sphere 8 134 5 := hf 5
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1)=I.realization.basis .sphere 10 135 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1)=I.realization.basis .sphere 10 135 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1)=I.realization.basis .sphere 10 135 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1)=I.realization.basis .sphere 10 135 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1)=I.realization.basis .sphere 10 135 4 := hk 4
  have hsub {r : ℤ} {p : ℤ×ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  obtain ⟨_,a3,t1,ha3,ht1,da3⟩ := h279
  obtain ⟨_,a2,t2,ha2,ht2,da2⟩ := h280
  have da3' : E.d 3 (8,134) a3=t1 := da3
  have da2' : E.d 3 (8,134) a2=t2 := da2
  obtain ⟨aSumLate,hSumLate⟩ := h204
  obtain ⟨aSum,hSum⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤6) hSumLate
  have dSum : E.d 3 (8,134) aSum=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hSum ⟨aSumLate,hSumLate⟩
  let a0 := aSum-a3
  have ha0 : RepresentsOnPage E 3 (8,134) (I.realization.basis .sphere 8 134 0) a0 := by
    simpa only [add_sub_cancel_right] using hsub hSum ha3
  have da0 : E.d 3 (8,134) a0= -t1 := by
    change E.d 3 (8,134) (aSum-a3)= -t1
    rw [map_sub,dSum,da3',zero_sub]
  obtain ⟨a4Late,ha4Late⟩ := h203
  obtain ⟨a4,ha4⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤17) ha4Late
  have da4 : E.d 3 (8,134) a4=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<17) ha4 ⟨a4Late,ha4Late⟩
  have ha5 : RepresentsOnPage E 3 (8,134) (I.realization.basis .sphere 8 134 5) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h202
  have d1 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 1)=I.realization.basis .sphere 10 135 3 := h207.eq_on_page_two.2
  have d0 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 0)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (middle_rep2 (by decide) ha0) ⟨_,ha0⟩
  have d2 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (middle_rep2 (by decide) ha2) ⟨_,ha2⟩
  have d3 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 3)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (middle_rep2 (by decide) ha3) ⟨_,ha3⟩
  have d4 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 4)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (middle_rep2 (by decide) ha4) ⟨_,ha4⟩
  have d5 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 5)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (middle_rep2 (by decide) ha5) ⟨_,ha5⟩
  intro z
  let A := E.ssData (8,134)
  haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨w,hw⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance z
  let x : E.Page 2 (8,134) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) w
  have hx : RepresentsOnPage E 3 (8,134) x z := ⟨by decide,w,rfl,hw⟩
  have dx : E.d 2 (8,134) x=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (middle_rep2 (by decide) hx) ⟨z,hx⟩
  let c : Fin 6 → F2 := f x
  have hcoef := congrArg f.symm (FinitePageCalculus.f2_expand (f x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
  change x=(if c 0=0 then 0 else f.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else f.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else f.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else f.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else f.symm (Finsupp.single 4 1)) + ((if c 5=0 then 0 else f.symm (Finsupp.single 5 1)) + 0))))) at hcoef
  simp only [hf0,hf1,hf2,hf3,hf4,hf5,add_zero] at hcoef
  have difif2 (c : F2) (a : E.Page 2 (8,134)) :
      E.d 2 (8,134) (if c=0 then 0 else a)=if c=0 then 0 else E.d 2 (8,134) a := by
    split_ifs <;> simp only [map_zero]
  have hd := congrArg (E.d 2 (8,134)) hcoef
  rw [dx] at hd
  simp only [map_add,difif2,d0,d1,d2,d3,d4,d5,ite_self,zero_add,add_zero] at hd
  have c1 : c 1=0 := by
    by_contra hc1
    simp only [hc1,ite_false] at hd
    have hh := congrArg (fun y=>k y 3) hd
    rw [←hk3,LinearEquiv.apply_symm_apply,map_zero] at hh
    norm_num [Finsupp.single_apply] at hh
  have hform : z=(if c 0=0 then 0 else a0)+((if c 2=0 then 0 else a2)+((if c 3=0 then 0 else a3)+(if c 4=0 then 0 else a4))) := by
    apply represents_unique hx
    rw [hcoef]
    simp only [c1,ite_true,zero_add]
    have hh := middle_add (middle_if (c 0) ha0) (middle_add (middle_if (c 2) ha2)
      (middle_add (middle_if (c 3) ha3) (middle_add (middle_if (c 4) ha4) (middle_if (c 5) ha5))))
    simpa only [ite_self,add_zero] using hh
  have difif3 (c : F2) (a : E.Page 3 (8,134)) :
      E.d 3 (8,134) (if c=0 then 0 else a)=if c=0 then 0 else E.d 3 (8,134) a := by
    split_ifs <;> simp only [map_zero]
  have hdform := congrArg (E.d 3 (8,134)) hform
  simp only [map_add,difif3,da0,da2',da3',da4,ite_self,add_zero] at hdform
  let out : E.Page 2 (11,136) := (if c 0=0 then 0 else -I.realization.basis .sphere 11 136 1)+
    ((if c 2=0 then 0 else I.realization.basis .sphere 11 136 2)+(if c 3=0 then 0 else I.realization.basis .sphere 11 136 1))
  have hn1 : RepresentsOnPage E 3 (11,136) (-I.realization.basis .sphere 11 136 1) (-t1) := by
    simpa only [zero_sub] using hsub (RepresentsOnPage.zero (by decide)) ht1
  refine ⟨out,?_,?_⟩
  · rw [hdform]
    exact middle_add (middle_if (c 0) hn1) (middle_add (middle_if (c 2) ht2) (middle_if (c 3) ht1))
  · intro e he
    have he1 : e.symm (Finsupp.single (1:Fin 5) 1)=I.realization.basis .sphere 11 136 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 5) 1)=I.realization.basis .sphere 11 136 2 := he 2
    by_cases h0 : c 0=0 <;> by_cases h2 : c 2=0 <;> by_cases h3 : c 3=0
    all_goals simp only [out,h0,h2,h3,ite_true,ite_false,map_add,map_neg,map_zero,←he1,←he2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply]
    all_goals norm_num [Finsupp.single_apply,Fin.ext_iff]


private theorem y_raw_survives_five_h281 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 5 (11,136) (I.realization.basis .sphere 11 136 3) := by
  classical
  have hh := I.results ⟨.sphere,.reaches,5,11,136,[3],11,136,[],"S0_AdamsE2_ss",2852⟩ (by
    exact List.mem_of_getElem? (i := 281) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [3]=true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem y_raw_survives_five (I : Inputs D L G) :
    SurvivesTo (sequence D .sphere) 5 (11,136) (I.realization.basis .sphere 11 136 3) := by
  classical
  let E := sequence D .sphere
  have h281 : ReachesPage E 5 (11,136) (I.realization.basis .sphere 11 136 3) := y_raw_survives_five_h281 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 192) (by rfl))
  change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 136 i.val at he
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1)=I.realization.basis .sphere 11 136 3 := he 3
  have hsub {r : ℤ} {p : ℤ×ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have nonzero3 {x : E.Page 2 (11,136)} {a : E.Page 3 (11,136)}
      (hx : e x 3=1) (ha : RepresentsOnPage E 3 (11,136) x a) : a≠0 := by
    have hn : x≠0 := by
      intro hh
      rw [hh,map_zero,Finsupp.zero_apply] at hx
      exact zero_ne_one hx
    exact represents_next_nonzero_of_incoming_zero_at (E:=E) (r:=2) (p:=(11,136))
      (by change (2:ℤ)≤2; omega) (by decide) (y_incoming2_zero I) ha (middle_rep2 (by decide) ha) hn
  obtain ⟨y5,hy5⟩ := h281
  obtain ⟨y4,hy4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy5
  have hn4 : y4≠0 := by
    intro hy40
    obtain ⟨_,z,hz2,hz4⟩ := hy4
    let A := E.ssData (11,136)
    let i := Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2))
    let y3 := A.pageπ 1 (i z)
    have hy3 : RepresentsOnPage E 3 (11,136) (I.realization.basis .sphere 11 136 3) y3 := by
      refine ⟨by decide,i z,?_,rfl⟩
      change (i ≫ Subobject.ofLE _ _ _ ≫ A.pageπ 0) z=_
      dsimp only [i]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz2
    obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 3 (by change (2:ℤ)≤3; omega) (8,134) z).mp (hz4.trans hy40)
    change E.d 3 (8,134) u=y3 at hu
    obtain ⟨out,hout,hell⟩ := y_incoming3_represented I u
    have hcoord : e out 3=0 := hell e he
    rw [hu] at hout
    have hdiff : RepresentsOnPage E 3 (11,136) (I.realization.basis .sphere 11 136 3-out) 0 := by
      simpa only [sub_self] using hsub hy3 hout
    have hx : e (I.realization.basis .sphere 11 136 3-out) 3=1 := by
      rw [map_sub,Finsupp.sub_apply,←he3,LinearEquiv.apply_symm_apply,hcoord]
      norm_num [Finsupp.single_apply]
    exact nonzero3 hx hdiff rfl
  exact ⟨y5,hy5,represents_next_nonzero_of_incoming_zero_at (E:=E) (r:=4) (p:=(11,136))
    (by change (2:ℤ)≤4; omega) (by decide) (y_incoming4_zero I) hy5 hy4 hn4⟩


private theorem y_basis_label (I : Inputs D L G) :
    I.realization.sphere 11 136 KIP126.Computation.Near126.Y=I.realization.basis .sphere 11 136 3 := by
  classical
  have hc := I.csv (⟨.sphere,11,136,["69,1,89,1","1,1,389,1","1,1,388,1","0,2,391,1","0,3,375,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 192) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (3:Fin 5)
  have heq : KIP126.Computation.Near126.Y=z := by
    apply Subtype.ext
    rw [hz]
    change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨391,by decide⟩ = projection (monomialOfString "0,2,391,1")
    have hs : "0,2,391,1" ≠ "" := by decide
    have hp : (("0,2,391,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0,2,391,1] := by
      have split : "0,2,391,1".splitOn ","=["0","2","391","1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem y_survives_five (I : Inputs D L G) :
    Derived.Survival I.realization 5 KIP126.Computation.Near126.Y := by
  classical
  unfold Derived.Survival
  rw [y_basis_label I]
  exact y_raw_survives_five I


private theorem y_not_multiple (I : Inputs D L G) : ¬ ∃ a : E2 H SphereSpectrum 10 132,
    Sphere.Internal.product H M (s := 1) (t := 4) (s' := 10) (t' := 132)
      (Sphere.Internal.hi H M 2) a = I.realization.sphere 11 136 KIP126.Computation.Near126.Y := by
  classical
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,132,[]⟩ (by
    exact List.mem_of_getElem? (i := 179) (by rfl))
  change (sequence D .sphere).Page 2 (10,132) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  haveI : Subsingleton (E2 H SphereSpectrum 10 132) := e.injective.subsingleton
  intro ⟨a,ha⟩
  have ha0 : a=0 := Subsingleton.elim _ _
  have hY : I.realization.sphere 11 136 KIP126.Computation.Near126.Y=0 := by
    rw [ha0] at ha
    simpa only [Sphere.Internal.product,map_zero] using ha.symm
  obtain ⟨y,hy,hyn⟩ := y_survives_five I
  rw [hY] at hy
  exact hyn (represents_unique hy (RepresentsOnPage.zero (by decide)))


private theorem sphere_basic_survival_hd2h6_h142 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (1,64) (3,65)
    (I.realization.basis .sphere 1 64 0) (I.realization.basis .sphere 3 65 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,1,64,[0],3,65,[0],"S0_AdamsE2_ss",401⟩ (by
    exact List.mem_of_getElem? (i := 142) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (1,64) (3,65) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 1 64 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 3 65 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_basic_survival_hd2h6 (I : Inputs D L G) : Derived.Differential I.realization 2 dataH6 (mulAt dataH0 h5Sq) := by
  classical
  let E := sequence D .sphere
  have hs : I.realization.sphere 1 64 (dataH6) = I.realization.basis .sphere 1 64 0 := by
    have hc := I.csv (⟨.sphere,1,64,["69,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 85) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
    have heq : (dataH6)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨69,by decide⟩ = projection (monomialOfString "69,1")
      have hp : (("69,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69, 1] := by
        have split : "69,1".splitOn "," = ["69", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "69,1"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have ht : I.realization.sphere 3 65 (mulAt dataH0 h5Sq) = I.realization.basis .sphere 3 65 0 := by
    have hc := I.csv (⟨.sphere,3,65,["0,1,18,2"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 102) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
    have heq : (mulAt dataH0 h5Sq)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨0,by decide⟩ * (generator ⟨18,by decide⟩*generator ⟨18,by decide⟩) = projection (monomialOfString "0,1,18,2")
      have hp : (("0,1,18,2".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 1, 18, 2] := by
        have split : "0,1,18,2".splitOn "," = ["0", "1", "18", "2"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "0,1,18,2"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have h142 : HasDifferential E 2 (1,64) (3,65)
      (I.realization.basis .sphere 1 64 0) (I.realization.basis .sphere 3 65 0) := sphere_basic_survival_hd2h6_h142 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,3,65,["0,1,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 102) (by rfl))
  change E.Page 2 (3,65) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 3 65 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 3 65 0 := he 0
  change HasNonzeroDifferential E 2 (1,64) (3,65) _ _
  rw [hs,ht]
  obtain ⟨hd,x,y,hx,hy,hxy⟩ := h142
  refine ⟨hd,x,y,hx,hy,hxy,?_⟩
  rw [←hy.eq_on_page_two,←he0]
  intro h
  have hh := congrArg (fun x => e x 0) h
  simpa using hh

private theorem sphere_basic_survival_hd2x_h201 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,133) (10,134)
    (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,133,[1],10,134,[2, 4],"S0_AdamsE2_ss",2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,133) (10,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_basic_survival_hd2x (I : Inputs D L G) : Derived.Differential I.realization 2 (atom .x_125_8) (mulAt dataH1 KIP126.Computation.Near126.V + U) := by
  classical
  let E := sequence D .sphere
  have hs : I.realization.sphere 8 133 (atom .x_125_8) = I.realization.basis .sphere 8 133 1 := by
    have hc := I.csv (⟨.sphere,8,133,["376,1", "375,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 161) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (1:Fin 2)
    have heq : (atom .x_125_8)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨375,by decide⟩ = projection (monomialOfString "375,1")
      have hp : (("375,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [375, 1] := by
        have split : "375,1".splitOn "," = ["375", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "375,1"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have ht : I.realization.sphere 10 134 (mulAt dataH1 (atom .x_123_9)) = I.realization.basis .sphere 10 134 2 := by
    have hc := I.csv (⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 181) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (2:Fin 5)
    have heq : (mulAt dataH1 (atom .x_123_9))=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨1,by decide⟩*generator ⟨366,by decide⟩ = projection (monomialOfString "1,1,366,1")
      have hp : (("1,1,366,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1, 1, 366, 1] := by
        have split : "1,1,366,1".splitOn "," = ["1", "1", "366", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "1,1,366,1"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have hu : I.realization.sphere 10 134 (U) = I.realization.basis .sphere 10 134 4 := by
    have hc := I.csv (⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 181) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (4:Fin 5)
    have heq : (U)=z := by
      apply Subtype.ext
      rw [hz]
      change (generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*generator ⟨367,by decide⟩ = projection (monomialOfString "0,2,367,1")
      have hp : (("0,2,367,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 2, 367, 1] := by
        have split : "0,2,367,1".splitOn "," = ["0", "2", "367", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "0,2,367,1"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have hV : mulAt dataH1 KIP126.Computation.Near126.V = mulAt dataH1 (atom .x_123_9) := by
    apply Subtype.ext
    change h1*((atom .x_123_9).val+h0*(atom .x_123_8).val)=h1*(atom .x_123_9).val
    rw [mul_add,←mul_assoc,mul_comm h1 h0,h0_mul_h1_eq_zero,zero_mul,add_zero]
  have h201 : HasDifferential E 2 (8,133) (10,134)
      (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := sphere_basic_survival_hd2x_h201 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 134 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 10 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 10 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 10 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 10 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 10 134 4 := he 4
  change HasNonzeroDifferential E 2 (8,133) (10,134) _ _
  rw [hs,hV,map_add,ht,hu]
  obtain ⟨hd,x,y,hx,hy,hxy⟩ := h201
  refine ⟨hd,x,y,hx,hy,hxy,?_⟩
  rw [←hy.eq_on_page_two,←he2,←he4]
  intro h
  have hh := congrArg (fun x => e x 2) h
  simpa using hh

private theorem sphere_basic_survival_hVX (I : Inputs D L G) : Derived.Survival I.realization 12 KIP126.Computation.Near126.V ∧ Derived.NotHit I.realization KIP126.Computation.Near126.V ∧
  Derived.Survival I.realization 6 X ∧ Derived.NotHit I.realization X := by
  classical

  exact ⟨v_survives I,v_never_hit I,x_survives I,x_never_hit I⟩

private theorem sphere_basic_survival_hY (I : Inputs D L G) : Derived.Survival I.realization 5 Y ∧
  (¬ ∃ a : E2 H SphereSpectrum 10 132,
    Sphere.Internal.product H M (s := 1) (t := 4) (s' := 10) (t' := 132)
      (Sphere.Internal.hi H M 2) a = I.realization.sphere 11 136 Y) := by
  classical

  exact ⟨y_survives_five I,y_not_multiple I⟩

private theorem sphere_basic_survival (I : Inputs D L G) :
    (Derived.Differential I.realization 2 dataH6 (mulAt dataH0 h5Sq)) ∧
    (Derived.Differential I.realization 2 (atom .x_125_8) (mulAt dataH1 KIP126.Computation.Near126.V + U)) ∧
    (Derived.Survival I.realization 12 KIP126.Computation.Near126.V ∧ Derived.NotHit I.realization KIP126.Computation.Near126.V ∧
    Derived.Survival I.realization 6 X ∧ Derived.NotHit I.realization X) ∧
    (Derived.Survival I.realization 5 Y ∧
    (¬ ∃ a : E2 H SphereSpectrum 10 132,
      Sphere.Internal.product H M (s := 1) (t := 4) (s' := 10) (t' := 132)
        (Sphere.Internal.hi H M 2) a = I.realization.sphere 11 136 Y)) := by
  classical
  exact ⟨(sphere_basic_survival_hd2h6 I), (sphere_basic_survival_hd2x I), (sphere_basic_survival_hVX I), (sphere_basic_survival_hY I)⟩

private theorem stem125_af12_four_h260 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,136) (12,137)
    ((I.realization.basis .sphere 10 136 0)) ((I.realization.basis .sphere 12 137 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,136,[0],12,137,[2],"S0_AdamsE2_ss",2859⟩ (by
    exact List.mem_of_getElem? (i := 260) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,136) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af12_four_h234 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    ((I.realization.basis .sphere 9 135 3)) ((I.realization.basis .sphere 12 137 3)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,135,[3],12,137,[3],"S0_AdamsE2_ss",2793⟩ (by
    exact List.mem_of_getElem? (i := 234) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af12_four_h307 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    ((I.realization.basis .sphere 9 135 0) + (I.realization.basis .sphere 9 135 3)) ((I.realization.basis .sphere 12 137 4)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,135,[0, 3],12,137,[4],"S0_AdamsE2_ss",2920⟩ (by
    exact List.mem_of_getElem? (i := 307) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0, 3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af12_four_h308 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,137) (14,138)
    ((I.realization.basis .sphere 12 137 1)) ((I.realization.basis .sphere 14 138 4)) := by
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
  exact hd

private theorem stem125_af12_four_h309 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,137) (14,138)
    ((I.realization.basis .sphere 12 137 0)) ((I.realization.basis .sphere 14 138 3)) := by
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
  exact hd

private theorem stem125_af12_four (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (12,137)) := by
  classical
  let E := sequence D .sphere
  have h260 : HasDifferential E 2 (10,136) (12,137)
      ((I.realization.basis .sphere 10 136 0)) ((I.realization.basis .sphere 12 137 2)) := stem125_af12_four_h260 I
  have h234 : HasDifferential E 3 (9,135) (12,137)
      ((I.realization.basis .sphere 9 135 3)) ((I.realization.basis .sphere 12 137 3)) := stem125_af12_four_h234 I
  have h307 : HasDifferential E 3 (9,135) (12,137)
      ((I.realization.basis .sphere 9 135 0) + (I.realization.basis .sphere 9 135 3)) ((I.realization.basis .sphere 12 137 4)) := stem125_af12_four_h307 I
  have h308 : HasDifferential E 2 (12,137) (14,138)
      ((I.realization.basis .sphere 12 137 1)) ((I.realization.basis .sphere 14 138 4)) := stem125_af12_four_h308 I
  have h309 : HasDifferential E 2 (12,137) (14,138)
      ((I.realization.basis .sphere 12 137 0)) ((I.realization.basis .sphere 14 138 3)) := stem125_af12_four_h309 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 137 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
    exact List.mem_of_getElem? (i := 216) (by rfl))
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 138 i.val at hf
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 12 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 12 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 12 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 12 137 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 12 137 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 14 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 14 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 14 138 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 14 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 14 138 4 := hf 4
  have hz2 : RepresentsOnPage E 4 (12,137) (I.realization.basis .sphere 12 137 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h260
  have d2 : E.d 2 (12,137) (I.realization.basis .sphere 12 137 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (middle_rep2 (by decide) hz2) ⟨0,hz2⟩
  have hz3 : RepresentsOnPage E 4 (12,137) (I.realization.basis .sphere 12 137 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h234
  have d3 : E.d 2 (12,137) (I.realization.basis .sphere 12 137 3)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (middle_rep2 (by decide) hz3) ⟨0,hz3⟩
  have hz4 : RepresentsOnPage E 4 (12,137) (I.realization.basis .sphere 12 137 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h307
  have d4 : E.d 2 (12,137) (I.realization.basis .sphere 12 137 4)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (middle_rep2 (by decide) hz4) ⟨0,hz4⟩
  have d0 : E.d 2 (12,137) (I.realization.basis .sphere 12 137 0)=I.realization.basis .sphere 14 138 3 := h309.eq_on_page_two.2
  have d1 : E.d 2 (12,137) (I.realization.basis .sphere 12 137 1)=I.realization.basis .sphere 14 138 4 := h308.eq_on_page_two.2
  suffices hall : ∀ y : E.Page 4 (12,137), y=0 by
    exact ⟨fun x y => (hall x).trans (hall y).symm⟩
  intro y
  let A := E.ssData (12,137)
  haveI : Epi (A.pageπ 2) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 2)).mp inferInstance y
  let x : E.Page 2 (12,137) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
  have hx : RepresentsOnPage E 4 (12,137) x y := ⟨by decide,z,rfl,hz⟩
  have dx : E.d 2 (12,137) x=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (middle_rep2 (by decide) hx) ⟨y,hx⟩
  let c : Fin 5 → F2 := e x
  have hcoef := congrArg e.symm (FinitePageCalculus.f2_expand (e x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
  change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
  simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
  have hd := congrArg (E.d 2 (12,137)) hcoef
  rw [dx] at hd
  simp only [map_add,apply_ite,map_zero] at hd
  simp only [d0,d1,d2,d3,d4,ite_self,zero_add,add_zero] at hd
  have c0 : c 0=0 := by
    by_contra h0
    simp only [h0,ite_false] at hd
    by_cases h1 : c 1=0
    all_goals simp only [h1,ite_true,ite_false] at hd
    all_goals have hh := congrArg (fun z => f z 3) hd
    all_goals simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hf3,←hf4,LinearEquiv.apply_symm_apply] at hh
    all_goals norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have c1 : c 1=0 := by
    by_contra h1
    simp only [c0,h1,ite_true,ite_false,zero_add] at hd
    have hh := congrArg (fun z => f z 4) hd
    simp only [map_zero,Finsupp.zero_apply,←hf4,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  apply represents_unique hx
  rw [hcoef]
  simp only [c0,c1,ite_true,zero_add]
  have hh := middle_add (middle_if (c 2) hz2) (middle_add (middle_if (c 3) hz3) (middle_if (c 4) hz4))
  simpa only [ite_self,zero_add] using hh


private theorem stem125_af13_five_h231 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    ((I.realization.basis .sphere 9 135 2)) ((I.realization.basis .sphere 13 138 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
    exact List.mem_of_getElem? (i := 231) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af13_five_h232 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    ((I.realization.basis .sphere 9 135 1)) ((I.realization.basis .sphere 13 138 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
    exact List.mem_of_getElem? (i := 232) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af13_five_h288 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    ((I.realization.basis .sphere 11 137 0)) ((I.realization.basis .sphere 13 138 3)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
    exact List.mem_of_getElem? (i := 288) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,137) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af13_five_h289 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    ((I.realization.basis .sphere 11 137 3)) ((I.realization.basis .sphere 13 138 4)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
    exact List.mem_of_getElem? (i := 289) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,137) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af13_five_h329 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (13,138) (16,140)
    ((I.realization.basis .sphere 13 138 1)) ((I.realization.basis .sphere 16 140 1)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,13,138,[1],16,140,[1],"S0_AdamsE2_ss",3012⟩ (by
    exact List.mem_of_getElem? (i := 329) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,138) (16,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af13_five_h314 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,138) (14,139)
    ((I.realization.basis .sphere 12 138 1)) ((I.realization.basis .sphere 14 139 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,12,138,[1],14,139,[2],"S0_AdamsE2_ss",3017⟩ (by
    exact List.mem_of_getElem? (i := 314) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,138) (14,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 139 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af13_five_h343 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,139) (16,140)
    ((I.realization.basis .sphere 14 139 0)) ((I.realization.basis .sphere 16 140 2)) := by
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
  exact hd

private theorem stem125_af13_five_h342 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (14,139) (I.realization.basis .sphere 14 139 1) := by
  classical
  have hh := I.results ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
    exact List.mem_of_getElem? (i := 342) (by rfl))
  dsimp only [Statement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1]=true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem stem125_af13_five (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (13,138)) := by
  classical
  let E := sequence D .sphere
  have h231 : HasDifferential E 4 (9,135) (13,138)
      ((I.realization.basis .sphere 9 135 2)) ((I.realization.basis .sphere 13 138 0)) := stem125_af13_five_h231 I
  have h232 : HasDifferential E 4 (9,135) (13,138)
      ((I.realization.basis .sphere 9 135 1)) ((I.realization.basis .sphere 13 138 2)) := stem125_af13_five_h232 I
  have h288 : HasDifferential E 2 (11,137) (13,138)
      ((I.realization.basis .sphere 11 137 0)) ((I.realization.basis .sphere 13 138 3)) := stem125_af13_five_h288 I
  have h289 : HasDifferential E 2 (11,137) (13,138)
      ((I.realization.basis .sphere 11 137 3)) ((I.realization.basis .sphere 13 138 4)) := stem125_af13_five_h289 I
  have h329 : HasDifferential E 3 (13,138) (16,140)
      ((I.realization.basis .sphere 13 138 1)) ((I.realization.basis .sphere 16 140 1)) := stem125_af13_five_h329 I
  have h314 : HasDifferential E 2 (12,138) (14,139)
      ((I.realization.basis .sphere 12 138 1)) ((I.realization.basis .sphere 14 139 2)) := stem125_af13_five_h314 I
  have h343 : HasDifferential E 2 (14,139) (16,140)
      ((I.realization.basis .sphere 14 139 0)) ((I.realization.basis .sphere 16 140 2)) := stem125_af13_five_h343 I
  have h342 : ReachesPage E 1000 (14,139) (I.realization.basis .sphere 14 139 1) := stem125_af13_five_h342 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 209) (by rfl))
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 138 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,14,139,["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl))
  change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 139 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,16,140,["9,1,261,1", "1,1,438,1", "0,1,448,1", "0,2,440,1", "0,2,439,1"]⟩ (by
    exact List.mem_of_getElem? (i := 231) (by rfl))
  change E.Page 2 (16,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 140 i.val at hg
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 13 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 13 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 13 138 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 13 138 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 13 138 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 14 139 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 14 139 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 14 139 2 := hf 2
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 16 140 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 16 140 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 16 140 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 16 140 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 16 140 4 := hg 4
  have df0 : E.d 2 (14,139) (I.realization.basis .sphere 14 139 0)=I.realization.basis .sphere 16 140 2 := h343.eq_on_page_two.2
  have df1 : E.d 2 (14,139) (I.realization.basis .sphere 14 139 1)=0 := by
    obtain ⟨x,hx⟩ := h342
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000)
      (middle_rep2 (by decide) hx) ⟨x,hx⟩
  have df2 : E.d 2 (14,139) (I.realization.basis .sphere 14 139 2)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(12,138)) ⟨_,h314.eq_on_page_two.2⟩
  have incoming (x : E.Page 2 (14,139)) : g (E.d 2 (14,139) x) 1=0 := by
    have all (a : Fin 3 →₀ F2) : g (E.d 2 (14,139) (f.symm a)) 1=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hc ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (14,139) (f.symm (Finsupp.single i 1))) 1=0
          rw [hf]
          fin_cases i
          all_goals dsimp only
          all_goals simp only [df0,df1,df2,map_zero,Finsupp.zero_apply,←hg2,LinearEquiv.apply_symm_apply]
          all_goals norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using all (f x)
  obtain ⟨_,b1,t,hb1,ht,db1⟩ := h329
  have db1' : E.d 3 (13,138) b1=t := db1
  have tn : t≠0 := by
    intro ht0
    obtain ⟨_,z,hz,hzt⟩ := ht
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (14,139) z).mp (hzt.trans ht0)
    change (Subobject.ofLE _ _ ((E.ssData (16,140)).Z_anti bot_le) ≫ (E.ssData (16,140)).pageπ 0) z ∈ LinearMap.range (E.d 2 (14,139)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (16,140)).Z_anti bot_le) ≫ (E.ssData (16,140)).pageπ 0) z = I.realization.basis .sphere 16 140 1 at hz
    rw [hz] at hh
    obtain ⟨u,hu⟩ := hh
    have hh := incoming u
    rw [hu,←hg1,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  have hz0 : RepresentsOnPage E 5 (13,138) (I.realization.basis .sphere 13 138 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h231
  have hz2 : RepresentsOnPage E 5 (13,138) (I.realization.basis .sphere 13 138 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h232
  have hz3 : RepresentsOnPage E 5 (13,138) (I.realization.basis .sphere 13 138 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) h288
  have hz4 : RepresentsOnPage E 5 (13,138) (I.realization.basis .sphere 13 138 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) h289
  obtain ⟨_,_,b0late,_,hb0late,_⟩ := h231
  obtain ⟨b0,hb0⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hb0late
  have db0 : E.d 3 (13,138) b0=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) hb0 ⟨b0late,hb0late⟩
  obtain ⟨_,_,b2late,_,hb2late,_⟩ := h232
  obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hb2late
  have db2 : E.d 3 (13,138) b2=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) hb2 ⟨b2late,hb2late⟩
  have hb3 : RepresentsOnPage E 3 (13,138) (I.realization.basis .sphere 13 138 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h288
  have hb4 : RepresentsOnPage E 3 (13,138) (I.realization.basis .sphere 13 138 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h289
  suffices hall : ∀ y : E.Page 5 (13,138), y=0 by
    exact ⟨fun x y => (hall x).trans (hall y).symm⟩
  intro y
  let A := E.ssData (13,138)
  haveI : Epi (A.pageπ 3) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 3)).mp inferInstance y
  let x : E.Page 2 (13,138) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
  have hx : RepresentsOnPage E 5 (13,138) x y := ⟨by decide,z,rfl,hz⟩
  let c : Fin 5 → F2 := e x
  have hcoef := congrArg e.symm (FinitePageCalculus.f2_expand (e x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
  change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
  simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
  have hrep3 : RepresentsOnPage E 3 (13,138) x
      ((if c 0=0 then 0 else b0)+((if c 1=0 then 0 else b1)+(if c 2=0 then 0 else b2))) := by
    rw [hcoef]
    have hh := middle_add (middle_if (c 0) hb0) (middle_add (middle_if (c 1) hb1)
      (middle_add (middle_if (c 2) hb2) (middle_add (middle_if (c 3) hb3) (middle_if (c 4) hb4))))
    simpa only [ite_self,add_zero] using hh
  have dx3 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) hrep3 ⟨y,hx⟩
  have c1 : c 1=0 := by
    by_contra hc1
    apply tn
    simpa only [map_add,apply_ite,map_zero,db0,db1',db2,hc1,ite_false,ite_self,zero_add,add_zero] using dx3
  apply represents_unique hx
  rw [hcoef]
  simp only [c1,ite_true,zero_add]
  have hh := middle_add (middle_if (c 0) hz0) (middle_add (middle_if (c 2) hz2)
    (middle_add (middle_if (c 3) hz3) (middle_if (c 4) hz4)))
  simpa only [ite_self,zero_add] using hh


private theorem stem125_e2_low (I : Inputs D L G) (s : ℕ) (hs : s≤4) :
    Subsingleton ((sequence D .sphere).Page 2 (s,(s:ℤ)+125)) := by
  classical
  let E := sequence D .sphere
  interval_cases s
  · change Subsingleton (E.Page 2 (0,125))
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,0,125,[]⟩ (by
      exact List.mem_of_getElem? (i := 76) (by rfl))
    change E.Page 2 (0,125) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 0 125 i.val at he
    exact e.injective.subsingleton
  · change Subsingleton (E.Page 2 (1,126))
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,1,126,[]⟩ (by
      exact List.mem_of_getElem? (i := 89) (by rfl))
    change E.Page 2 (1,126) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 1 126 i.val at he
    exact e.injective.subsingleton
  · change Subsingleton (E.Page 2 (2,127))
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,2,127,[]⟩ (by
      exact List.mem_of_getElem? (i := 99) (by rfl))
    change E.Page 2 (2,127) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 2 127 i.val at he
    exact e.injective.subsingleton
  · change Subsingleton (E.Page 2 (3,128))
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,3,128,[]⟩ (by
      exact List.mem_of_getElem? (i := 107) (by rfl))
    change E.Page 2 (3,128) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 3 128 i.val at he
    exact e.injective.subsingleton
  · change Subsingleton (E.Page 2 (4,129))
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,4,129,[]⟩ (by
      exact List.mem_of_getElem? (i := 118) (by rfl))
    change E.Page 2 (4,129) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 4 129 i.val at he
    exact e.injective.subsingleton

private theorem sphere_low_page_vanishing_hMiddle125 (I : Inputs D L G) : Subsingleton ((sequence D .sphere).Page 4 (12,137)) ∧
  Subsingleton ((sequence D .sphere).Page 5 (13,138)) := by
  classical

  exact ⟨stem125_af12_four I,stem125_af13_five I⟩

private theorem sphere_low_page_vanishing_hAF11_h171 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 0) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 3) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3], "S0_AdamsE2_ss", 2492⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h172 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 1) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 1 + I.realization.basis .sphere 10 134 3 + I.realization.basis .sphere 10 134 4) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4], "S0_AdamsE2_ss", 2493⟩ (by
    exact List.mem_of_getElem? (i := 172) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h201 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,133) (10,134) (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "S0_AdamsE2_ss", 2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,133) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h250 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 5 (10,134) (15,138) (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 5, 10, 134, [3], 15, 138, [1], "S0_AdamsE2_ss", 2694⟩ (by
    exact List.mem_of_getElem? (i := 250) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (10,134) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h200 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,133) (11,135) (I.realization.basis .sphere 8 133 0) (I.realization.basis .sphere 11 135 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2629⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,133) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h226 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,134) (12,136) (I.realization.basis .sphere 9 134 1) (I.realization.basis .sphere 12 136 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 9, 134, [1], 12, 136, [0], "S0_AdamsE2_ss", 2697⟩ (by
    exact List.mem_of_getElem? (i := 226) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,134) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h227 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135) (I.realization.basis .sphere 9 134 0) (I.realization.basis .sphere 11 135 3 + I.realization.basis .sphere 11 135 4) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 9, 134, [0], 11, 135, [3, 4], "S0_AdamsE2_ss", 2698⟩ (by
    exact List.mem_of_getElem? (i := 227) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h228 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135) (I.realization.basis .sphere 9 134 4) (I.realization.basis .sphere 11 135 4) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 9, 134, [4], 11, 135, [4], "S0_AdamsE2_ss", 2699⟩ (by
    exact List.mem_of_getElem? (i := 228) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h253 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136) (I.realization.basis .sphere 10 135 1) (I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 10, 135, [1], 12, 136, [1, 2], "S0_AdamsE2_ss", 2785⟩ (by
    exact List.mem_of_getElem? (i := 253) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h254 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136) (I.realization.basis .sphere 10 135 2) (I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 10, 135, [2], 12, 136, [3, 4], "S0_AdamsE2_ss", 2786⟩ (by
    exact List.mem_of_getElem? (i := 254) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h255 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136) (I.realization.basis .sphere 10 135 4) (I.realization.basis .sphere 12 136 4) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 10, 135, [4], 12, 136, [4], "S0_AdamsE2_ss", 2787⟩ (by
    exact List.mem_of_getElem? (i := 255) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h277 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (11,135) (15,138) (I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 15 138 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0], "S0_AdamsE2_ss", 2781⟩ (by
    exact List.mem_of_getElem? (i := 277) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (11,135) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h278 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,135) (13,136) (I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 13 136 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 11, 135, [2], 13, 136, [2], "S0_AdamsE2_ss", 2782⟩ (by
    exact List.mem_of_getElem? (i := 278) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,135) (13,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 136 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h304 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,136) (14,137) (I.realization.basis .sphere 12 136 2) (I.realization.basis .sphere 14 137 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2], "S0_AdamsE2_ss", 2849⟩ (by
    exact List.mem_of_getElem? (i := 304) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,136) (14,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 137 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h321 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,136) (13,137) (I.realization.basis .sphere 11 136 4) (I.realization.basis .sphere 13 137 3) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 11, 136, [4], 13, 137, [3], "S0_AdamsE2_ss", 2914⟩ (by
    exact List.mem_of_getElem? (i := 321) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,136) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h322 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (10,135) (13,137) (I.realization.basis .sphere 10 135 0) (I.realization.basis .sphere 13 137 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 10, 135, [0], 13, 137, [0], "S0_AdamsE2_ss", 2915⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (10,135) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h323 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (13,137) (I.realization.basis .sphere 13 137 1) := by
  classical
  have hrow := I.results ⟨.sphere, .reaches, 1000, 13, 137, [1], 13, 137, [], "S0_AdamsE2_ss", 2916⟩ (by
    exact List.mem_of_getElem? (i := 323) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [1] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem sphere_low_page_vanishing_hAF11_h324 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (13,137) (16,139) (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
    exact List.mem_of_getElem? (i := 324) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,137) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11 (I : Inputs D L G) : Subsingleton ((sequence D .sphere).Page 5 (11,135)) := by
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
  have h171 : HasDifferential E 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 0) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 3) := sphere_low_page_vanishing_hAF11_h171 I
  have h172 : HasDifferential E 4 (6,131) (10,134) (I.realization.basis .sphere 6 131 1) (I.realization.basis .sphere 10 134 0 + I.realization.basis .sphere 10 134 1 + I.realization.basis .sphere 10 134 3 + I.realization.basis .sphere 10 134 4) := sphere_low_page_vanishing_hAF11_h172 I
  have h201 : HasDifferential E 2 (8,133) (10,134) (I.realization.basis .sphere 8 133 1) (I.realization.basis .sphere 10 134 2 + I.realization.basis .sphere 10 134 4) := sphere_low_page_vanishing_hAF11_h201 I
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := sphere_low_page_vanishing_hAF11_h250 I
  have h200 : HasDifferential E 3 (8,133) (11,135) (I.realization.basis .sphere 8 133 0) (I.realization.basis .sphere 11 135 0) := sphere_low_page_vanishing_hAF11_h200 I
  have h226 : HasDifferential E 3 (9,134) (12,136) (I.realization.basis .sphere 9 134 1) (I.realization.basis .sphere 12 136 0) := sphere_low_page_vanishing_hAF11_h226 I
  have h227 : HasDifferential E 2 (9,134) (11,135) (I.realization.basis .sphere 9 134 0) (I.realization.basis .sphere 11 135 3 + I.realization.basis .sphere 11 135 4) := sphere_low_page_vanishing_hAF11_h227 I
  have h228 : HasDifferential E 2 (9,134) (11,135) (I.realization.basis .sphere 9 134 4) (I.realization.basis .sphere 11 135 4) := sphere_low_page_vanishing_hAF11_h228 I
  have h253 : HasDifferential E 2 (10,135) (12,136) (I.realization.basis .sphere 10 135 1) (I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) := sphere_low_page_vanishing_hAF11_h253 I
  have h254 : HasDifferential E 2 (10,135) (12,136) (I.realization.basis .sphere 10 135 2) (I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4) := sphere_low_page_vanishing_hAF11_h254 I
  have h255 : HasDifferential E 2 (10,135) (12,136) (I.realization.basis .sphere 10 135 4) (I.realization.basis .sphere 12 136 4) := sphere_low_page_vanishing_hAF11_h255 I
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 15 138 0) := sphere_low_page_vanishing_hAF11_h277 I
  have h278 : HasDifferential E 2 (11,135) (13,136) (I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 13 136 2) := sphere_low_page_vanishing_hAF11_h278 I
  have h304 : HasDifferential E 2 (12,136) (14,137) (I.realization.basis .sphere 12 136 2) (I.realization.basis .sphere 14 137 2) := sphere_low_page_vanishing_hAF11_h304 I
  have h321 : HasDifferential E 2 (11,136) (13,137) (I.realization.basis .sphere 11 136 4) (I.realization.basis .sphere 13 137 3) := sphere_low_page_vanishing_hAF11_h321 I
  have h322 : HasDifferential E 3 (10,135) (13,137) (I.realization.basis .sphere 10 135 0) (I.realization.basis .sphere 13 137 0) := sphere_low_page_vanishing_hAF11_h322 I
  have h323 : ReachesPage E 1000 (13,137) (I.realization.basis .sphere 13 137 1) := sphere_low_page_vanishing_hAF11_h323 I
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := sphere_low_page_vanishing_hAF11_h324 I
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

  have ht0n : t0≠0 := nonzero4 (by
    rw [←he15_138_0]
    intro h
    have hh := congrArg (fun z => e15_138 z 0) h
    simpa using hh) ht0
  have hnext := next_page_two_of_kernel E 4 (by change (2:ℤ)≤4;omega) (11,135) 0 (by
    intro a ha
    rcases kernel_11 a with h|h
    · exact Or.inl h
    · rw [h,hd4] at ha
      exact (ht0n ha).elim)
  have hall (a : E.Page 5 (11,135)) : a=0 := by
    rcases hnext a with h|h
    · exact h
    · simpa only [map_zero] using h
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem sphere_low_page_vanishing_hAF12_h226 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,134) (12,136)
    (I.realization.basis .sphere 9 134 1) (I.realization.basis .sphere 12 136 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
    exact List.mem_of_getElem? (i := 226) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,134) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_low_page_vanishing_hAF12_h253 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.realization.basis .sphere 10 135 1) (I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
    exact List.mem_of_getElem? (i := 253) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_low_page_vanishing_hAF12_h254 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.realization.basis .sphere 10 135 2) (I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
    exact List.mem_of_getElem? (i := 254) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_low_page_vanishing_hAF12_h255 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.realization.basis .sphere 10 135 4) (I.realization.basis .sphere 12 136 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
    exact List.mem_of_getElem? (i := 255) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_low_page_vanishing_hAF12_h304 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,136) (14,137)
    (I.realization.basis .sphere 12 136 2) (I.realization.basis .sphere 14 137 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,12,136,[2],14,137,[2],"S0_AdamsE2_ss",2849⟩ (by
    exact List.mem_of_getElem? (i := 304) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,136) (14,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 137 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_low_page_vanishing_hAF12 (I : Inputs D L G) : Subsingleton ((sequence D .sphere).Page 4 (12,136)) := by
  classical
  let E := sequence D .sphere
  have h226 : HasDifferential E 3 (9,134) (12,136)
      (I.realization.basis .sphere 9 134 1) (I.realization.basis .sphere 12 136 0) := sphere_low_page_vanishing_hAF12_h226 I
  have h253 : HasDifferential E 2 (10,135) (12,136)
      (I.realization.basis .sphere 10 135 1) (I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) := sphere_low_page_vanishing_hAF12_h253 I
  have h254 : HasDifferential E 2 (10,135) (12,136)
      (I.realization.basis .sphere 10 135 2) (I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4) := sphere_low_page_vanishing_hAF12_h254 I
  have h255 : HasDifferential E 2 (10,135) (12,136)
      (I.realization.basis .sphere 10 135 4) (I.realization.basis .sphere 12 136 4) := sphere_low_page_vanishing_hAF12_h255 I
  have h304 : HasDifferential E 2 (12,136) (14,137)
      (I.realization.basis .sphere 12 136 2) (I.realization.basis .sphere 14 137 2) := sphere_low_page_vanishing_hAF12_h304 I
  obtain ⟨e12_136,he12_136⟩ := I.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e12_136
  change ∀ i : Fin 5, e12_136.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 136 i.val at he12_136
  have he12_136_0 : e12_136.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 12 136 0 := he12_136 0
  have he12_136_1 : e12_136.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 12 136 1 := he12_136 1
  have he12_136_2 : e12_136.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 12 136 2 := he12_136 2
  have he12_136_3 : e12_136.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 12 136 3 := he12_136 3
  have he12_136_4 : e12_136.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 12 136 4 := he12_136 4
  obtain ⟨e14_137,he14_137⟩ := I.basis ⟨.sphere,14,137,["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀ i : Fin 3, e14_137.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 137 i.val at he14_137
  have he14_137_0 : e14_137.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 14 137 0 := he14_137 0
  have he14_137_1 : e14_137.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 14 137 1 := he14_137 1
  have he14_137_2 : e14_137.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 14 137 2 := he14_137 2
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
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  have h226copy := h226
  obtain ⟨_,in0,a0,hin0,ha0,hda0⟩ := h226
  have ha00 : RepresentsOnPage E 4 (12,136) (I.realization.basis .sphere 12 136 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<4) h226copy
  have rz12 : RepresentsOnPage E 4 (12,136)
      (I.realization.basis .sphere 12 136 1 + I.realization.basis .sphere 12 136 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h253
  have rz34 : RepresentsOnPage E 4 (12,136)
      (I.realization.basis .sphere 12 136 3 + I.realization.basis .sphere 12 136 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h254
  have rz4 : RepresentsOnPage E 4 (12,136) (I.realization.basis .sphere 12 136 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h255
  have rz3 : RepresentsOnPage E 4 (12,136) (I.realization.basis .sphere 12 136 3) 0 := by
    simpa only [add_sub_cancel_right,sub_self] using hsub rz34 rz4
  have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a0,ha0⟩
  have d12 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz12⟩
  have d3 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz3⟩
  have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz4⟩
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
  have hall (x : E.Page 4 (12,136)) : x=0 := by
    obtain ⟨a,ha⟩ := lift_e2 (by decide : (2:ℤ)≤4) x
    have da := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 a) ⟨x,ha⟩
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
    have hx : x=0 := by
      apply represents_unique ha
      rw [hacomb]
      simpa only [ite_self,add_zero] using hadd (hadd (hadd (hif (c 0) ha00) (hif (c 1) rz12)) (hif (c 3) rz3)) (hif (c 4) rz4)
    exact hx
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem sphere_low_page_vanishing_hxH2 (I : Inputs D L G) : I.realization.sphere 9 134 (mulAt X (atom .h2)) = 0 := by
  classical
  have h : mulAt X (atom .h2) = 0 := by
    apply Subtype.ext
    change (h1 * (atom .x_121_7).val) * h2 = 0
    calc
      _ = (h1*h2) * (atom .x_121_7).val := by ac_rfl
      _ = 0 := by rw [h1_mul_h2_eq_zero,zero_mul]
  rw [h,map_zero]

private theorem sphere_low_page_vanishing (I : Inputs D L G) :
    (Subsingleton ((sequence D .sphere).Page 4 (12,137)) ∧
    Subsingleton ((sequence D .sphere).Page 5 (13,138))) ∧
    (Subsingleton ((sequence D .sphere).Page 5 (11,135))) ∧
    (Subsingleton ((sequence D .sphere).Page 4 (12,136))) ∧
    (I.realization.sphere 9 134 (mulAt X (atom .h2)) = 0) ∧
    (∀ (s : ℕ) (hs : s≤4),
      Subsingleton ((sequence D .sphere).Page 2 (s,(s:ℤ)+125))) := by
  classical
  exact ⟨(sphere_low_page_vanishing_hMiddle125 I), (sphere_low_page_vanishing_hAF11 I), (sphere_low_page_vanishing_hAF12 I), (sphere_low_page_vanishing_hxH2 I), stem125_e2_low I⟩

private theorem sphere_named_differentials_hD3sq_h324 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (13,137) (16,139) (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
    exact List.mem_of_getElem? (i := 324) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,137) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD3sq_h366 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 14, 138, [1], 16, 139, [1, 2], "S0_AdamsE2_ss", 3072⟩ (by
    exact List.mem_of_getElem? (i := 366) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD3sq_h367 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 14, 138, [0, 1], 16, 139, [2], "S0_AdamsE2_ss", 3073⟩ (by
    exact List.mem_of_getElem? (i := 367) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD3sq_h654 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (15,138) (18,140) (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 15, 138, [2], 18, 140, [2], "proofs.db/log", 462481⟩ (by
    exact List.mem_of_getElem? (i := 654) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (15,138) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 138 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_d2_16
    (I : KIP126.Computation.Route.Inputs D L G) : (sequence D .sphere).d 2 (16,139)=0  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e16_139,he16_139⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
  change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 139 i.val at he16_139
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := sphere_named_differentials_hD3sq_h324 I
  have h366 : HasDifferential E 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := sphere_named_differentials_hD3sq_h366 I
  have h367 : HasDifferential E 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := sphere_named_differentials_hD3sq_h367 I
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


private theorem sphere_named_differentials_hD3sq (I : Inputs D L G) : Derived.Differential I.realization 3 (mulAt h0Sq (atom .x_123_13_2))
    (mulAt h0Sq (atom .x_122_16)) := by
  classical
  let E := sequence D .sphere
  have stem122_d3_target_nonzero :
    HasNonzeroDifferential E 3 (15,138) (18,140)
      (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := by
    let E := sequence D .sphere
    obtain ⟨e16_139,he16_139⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
      exact List.mem_of_getElem? (i := 230) (by rfl))
    change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
    change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 139 i.val at he16_139
    obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
      exact List.mem_of_getElem? (i := 244) (by rfl))
    change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
    change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.realization.basis .sphere 18 140 i.val at he18_140
    have h324 : HasDifferential E 3 (13,137) (16,139) (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := sphere_named_differentials_hD3sq_h324 I
    have h366 : HasDifferential E 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := sphere_named_differentials_hD3sq_h366 I
    have h367 : HasDifferential E 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := sphere_named_differentials_hD3sq_h367 I
    have h654 : HasDifferential E 3 (15,138) (18,140) (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := sphere_named_differentials_hD3sq_h654 I
    have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
      exact represents_two_self _
    have d2_16 : E.d 2 (16,139)=0 :=
      sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_d2_16 I
    obtain ⟨hdeg,xr,yr,hxr,hyr,hd⟩ := h654
    refine ⟨hdeg,xr,yr,hxr,hyr,hd,?_⟩
    have bne : I.realization.basis .sphere 18 140 2 ≠ 0 := by
      rw [show I.realization.basis .sphere 18 140 2=e18_140.symm (Finsupp.single 2 1) from (he18_140 2).symm]
      intro h
      have hh := congrArg e18_140 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
      norm_num at hh'
    exact represents_next_nonzero_of_incoming_zero_at
      (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)≤2)
      (by exact d2_16) hyr (hrep2 _) bne
  have label15_138_2 : I.realization.sphere 15 138 (mulAt h0Sq (atom .x_123_13_2)) = I.realization.basis .sphere 15 138 2 := by
    have hc := I.csv ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
      exact List.mem_of_getElem? (i := 222) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (2 : Fin 3)
    have heq : (mulAt h0Sq (atom .x_123_13_2))=z := by
      apply Subtype.ext
      rw [hz]
      change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨418,by decide⟩ = projection (monomialOfString "0,2,418,1")
      have hs : "0,2,418,1" ≠ "" := by decide
      have hp : (("0,2,418,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,2,418,1] := by
        have split : "0,2,418,1".splitOn "," = ["0", "2", "418", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  have label18_140_2 : I.realization.sphere 18 140 (mulAt h0Sq (atom .x_122_16)) = I.realization.basis .sphere 18 140 2 := by
    have hc := I.csv ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
      exact List.mem_of_getElem? (i := 244) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (2 : Fin 3)
    have heq : (mulAt h0Sq (atom .x_122_16))=z := by
      apply Subtype.ext
      rw [hz]
      change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨437,by decide⟩ = projection (monomialOfString "0,2,437,1")
      have hs : "0,2,437,1" ≠ "" := by decide
      have hp : (("0,2,437,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,2,437,1] := by
        have split : "0,2,437,1".splitOn "," = ["0", "2", "437", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  change HasNonzeroDifferential E 3 (15,138) (18,140)
    (I.realization.sphere 15 138 (mulAt h0Sq (atom .x_123_13_2)))
    (I.realization.sphere 18 140 (mulAt h0Sq (atom .x_122_16)))
  rw [label15_138_2,label18_140_2]
  exact stem122_d3_target_nonzero

private theorem sphere_named_differentials_hD3x1264_h153 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (3,130) (5,131) (I.realization.basis .sphere 3 130 1) (I.realization.basis .sphere 5 131 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 3, 130, [1], 5, 131, [0], "S0_AdamsE2_ss", 2439⟩ (by
    exact List.mem_of_getElem? (i := 153) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (3,130) (5,131) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 5 131 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD3x1264_h655 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (4,130) (7,132) (I.realization.basis .sphere 4 130 0) (I.realization.basis .sphere 7 132 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "proofs.db/log", 929469⟩ (by
    exact List.mem_of_getElem? (i := 655) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (4,130) (7,132) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD3x1264_label4_130_0 (I : Inputs D L G) : I.realization.sphere 4 130 (atom .x_126_4) = I.realization.basis .sphere 4 130 0  := by
  have hc := I.csv ⟨.sphere, 4, 130, ["341,1", "0,2,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 119) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0 : Fin 2)
  have heq : (atom .x_126_4)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨341,by decide⟩ = projection (monomialOfString "341,1")
    have hs : "341,1" ≠ "" := by decide
    have hp : (("341,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [341,1] := by
      have split : "341,1".splitOn "," = ["341", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD3x1264_label7_132_0 (I : Inputs D L G) : I.realization.sphere 7 132 (mulAt h0Sq (atom .x_125_5)) = I.realization.basis .sphere 7 132 0  := by
  have hc := I.csv ⟨.sphere, 7, 132, ["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0 : Fin 1)
  have heq : (mulAt h0Sq (atom .x_125_5))=z := by
    apply Subtype.ext
    rw [hz]
    change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨340,by decide⟩ = projection (monomialOfString "0,2,340,1")
    have hs : "0,2,340,1" ≠ "" := by decide
    have hp : (("0,2,340,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,2,340,1] := by
      have split : "0,2,340,1".splitOn "," = ["0", "2", "340", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD3x1264 (I : Inputs D L G) : Derived.Differential I.realization 3 (atom .x_126_4) (mulAt h0Sq (atom .x_125_5)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e5_131,he5_131⟩ := I.basis ⟨.sphere, 5, 131, ["0,3,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 127) (by rfl))
  change E.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e5_131
  change ∀i : Fin 1, e5_131.symm (Finsupp.single i 1) = I.realization.basis .sphere 5 131 i.val at he5_131
  obtain ⟨e7_132,he7_132⟩ := I.basis ⟨.sphere, 7, 132, ["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e7_132
  change ∀i : Fin 1, e7_132.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 132 i.val at he7_132
  have h153 : HasDifferential E 2 (3,130) (5,131) (I.realization.basis .sphere 3 130 1) (I.realization.basis .sphere 5 131 0) := sphere_named_differentials_hD3x1264_h153 I
  have h655 : HasDifferential E 3 (4,130) (7,132) (I.realization.basis .sphere 4 130 0) (I.realization.basis .sphere 7 132 0) := sphere_named_differentials_hD3x1264_h655 I
  have label4_130_0 : I.realization.sphere 4 130 (atom .x_126_4) = I.realization.basis .sphere 4 130 0  := sphere_named_differentials_hD3x1264_label4_130_0 I
  have label7_132_0 : I.realization.sphere 7 132 (mulAt h0Sq (atom .x_125_5)) = I.realization.basis .sphere 7 132 0  := sphere_named_differentials_hD3x1264_label7_132_0 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    as_aux_lemma =>
      exact represents_two_self _
  have d2_5 : E.d 2 (5,131)=0 := by
    obtain ⟨y,hy,hd⟩ := differential_target_cycle h153
    have d0 : E.d 2 (5,131) (I.realization.basis .sphere 5 131 0)=0 := by
      exact (congrArg (fun z => E.d 2 (5,131) z) hy.eq_on_page_two).trans hd
    apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e5_131
    intro i
    fin_cases i
    refine ⟨I.realization.basis .sphere 5 131 0,?_,d0⟩
    rw [he5_131]
    exact represents_two_self _
  change HasNonzeroDifferential E 3 (4,130) (7,132)
    (I.realization.sphere 4 130 (atom .x_126_4))
    (I.realization.sphere 7 132 (mulAt h0Sq (atom .x_125_5)))
  rw [label4_130_0,label7_132_0]
  obtain ⟨hdeg,xr,yr,hxr,hyr,hd⟩ := h655
  refine ⟨hdeg,xr,yr,hxr,hyr,hd,?_⟩
  have bne : I.realization.basis .sphere 7 132 0≠0 := by
    rw [show I.realization.basis .sphere 7 132 0 = e7_132.symm (Finsupp.single 0 1) from (he7_132 0).symm]
    exact basis_vector_ne_zero e7_132 0
  exact represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)≤2)
    d2_5 hyr (hrep2 _) bne

private theorem sphere_named_differentials_hD7source_h324 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (13,137) (16,139) (I.realization.basis .sphere 13 137 2) (I.realization.basis .sphere 16 139 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
    exact List.mem_of_getElem? (i := 324) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,137) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h366 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 1 + I.realization.basis .sphere 16 139 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 14, 138, [1], 16, 139, [1, 2], "S0_AdamsE2_ss", 3072⟩ (by
    exact List.mem_of_getElem? (i := 366) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h367 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139) (I.realization.basis .sphere 14 138 0 + I.realization.basis .sphere 14 138 1) (I.realization.basis .sphere 16 139 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 14, 138, [0, 1], 16, 139, [2], "S0_AdamsE2_ss", 3073⟩ (by
    exact List.mem_of_getElem? (i := 367) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h654 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (15,138) (18,140) (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 15, 138, [2], 18, 140, [2], "proofs.db/log", 462481⟩ (by
    exact List.mem_of_getElem? (i := 654) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (15,138) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 138 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h656 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 7 (11,134) (18,140) (I.realization.basis .sphere 11 134 0 + I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 18 140 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 7, 11, 134, [0, 1, 3], 18, 140, [1], "proofs.db/log", 2671068⟩ (by
    exact List.mem_of_getElem? (i := 656) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 7 (11,134) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 134 [0, 1, 3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h250 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 5 (10,134) (15,138) (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 5, 10, 134, [3], 15, 138, [1], "S0_AdamsE2_ss", 2694⟩ (by
    exact List.mem_of_getElem? (i := 250) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (10,134) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h277 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (11,135) (15,138) (I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 15 138 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0], "S0_AdamsE2_ss", 2781⟩ (by
    exact List.mem_of_getElem? (i := 277) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (11,135) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h339 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (14,137) (17,139) (I.realization.basis .sphere 14 137 1) (I.realization.basis .sphere 17 139 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 14, 137, [1], 17, 139, [1], "S0_AdamsE2_ss", 2912⟩ (by
    exact List.mem_of_getElem? (i := 339) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h340 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (14,137) (17,139) (I.realization.basis .sphere 14 137 0) (I.realization.basis .sphere 17 139 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 14, 137, [0], 17, 139, [0], "S0_AdamsE2_ss", 2913⟩ (by
    exact List.mem_of_getElem? (i := 340) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h304 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,136) (14,137) (I.realization.basis .sphere 12 136 2) (I.realization.basis .sphere 14 137 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2], "S0_AdamsE2_ss", 2849⟩ (by
    exact List.mem_of_getElem? (i := 304) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,136) (14,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 137 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h319 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (13,136) (16,138) (I.realization.basis .sphere 13 136 1) (I.realization.basis .sphere 16 138 1) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 13, 136, [1], 16, 138, [1], "S0_AdamsE2_ss", 2843⟩ (by
    exact List.mem_of_getElem? (i := 319) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,136) (16,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 136 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 138 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h320 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (13,136) (16,138) (I.realization.basis .sphere 13 136 0) (I.realization.basis .sphere 16 138 0 + I.realization.basis .sphere 16 138 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 13, 136, [0], 16, 138, [0, 2], "S0_AdamsE2_ss", 2844⟩ (by
    exact List.mem_of_getElem? (i := 320) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,136) (16,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 138 [0, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h278 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,135) (13,136) (I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 13 136 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 11, 135, [2], 13, 136, [2], "S0_AdamsE2_ss", 2782⟩ (by
    exact List.mem_of_getElem? (i := 278) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,135) (13,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 136 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h297 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,133) (12,135) (I.realization.basis .sphere 9 133 1 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 9, 133, [1, 2], 12, 135, [0], "S0_AdamsE2_ss", 2775⟩ (by
    exact List.mem_of_getElem? (i := 297) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h298 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,133) (12,135) (I.realization.basis .sphere 9 133 0 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 1 + I.realization.basis .sphere 12 135 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 9, 133, [0, 2], 12, 135, [1, 2], "S0_AdamsE2_ss", 2776⟩ (by
    exact List.mem_of_getElem? (i := 298) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [0, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [1, 2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h299 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 5 (7,131) (12,135) (I.realization.basis .sphere 7 131 1) (I.realization.basis .sphere 12 135 2) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 5, 7, 131, [1], 12, 135, [2], "S0_AdamsE2_ss", 2777⟩ (by
    exact List.mem_of_getElem? (i := 299) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (7,131) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source12
    (I : Inputs D L G) : Subsingleton ((sequence D .sphere).Page 6 (12,135))  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e12_135,he12_135⟩ := I.basis ⟨.sphere, 12, 135, ["408,1", "0,1,386,1", "0,2,69,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  change E.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e12_135
  change ∀i : Fin 3, e12_135.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 135 i.val at he12_135
  have h297 : HasDifferential E 3 (9,133) (12,135) (I.realization.basis .sphere 9 133 1 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 0) := sphere_named_differentials_hD7source_h297 I
  have h298 : HasDifferential E 3 (9,133) (12,135) (I.realization.basis .sphere 9 133 0 + I.realization.basis .sphere 9 133 2) (I.realization.basis .sphere 12 135 1 + I.realization.basis .sphere 12 135 2) := sphere_named_differentials_hD7source_h298 I
  have h299 : HasDifferential E 5 (7,131) (12,135) (I.realization.basis .sphere 7 131 1) (I.realization.basis .sphere 12 135 2) := sphere_named_differentials_hD7source_h299 I
  have hsub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)

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

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source13
    (I : Inputs D L G) : Subsingleton ((sequence D .sphere).Page 4 (13,136))  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e14_137,he14_137⟩ := I.basis ⟨.sphere, 14, 137, ["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀i : Fin 3, e14_137.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 137 i.val at he14_137
  obtain ⟨e13_136,he13_136⟩ := I.basis ⟨.sphere, 13, 136, ["418,1", "417,1", "0,2,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  change E.Page 2 (13,136) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e13_136
  change ∀i : Fin 3, e13_136.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 136 i.val at he13_136
  obtain ⟨e16_138,he16_138⟩ := I.basis ⟨.sphere, 16, 138, ["437,1", "23,1,189,1", "0,1,424,1"]⟩ (by
    exact List.mem_of_getElem? (i := 229) (by rfl))
  change E.Page 2 (16,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_138
  change ∀i : Fin 3, e16_138.symm (Finsupp.single i 1) = I.realization.basis .sphere 16 138 i.val at he16_138
  have h339 : HasDifferential E 3 (14,137) (17,139) (I.realization.basis .sphere 14 137 1) (I.realization.basis .sphere 17 139 1) := sphere_named_differentials_hD7source_h339 I
  have h340 : HasDifferential E 3 (14,137) (17,139) (I.realization.basis .sphere 14 137 0) (I.realization.basis .sphere 17 139 0) := sphere_named_differentials_hD7source_h340 I
  have h304 : HasDifferential E 2 (12,136) (14,137) (I.realization.basis .sphere 12 136 2) (I.realization.basis .sphere 14 137 2) := sphere_named_differentials_hD7source_h304 I
  have h319 : HasDifferential E 3 (13,136) (16,138) (I.realization.basis .sphere 13 136 1) (I.realization.basis .sphere 16 138 1) := sphere_named_differentials_hD7source_h319 I
  have h320 : HasDifferential E 3 (13,136) (16,138) (I.realization.basis .sphere 13 136 0) (I.realization.basis .sphere 16 138 0 + I.realization.basis .sphere 16 138 2) := sphere_named_differentials_hD7source_h320 I
  have h278 : HasDifferential E 2 (11,135) (13,136) (I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 13 136 2) := sphere_named_differentials_hD7source_h278 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
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

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source14
    (I : Inputs D L G) : Subsingleton ((sequence D .sphere).Page 4 (14,137))  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e15_138,he15_138⟩ := I.basis ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = I.realization.basis .sphere 15 138 i.val at he15_138
  obtain ⟨e14_137,he14_137⟩ := I.basis ⟨.sphere, 14, 137, ["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀i : Fin 3, e14_137.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 137 i.val at he14_137
  obtain ⟨e17_139,he17_139⟩ := I.basis ⟨.sphere, 17, 139, ["13,3,76,1", "0,1,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 237) (by rfl))
  change E.Page 2 (17,139) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e17_139
  change ∀i : Fin 2, e17_139.symm (Finsupp.single i 1) = I.realization.basis .sphere 17 139 i.val at he17_139
  have h654 : HasDifferential E 3 (15,138) (18,140) (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := sphere_named_differentials_hD7source_h654 I
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := sphere_named_differentials_hD7source_h250 I
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 15 138 0) := sphere_named_differentials_hD7source_h277 I
  have h339 : HasDifferential E 3 (14,137) (17,139) (I.realization.basis .sphere 14 137 1) (I.realization.basis .sphere 17 139 1) := sphere_named_differentials_hD7source_h339 I
  have h340 : HasDifferential E 3 (14,137) (17,139) (I.realization.basis .sphere 14 137 0) (I.realization.basis .sphere 17 139 0) := sphere_named_differentials_hD7source_h340 I
  have h304 : HasDifferential E 2 (12,136) (14,137) (I.realization.basis .sphere 12 136 2) (I.realization.basis .sphere 14 137 2) := sphere_named_differentials_hD7source_h304 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
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


private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_bne
    (I : KIP126.Computation.Route.Inputs D L G) : I.realization.basis .sphere 18 140 1 ≠ 0  := by
  classical
  let E := sequence D .sphere
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

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_bdne
    (I : KIP126.Computation.Route.Inputs D L G) : I.realization.basis .sphere 18 140 1-I.realization.basis .sphere 18 140 2 ≠ 0  := by
  classical
  let E := sequence D .sphere
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

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_third_image (I : KIP126.Computation.Route.Inputs D L G) :
    ∃ b : (sequence D .sphere).Page 3 (18,140),
    RepresentsOnPage (sequence D .sphere) 3 (18,140)
      (I.realization.basis .sphere 18 140 2) b ∧
    (∀ v : (sequence D .sphere).Page 3 (15,138),
      (sequence D .sphere).d 3 (15,138) v=0 ∨ (sequence D .sphere).d 3 (15,138) v=b) := by

  classical

  let E := sequence D .sphere
  obtain ⟨e15_138,he15_138⟩ := I.basis ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = I.realization.basis .sphere 15 138 i.val at he15_138
  have h654 : HasDifferential E 3 (15,138) (18,140) (I.realization.basis .sphere 15 138 2) (I.realization.basis .sphere 18 140 2) := sphere_named_differentials_hD7source_h654 I
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.realization.basis .sphere 10 134 3) (I.realization.basis .sphere 15 138 1) := sphere_named_differentials_hD7source_h250 I
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.realization.basis .sphere 11 135 1 + I.realization.basis .sphere 11 135 2) (I.realization.basis .sphere 15 138 0) := sphere_named_differentials_hD7source_h277 I
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

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero (I : Inputs D L G)
    {y4 : (sequence D .sphere).Page 4 (18,140)}
    (hy4 : RepresentsOnPage (sequence D .sphere) 4 (18,140)
      (I.realization.basis .sphere 18 140 1) y4) : y4 ≠ 0 := by
  classical
  let E := sequence D .sphere
  have d2_16 : E.d 2 (16,139)=0 := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_d2_16 I
  obtain ⟨b2,hb2,image3⟩ := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_third_image I
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hy4
  have bne : I.realization.basis .sphere 18 140 1 ≠ 0  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_bne I
  have bdne : I.realization.basis .sphere 18 140 1-I.realization.basis .sphere 18 140 2 ≠ 0  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_bdne I
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


private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero (I : Inputs D L G) :
  HasNonzeroDifferential (sequence D .sphere) 7 (11,134) (18,140)
    (I.realization.basis .sphere 11 134 0 + I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 18 140 1)  := by
  let E := sequence D .sphere
  have h656 : HasDifferential E 7 (11,134) (18,140) (I.realization.basis .sphere 11 134 0 + I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 18 140 1) := sphere_named_differentials_hD7source_h656 I
  have source14 : Subsingleton (E.Page 4 (14,137))  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source14 I
  have source13 : Subsingleton (E.Page 4 (13,136))  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source13 I
  have source12 : Subsingleton (E.Page 6 (12,135))  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source12 I
  obtain ⟨hdeg,x7,y7,hx7,hy7,hd7⟩ := h656
  obtain ⟨y4,hy4⟩ := represents_before (E := E) (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤7) hy7
  have y4ne : y4≠0 := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero I hy4
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


private theorem sphere_named_differentials_hD7source_label11_134_0 (I : Inputs D L G) : I.realization.sphere 11 134 (atom .x_123_11_2) = I.realization.basis .sphere 11 134 0  := by
  have hc := I.csv ⟨.sphere, 11, 134, ["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0 : Fin 5)
  have heq : (atom .x_123_11_2)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨387,by decide⟩ = projection (monomialOfString "387,1")
    have hs : "387,1" ≠ "" := by decide
    have hp : (("387,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [387,1] := by
      have split : "387,1".splitOn "," = ["387", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD7source_label11_134_1 (I : Inputs D L G) : I.realization.sphere 11 134 (atom .x_123_11) = I.realization.basis .sphere 11 134 1  := by
  have hc := I.csv ⟨.sphere, 11, 134, ["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (1 : Fin 5)
  have heq : (atom .x_123_11)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨386,by decide⟩ = projection (monomialOfString "386,1")
    have hs : "386,1" ≠ "" := by decide
    have hp : (("386,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [386,1] := by
      have split : "386,1".splitOn "," = ["386", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD7source_label11_134_3 (I : Inputs D L G) : I.realization.sphere 11 134 (mulAt (mulAt dataH0 dataH6) (atom .b4)) = I.realization.basis .sphere 11 134 3  := by
  have hc := I.csv ⟨.sphere, 11, 134, ["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (3 : Fin 5)
  have heq : (mulAt (mulAt dataH0 dataH6) (atom .b4))=z := by
    apply Subtype.ext
    rw [hz]
    change (generator ⟨0,by decide⟩ * generator ⟨69,by decide⟩) * generator ⟨80,by decide⟩ = projection (monomialOfString "0,1,69,1,80,1")
    have hs : "0,1,69,1,80,1" ≠ "" := by decide
    have hp : (("0,1,69,1,80,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,1,69,1,80,1] := by
      have split : "0,1,69,1,80,1".splitOn "," = ["0", "1", "69", "1", "80", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD7source_label18_140_1 (I : Inputs D L G) : I.realization.sphere 18 140 (mulAt dataH1 (atom .x_121_17)) = I.realization.basis .sphere 18 140 1  := by
  have hc := I.csv ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (1 : Fin 3)
  have heq : (mulAt dataH1 (atom .x_121_17))=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨1,by decide⟩ * generator ⟨436,by decide⟩ = projection (monomialOfString "1,1,436,1")
    have hs : "1,1,436,1" ≠ "" := by decide
    have hp : (("1,1,436,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1,1,436,1] := by
      have split : "1,1,436,1".splitOn "," = ["1", "1", "436", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD7source (I : Inputs D L G) : Derived.Differential I.realization 7 d7Source (mulAt dataH1 (atom .x_121_17)) := by
  classical
  have stem122_d7_target_nonzero :
    HasNonzeroDifferential (sequence D .sphere) 7 (11,134) (18,140)
      (I.realization.basis .sphere 11 134 0 + I.realization.basis .sphere 11 134 1 + I.realization.basis .sphere 11 134 3) (I.realization.basis .sphere 18 140 1)  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero I
  have label11_134_0 : I.realization.sphere 11 134 (atom .x_123_11_2) = I.realization.basis .sphere 11 134 0  := sphere_named_differentials_hD7source_label11_134_0 I
  have label11_134_1 : I.realization.sphere 11 134 (atom .x_123_11) = I.realization.basis .sphere 11 134 1  := sphere_named_differentials_hD7source_label11_134_1 I
  have label11_134_3 : I.realization.sphere 11 134 (mulAt (mulAt dataH0 dataH6) (atom .b4)) = I.realization.basis .sphere 11 134 3  := sphere_named_differentials_hD7source_label11_134_3 I
  have label18_140_1 : I.realization.sphere 18 140 (mulAt dataH1 (atom .x_121_17)) = I.realization.basis .sphere 18 140 1  := sphere_named_differentials_hD7source_label18_140_1 I
  change HasNonzeroDifferential (sequence D .sphere) 7 (11,134) (18,140)
    (I.realization.sphere 11 134 d7Source)
    (I.realization.sphere 18 140 (mulAt dataH1 (atom .x_121_17)))
  simp only [d7Source,map_add,label11_134_0,label11_134_1,label11_134_3,label18_140_1]
  exact stem122_d7_target_nonzero

private theorem sphere_named_differentials (I : Inputs D L G) :
    (Derived.Differential I.realization 3 (mulAt h0Sq (atom .x_123_13_2))
      (mulAt h0Sq (atom .x_122_16))) ∧
    (Derived.Differential I.realization 3 (atom .x_126_4) (mulAt h0Sq (atom .x_125_5))) ∧
    (Derived.Differential I.realization 7 d7Source (mulAt dataH1 (atom .x_121_17))) := by
  classical
  exact ⟨(sphere_named_differentials_hD3sq I), (sphere_named_differentials_hD3x1264 I), (sphere_named_differentials_hD7source I)⟩

private theorem pq_p_label (I : Inputs D L G)
    (hc0 : "2,1,79,1;0,1,89,1" ∈ RawData.relations) :
    I.realization.sphere 12 137 (mulAt P (atom .h2))=I.realization.basis .sphere 12 137 2 := by
  classical
  have hc := I.csv (⟨.sphere,12,137,["426,1","425,1","0,1,69,1,89,1","0,3,391,1","0,4,375,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 201) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (2:Fin 5)
  have hm0 : "0,1,69,1,89,1"≠"" := by decide
  have hm : (("0,1,69,1,89,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 1, 69, 1, 89, 1] := by
    have hs : "0,1,69,1,89,1".splitOn ","=["0", "1", "69", "1", "89", "1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    rw [hs]
    simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
      String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
  have hm : projection (monomialOfString "0,1,69,1,89,1")=generator ⟨0,by decide⟩*(generator ⟨69,by decide⟩*generator ⟨89,by decide⟩) := by
    norm_num [monomialOfString,hm,hm0,polynomialOfPowers,RawData.generatorCount,map_mul,map_pow,generator]
  have hv : mulAt P (atom .h2)=z := by
    apply Subtype.ext
    rw [hz]
    change (generator ⟨69,by decide⟩*generator ⟨79,by decide⟩)*generator ⟨2,by decide⟩=projection (monomialOfString "0,1,69,1,89,1")
    rw [hm]
    calc
      _ = generator ⟨69,by decide⟩*(generator ⟨2,by decide⟩*generator ⟨79,by decide⟩) := by ac_rfl
      _ = generator ⟨69,by decide⟩*(generator ⟨0,by decide⟩*generator ⟨89,by decide⟩) := by rw [pq_relation0 hc0]
      _ = _ := by ac_rfl
  rw [hv]
  exact he

private theorem pq_q_label (I : Inputs D L G)
    (hc1 : "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1" ∈ RawData.relations)
    (hc2 : "0,1,426,1;0,4,391,1" ∈ RawData.relations)
    (hc3 : "0,2,69,1,89,1;0,5,375,1" ∈ RawData.relations) :
    I.realization.sphere 13 138 (mulAt Q (atom .h2))=
      I.realization.basis .sphere 13 138 3+I.realization.basis .sphere 13 138 4 := by
  classical
  have hc := I.csv (⟨.sphere,13,138,["24,1,190,1","3,1,335,1","0,1,425,1","0,4,391,1","0,5,375,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 209) (by rfl)) rfl
  obtain ⟨z3,hz3,he3⟩ := hc (3:Fin 5)
  obtain ⟨z4,hz4,he4⟩ := hc (4:Fin 5)
  have hp30 : "0,4,391,1"≠"" := by decide
  have hp3 : (("0,4,391,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 4, 391, 1] := by
    have hs : "0,4,391,1".splitOn ","=["0", "4", "391", "1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    rw [hs]
    simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
      String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
  have hp40 : "0,5,375,1"≠"" := by decide
  have hp4 : (("0,5,375,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 5, 375, 1] := by
    have hs : "0,5,375,1".splitOn ","=["0", "5", "375", "1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    rw [hs]
    simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
      String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
  have hm3 : projection (monomialOfString "0,4,391,1")=generator ⟨0,by decide⟩^4*generator ⟨391,by decide⟩ := by
    norm_num [monomialOfString,hp3,hp30,polynomialOfPowers,RawData.generatorCount,map_mul,map_pow,generator]
  have hm4 : projection (monomialOfString "0,5,375,1")=generator ⟨0,by decide⟩^5*generator ⟨375,by decide⟩ := by
    norm_num [monomialOfString,hp4,hp40,polynomialOfPowers,RawData.generatorCount,map_mul,map_pow,generator]
  have hv : mulAt Q (atom .h2)=z3+z4 := by
    apply Subtype.ext
    change (generator ⟨18,by decide⟩*generator ⟨188,by decide⟩)*generator ⟨2,by decide⟩=z3.val+z4.val
    rw [hz3,hz4]
    change _=projection (monomialOfString "0,4,391,1")+projection (monomialOfString "0,5,375,1")
    rw [hm3,hm4]
    calc
      _ = generator ⟨2,by decide⟩*(generator ⟨18,by decide⟩*generator ⟨188,by decide⟩) := by ac_rfl
      _ = _ := (pq_relation1 hc1).trans (congrArg₂ (·+·) (pq_relation2 hc2) (pq_relation3 hc3))
  rw [hv,map_add,he3,he4]
  rfl

private theorem pq_p_boundary_h260 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,136) (12,137)
    ((I.realization.basis .sphere 10 136 0)) ((I.realization.basis .sphere 12 137 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,136,[0],12,137,[2],"S0_AdamsE2_ss",2859⟩ (by
    exact List.mem_of_getElem? (i := 260) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,136) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem pq_p_boundary (I : Inputs D L G)
    (hc0 : "2,1,79,1;0,1,89,1" ∈ RawData.relations) :
    IsBoundaryBy (sequence D .sphere) 2 (12,137)
      (I.realization.sphere 12 137 (mulAt P (atom .h2))) := by
  classical
  let E := sequence D .sphere
  have h260 : HasDifferential E 2 (10,136) (12,137)
      ((I.realization.basis .sphere 10 136 0)) ((I.realization.basis .sphere 12 137 2)) := pq_p_boundary_h260 I
  rw [pq_p_label I hc0]
  exact pq_rep3zero_boundary (differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h260)

private theorem pq_q_boundary_h288 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    ((I.realization.basis .sphere 11 137 0)) ((I.realization.basis .sphere 13 138 3)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
    exact List.mem_of_getElem? (i := 288) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,137) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem pq_q_boundary_h289 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    ((I.realization.basis .sphere 11 137 3)) ((I.realization.basis .sphere 13 138 4)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
    exact List.mem_of_getElem? (i := 289) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,137) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem pq_q_boundary (I : Inputs D L G)
    (hc1 : "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1" ∈ RawData.relations)
    (hc2 : "0,1,426,1;0,4,391,1" ∈ RawData.relations)
    (hc3 : "0,2,69,1,89,1;0,5,375,1" ∈ RawData.relations) :
    IsBoundaryBy (sequence D .sphere) 2 (13,138)
      (I.realization.sphere 13 138 (mulAt Q (atom .h2))) := by
  classical
  let E := sequence D .sphere
  have h288 : HasDifferential E 2 (11,137) (13,138)
      ((I.realization.basis .sphere 11 137 0)) ((I.realization.basis .sphere 13 138 3)) := pq_q_boundary_h288 I
  have h289 : HasDifferential E 2 (11,137) (13,138)
      ((I.realization.basis .sphere 11 137 3)) ((I.realization.basis .sphere 13 138 4)) := pq_q_boundary_h289 I
  rw [pq_q_label I hc1 hc2 hc3]
  apply pq_rep3zero_boundary
  simpa only [add_zero] using middle_add
    (differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h288)
    (differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h289)

private theorem sphere_product_obstructions_h180 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (7,70) (9,71)
    (I.realization.basis .sphere 7 70 2) (I.realization.basis .sphere 9 71 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,7,70,[2],9,71,[0],"S0_AdamsE2_ss",513⟩ (by
    exact List.mem_of_getElem? (i := 180) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,70) (9,71) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 70 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 71 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_product_obstructions_hD2H0six
    (I : Inputs D L G) : Derived.Differential I.realization 2 (mulAt h0Six dataH6) (mulAt dataH0 B)  := by
  classical

  have hmem := relation_member5
  let E := sequence D .sphere
  have hs : I.realization.sphere 7 70 (mulAt h0Six dataH6) = I.realization.basis .sphere 7 70 2 := by
    have hc := I.csv (⟨.sphere,7,70,["85,1", "84,1", "0,6,69,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 143) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (2:Fin 3)
    have heq : (mulAt h0Six dataH6)=z := by
      apply Subtype.ext
      rw [hz]
      change ((generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩))*generator ⟨69,by decide⟩ = projection (monomialOfString "0,6,69,1")
      have hp : (("0,6,69,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 6, 69, 1] := by
        have split : "0,6,69,1".splitOn "," = ["0", "6", "69", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "0,6,69,1"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have ht0 : I.realization.sphere 9 71 (mulAt (mulAt h0Six dataH0) h5Sq) = I.realization.basis .sphere 9 71 0 := by
    have hc := I.csv (⟨.sphere,9,71,["0,7,18,2"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 167) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
    have heq : (mulAt (mulAt h0Six dataH0) h5Sq)=z := by
      apply Subtype.ext
      rw [hz]
      change (((generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩))*generator ⟨0,by decide⟩)*(generator ⟨18,by decide⟩*generator ⟨18,by decide⟩) = projection (monomialOfString "0,7,18,2")
      have hp : (("0,7,18,2".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 7, 18, 2] := by
        have split : "0,7,18,2".splitOn "," = ["0", "7", "18", "2"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "0,7,18,2"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have hrel : mulAt dataH0 B = mulAt (mulAt h0Six dataH0) h5Sq := by
    apply Subtype.ext
    have hz := csv_relation_zero "0,1,82,1;0,7,18,2" hmem
    have hsplit : "0,1,82,1;0,7,18,2".splitOn ";" = ["0,1,82,1","0,7,18,2"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hp0 : (("0,1,82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 1, 82, 1] := by
      have split : "0,1,82,1".splitOn "," = ["0", "1", "82", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hp1 : (("0,7,18,2".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 7, 18, 2] := by
      have split : "0,7,18,2".splitOn "," = ["0", "7", "18", "2"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hneg (x : KIP126.LinE2.E2) : -x = x := by
      obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
      change -(projection p)=projection p
      rw [←map_neg]
      exact congrArg projection (CharTwo.neg_eq p)
    norm_num [relationPolynomial,hsplit,monomialOfString,hp0,hp1,polynomialOfPowers,
      RawData.generatorCount,generator,map_mul,map_add,pow_succ,mul_assoc] at hz
    have heq := (eq_neg_of_add_eq_zero_left hz).trans (hneg _)
    simpa [mulAt,dataH0,B,atom,h0Six,h0Sq,h5Sq,generator,h0,RawData.generatorCount,
      pow_succ,mul_assoc,map_mul] using heq
  have ht : I.realization.sphere 9 71 (mulAt dataH0 B) = I.realization.basis .sphere 9 71 0 := by
    rw [hrel]
    exact ht0
  have h180 : HasDifferential E 2 (7,70) (9,71)
      (I.realization.basis .sphere 7 70 2) (I.realization.basis .sphere 9 71 0) := sphere_product_obstructions_h180 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,71,["0,7,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 167) (by rfl))
  change E.Page 2 (9,71) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 71 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 9 71 0 := he 0
  change HasNonzeroDifferential E 2 (7,70) (9,71) _ _
  rw [hs,ht]
  obtain ⟨hd,x,y,hx,hy,hxy⟩ := h180
  refine ⟨hd,x,y,hx,hy,hxy,?_⟩
  rw [←hy.eq_on_page_two,←he0]
  intro h
  have hh := congrArg (fun x => e x 0) h
  simpa using hh

private theorem sphere_product_obstructions_hH5B
    (I : Inputs D L G) : I.realization.sphere 10 134 (mulAt h5Sq B)=0  := by
  classical

  have hmem := relation_member4
  have hcode : "18,1,82,1" ∈ RawData.relations := hmem
  have hz := csv_relation_zero _ hcode
  have hs : "18,1,82,1".splitOn ";" = ["18,1,82,1"] := by
    simp +decide [String.splitOn,String.splitOnAux]
  have hc : (("18,1,82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [18,1,82,1] := by
    have hsplit : "18,1,82,1".splitOn "," = ["18","1","82","1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    rw [hsplit]
    simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
      String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
  have hmul : generator ⟨18,by decide⟩ * generator ⟨82,by decide⟩ = 0 := by
    simpa [relationPolynomial,hs,monomialOfString,hc,polynomialOfPowers,
      RawData.generatorCount,generator,map_mul] using hz
  have h : mulAt h5Sq B = 0 := by
    apply Subtype.ext
    change (generator ⟨18,by decide⟩ * generator ⟨18,by decide⟩) * generator ⟨82,by decide⟩ = 0
    rw [mul_assoc,hmul,mul_zero]
  rw [h,map_zero]

private theorem sphere_product_obstructions_hH1Correction
    (I : Inputs D L G) : I.realization.sphere 14 139 (mulAt dataH1 correction)=0  := by
  classical

  have hm0 := relation_member6
  have hm1 := relation_member7
  have hm2 := relation_member8
  have hm3 := relation_member9
  have hm4 := relation_member1
  have hm5 := relation_member2
  have hm6 := relation_member3
  have pq_neg_eq_self (x : KIP126.LinE2.E2) : -x=x := by
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
    change -(projection p)=projection p
    rw [←map_neg]
    exact congrArg projection (CharTwo.neg_eq p)
  have pq_relation1 (hc : "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1" ∈ RawData.relations) :
      generator ⟨2,by decide⟩*(generator ⟨18,by decide⟩*generator ⟨188,by decide⟩) = generator ⟨0,by decide⟩*generator ⟨426,by decide⟩+generator ⟨0,by decide⟩^2*(generator ⟨69,by decide⟩*generator ⟨89,by decide⟩) := by
    have hz := csv_relation_zero "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1" hc
    have hs : "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1".splitOn ";"=["2,1,18,1,188,1", "0,1,426,1", "0,2,69,1,89,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hp00 : "2,1,18,1,188,1"≠"" := by decide
    have hp0 : (("2,1,18,1,188,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[2, 1, 18, 1, 188, 1] := by
      have hs : "2,1,18,1,188,1".splitOn ","=["2", "1", "18", "1", "188", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hp10 : "0,1,426,1"≠"" := by decide
    have hp1 : (("0,1,426,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 1, 426, 1] := by
      have hs : "0,1,426,1".splitOn ","=["0", "1", "426", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hp20 : "0,2,69,1,89,1"≠"" := by decide
    have hp2 : (("0,2,69,1,89,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 2, 69, 1, 89, 1] := by
      have hs : "0,2,69,1,89,1".splitOn ","=["0", "2", "69", "1", "89", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hp00,hp1,hp10,hp2,hp20,polynomialOfPowers,RawData.generatorCount,
      map_add,map_mul,map_pow,generator] at hz
    exact (eq_neg_of_add_eq_zero_left hz).trans (pq_neg_eq_self _)
  have pq_relation2 (hc : "0,1,426,1;0,4,391,1" ∈ RawData.relations) :
      generator ⟨0,by decide⟩*generator ⟨426,by decide⟩=generator ⟨0,by decide⟩^4*generator ⟨391,by decide⟩ := by
    have hz := csv_relation_zero "0,1,426,1;0,4,391,1" hc
    have hs : "0,1,426,1;0,4,391,1".splitOn ";"=["0,1,426,1", "0,4,391,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hp00 : "0,1,426,1"≠"" := by decide
    have hp0 : (("0,1,426,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 1, 426, 1] := by
      have hs : "0,1,426,1".splitOn ","=["0", "1", "426", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hp10 : "0,4,391,1"≠"" := by decide
    have hp1 : (("0,4,391,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 4, 391, 1] := by
      have hs : "0,4,391,1".splitOn ","=["0", "4", "391", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hp00,hp1,hp10,polynomialOfPowers,RawData.generatorCount,
      map_add,map_mul,map_pow,generator] at hz
    exact (eq_neg_of_add_eq_zero_left hz).trans (pq_neg_eq_self _)
  have pq_relation3 (hc : "0,2,69,1,89,1;0,5,375,1" ∈ RawData.relations) :
      generator ⟨0,by decide⟩^2*(generator ⟨69,by decide⟩*generator ⟨89,by decide⟩)=generator ⟨0,by decide⟩^5*generator ⟨375,by decide⟩ := by
    have hz := csv_relation_zero "0,2,69,1,89,1;0,5,375,1" hc
    have hs : "0,2,69,1,89,1;0,5,375,1".splitOn ";"=["0,2,69,1,89,1", "0,5,375,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hp00 : "0,2,69,1,89,1"≠"" := by decide
    have hp0 : (("0,2,69,1,89,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 2, 69, 1, 89, 1] := by
      have hs : "0,2,69,1,89,1".splitOn ","=["0", "2", "69", "1", "89", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hp10 : "0,5,375,1"≠"" := by decide
    have hp1 : (("0,5,375,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 5, 375, 1] := by
      have hs : "0,5,375,1".splitOn ","=["0", "5", "375", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hp00,hp1,hp10,polynomialOfPowers,RawData.generatorCount,
      map_add,map_mul,map_pow,generator] at hz
    exact (eq_neg_of_add_eq_zero_left hz).trans (pq_neg_eq_self _)
  have corr_relation0 (hc : "2,1,239,1;1,1,251,1" ∈ RawData.relations) :
      (generator ⟨2,by decide⟩ * generator ⟨239,by decide⟩) = (generator ⟨1,by decide⟩ * generator ⟨251,by decide⟩) := by
    have hz := csv_relation_zero "2,1,239,1;1,1,251,1" hc
    have hs : "2,1,239,1;1,1,251,1".splitOn ";"=["2,1,239,1", "1,1,251,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hne0 : "2,1,239,1" ≠ "" := by decide
    have hp0 : (("2,1,239,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[2, 1, 239, 1] := by
      have split : "2,1,239,1".splitOn ","=["2", "1", "239", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hne1 : "1,1,251,1" ≠ "" := by decide
    have hp1 : (("1,1,251,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[1, 1, 251, 1] := by
      have split : "1,1,251,1".splitOn ","=["1", "1", "251", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hne0,hp1,hne1,polynomialOfPowers,RawData.generatorCount,map_add,map_mul,map_pow,generator] at hz
    simpa [mul_assoc,generator,RawData.generatorCount] using (eq_neg_of_add_eq_zero_left hz).trans (pq_neg_eq_self _)
  have corr_relation1 (hc : "9,1,239,1;0,1,18,1,188,1" ∈ RawData.relations) :
      (generator ⟨9,by decide⟩ * generator ⟨239,by decide⟩) = (generator ⟨0,by decide⟩ * generator ⟨18,by decide⟩ * generator ⟨188,by decide⟩) := by
    have hz := csv_relation_zero "9,1,239,1;0,1,18,1,188,1" hc
    have hs : "9,1,239,1;0,1,18,1,188,1".splitOn ";"=["9,1,239,1", "0,1,18,1,188,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hne0 : "9,1,239,1" ≠ "" := by decide
    have hp0 : (("9,1,239,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[9, 1, 239, 1] := by
      have split : "9,1,239,1".splitOn ","=["9", "1", "239", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hne1 : "0,1,18,1,188,1" ≠ "" := by decide
    have hp1 : (("0,1,18,1,188,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 1, 18, 1, 188, 1] := by
      have split : "0,1,18,1,188,1".splitOn ","=["0", "1", "18", "1", "188", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hne0,hp1,hne1,polynomialOfPowers,RawData.generatorCount,map_add,map_mul,map_pow,generator] at hz
    simpa [mul_assoc,generator,RawData.generatorCount] using (eq_neg_of_add_eq_zero_left hz).trans (pq_neg_eq_self _)
  have corr_relation2 (hc : "0,5,391,1" ∈ RawData.relations) :
      (generator ⟨0,by decide⟩^5 * generator ⟨391,by decide⟩) = 0 := by
    have hz := csv_relation_zero "0,5,391,1" hc
    have hs : "0,5,391,1".splitOn ";"=["0,5,391,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hne0 : "0,5,391,1" ≠ "" := by decide
    have hp0 : (("0,5,391,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 5, 391, 1] := by
      have split : "0,5,391,1".splitOn ","=["0", "5", "391", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hne0,polynomialOfPowers,RawData.generatorCount,map_add,map_mul,map_pow,generator] at hz
    simpa [mul_assoc,generator,RawData.generatorCount] using hz
  have corr_relation3 (hc : "0,6,375,1" ∈ RawData.relations) :
      (generator ⟨0,by decide⟩^6 * generator ⟨375,by decide⟩) = 0 := by
    have hz := csv_relation_zero "0,6,375,1" hc
    have hs : "0,6,375,1".splitOn ";"=["0,6,375,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hne0 : "0,6,375,1" ≠ "" := by decide
    have hp0 : (("0,6,375,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 6, 375, 1] := by
      have split : "0,6,375,1".splitOn ","=["0", "6", "375", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hne0,polynomialOfPowers,RawData.generatorCount,map_add,map_mul,map_pow,generator] at hz
    simpa [mul_assoc,generator,RawData.generatorCount] using hz
  have h : mulAt dataH1 correction=0 := by
    apply Subtype.ext
    let g (i : Fin RawData.generatorCount) := generator i
    change g ⟨1,by decide⟩ * (g ⟨9,by decide⟩ * g ⟨251,by decide⟩)=0
    have h0 := corr_relation0 hm0
    have h1 := corr_relation1 hm1
    have h2 := corr_relation2 hm2
    have h3 := corr_relation3 hm3
    have h4 := pq_relation1 hm4
    have h5 := pq_relation2 hm5
    have h6 := pq_relation3 hm6
    change g ⟨2,by decide⟩*g ⟨239,by decide⟩=g ⟨1,by decide⟩*g ⟨251,by decide⟩ at h0
    change g ⟨9,by decide⟩*g ⟨239,by decide⟩=g ⟨0,by decide⟩*g ⟨18,by decide⟩*g ⟨188,by decide⟩ at h1
    change g ⟨0,by decide⟩^5*g ⟨391,by decide⟩=0 at h2
    change g ⟨0,by decide⟩^6*g ⟨375,by decide⟩=0 at h3
    change g ⟨2,by decide⟩*(g ⟨18,by decide⟩*g ⟨188,by decide⟩)=g ⟨0,by decide⟩*g ⟨426,by decide⟩+g ⟨0,by decide⟩^2*(g ⟨69,by decide⟩*g ⟨89,by decide⟩) at h4
    change g ⟨0,by decide⟩*g ⟨426,by decide⟩=g ⟨0,by decide⟩^4*g ⟨391,by decide⟩ at h5
    change g ⟨0,by decide⟩^2*(g ⟨69,by decide⟩*g ⟨89,by decide⟩)=g ⟨0,by decide⟩^5*g ⟨375,by decide⟩ at h6
    calc
      _ = g ⟨9,by decide⟩*(g ⟨1,by decide⟩*g ⟨251,by decide⟩) := by ac_rfl
      _ = g ⟨9,by decide⟩*(g ⟨2,by decide⟩*g ⟨239,by decide⟩) := by rw [←h0]
      _ = g ⟨2,by decide⟩*(g ⟨9,by decide⟩*g ⟨239,by decide⟩) := by ac_rfl
      _ = g ⟨2,by decide⟩*(g ⟨0,by decide⟩*g ⟨18,by decide⟩*g ⟨188,by decide⟩) := by rw [h1]
      _ = g ⟨0,by decide⟩*(g ⟨2,by decide⟩*(g ⟨18,by decide⟩*g ⟨188,by decide⟩)) := by ac_rfl
      _ = g ⟨0,by decide⟩*(g ⟨0,by decide⟩*g ⟨426,by decide⟩+g ⟨0,by decide⟩^2*(g ⟨69,by decide⟩*g ⟨89,by decide⟩)) := by rw [h4]
      _ = g ⟨0,by decide⟩*(g ⟨0,by decide⟩^4*g ⟨391,by decide⟩+g ⟨0,by decide⟩^5*g ⟨375,by decide⟩) := by rw [h5,h6]
      _ = g ⟨0,by decide⟩^5*g ⟨391,by decide⟩+g ⟨0,by decide⟩^6*g ⟨375,by decide⟩ := by ring
      _ = 0 := by rw [h2,h3,add_zero]
  rw [h,map_zero]

private def h0_product_map : E2 H SphereSpectrum 13 138 →ₗ[ℤ] E2 H SphereSpectrum 14 139 where
  toFun := Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138)
    (Sphere.Internal.hi H M 0)
  map_add' := Sphere.Internal.product_add_right H M (s := 1) (t := 1) (s' := 13) (t' := 138) (Sphere.Internal.hi H M 0)
  map_smul' := by
    intro n a
    have hs := int_smul_eq_zsmul (ModuleCat.isModule (E2 H SphereSpectrum 13 138)) n a
    have ht := int_smul_eq_zsmul (ModuleCat.isModule (E2 H SphereSpectrum 14 139)) n
      (Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138) (Sphere.Internal.hi H M 0) a)
    exact (congrArg (Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138)
      (Sphere.Internal.hi H M 0)) hs).trans
        ((Sphere.Internal.product_zsmul_right H M (s := 1) (t := 1) (s' := 13) (t' := 138)
          (Sphere.Internal.hi H M 0) a n).trans ht.symm)


private theorem h0_product_map_apply (a : E2 H SphereSpectrum 13 138) :
    h0_product_map (H := H) (M := M) a = Sphere.Internal.product H M
      (s := 1) (t := 1) (s' := 13) (t' := 138) (Sphere.Internal.hi H M 0) a := rfl


attribute [local irreducible] h0_product_map

private theorem sphere_product_obstructions_hTnotH0
    (I : Inputs D L G) : ¬ ∃ a : E2 H SphereSpectrum 13 138,
      Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138)
        (Sphere.Internal.hi H M 0) a = I.realization.sphere 14 139 T  := by
  classical

  have hc0 := relation_member10
  have hc1 := relation_member11
  have hc2 := relation_member8
  have hc3 := relation_member9
  classical
  let E := sequence D .sphere
  have rel0 : (generator ⟨0,by decide⟩)*(generator ⟨24,by decide⟩)=0 := h0_obstruction_rel0
  have rel1 : (generator ⟨0,by decide⟩)*(generator ⟨3,by decide⟩)*(generator ⟨335,by decide⟩)=(generator ⟨0,by decide⟩^2)*(generator ⟨425,by decide⟩) := h0_obstruction_rel1
  have rel2 : (generator ⟨0,by decide⟩^5)*(generator ⟨391,by decide⟩)=0 := h0_obstruction_rel2
  have rel3 : (generator ⟨0,by decide⟩^6)*(generator ⟨375,by decide⟩)=0 := h0_obstruction_rel3
  obtain ⟨e13_138,he13_138⟩ := I.basis ⟨.sphere, 13, 138, ["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 209) (by rfl))
  change E2 H SphereSpectrum 13 138 ≃ₗ[ℤ] (Fin 5 →₀ F2) at e13_138
  change ∀i : Fin 5, e13_138.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 138 i.val at he13_138
  obtain ⟨e14_139,he14_139⟩ := I.basis ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl))
  change E2 H SphereSpectrum 14 139 ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_139
  change ∀i : Fin 3, e14_139.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 139 i.val at he14_139
  have hcsv := I.csv ⟨.sphere, 13, 138, ["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 209) (by rfl)) rfl
  choose z hz he using hcsv
  change Fin 5 → E2At 13 138 at z
  change ∀ i : Fin 5, I.realization.sphere 13 138 (z i) = I.realization.basis .sphere 13 138 i.val at he
  have mon0 : projection (monomialOfString "24,1,190,1") = (generator ⟨24,by decide⟩)*(generator ⟨190,by decide⟩) := h0_obstruction_mon0
  have zv0 : (z (0 : Fin 5)).val = (generator ⟨24,by decide⟩)*(generator ⟨190,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon0
  have mon1 : projection (monomialOfString "3,1,335,1") = (generator ⟨3,by decide⟩)*(generator ⟨335,by decide⟩) := h0_obstruction_mon1
  have zv1 : (z (1 : Fin 5)).val = (generator ⟨3,by decide⟩)*(generator ⟨335,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon1
  have mon2 : projection (monomialOfString "0,1,425,1") = (generator ⟨0,by decide⟩)*(generator ⟨425,by decide⟩) := h0_obstruction_mon2
  have zv2 : (z (2 : Fin 5)).val = (generator ⟨0,by decide⟩)*(generator ⟨425,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon2
  have mon3 : projection (monomialOfString "0,4,391,1") = (generator ⟨0,by decide⟩^4)*(generator ⟨391,by decide⟩) := h0_obstruction_mon3
  have zv3 : (z (3 : Fin 5)).val = (generator ⟨0,by decide⟩^4)*(generator ⟨391,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon3
  have mon4 : projection (monomialOfString "0,5,375,1") = (generator ⟨0,by decide⟩^5)*(generator ⟨375,by decide⟩) := h0_obstruction_mon4
  have zv4 : (z (4 : Fin 5)).val = (generator ⟨0,by decide⟩^5)*(generator ⟨375,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon4
  have monT : projection (monomialOfString "1,1,7,1,275,1") = (generator ⟨1,by decide⟩)*(generator ⟨7,by decide⟩)*(generator ⟨275,by decide⟩) := h0_obstruction_monT
  have targetCSV := I.csv ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl)) rfl
  have labelT : I.realization.sphere 14 139 T = I.realization.basis .sphere 14 139 1 := by
    as_aux_lemma =>
      obtain ⟨y,hy,heq⟩ := targetCSV (1 : Fin 3)
      have hyT : T=y := by
        as_aux_lemma =>
          apply Subtype.ext
          rw [hy]
          change generator ⟨1,by decide⟩*(generator ⟨7,by decide⟩*generator ⟨275,by decide⟩)=projection (monomialOfString "1,1,7,1,275,1")
          rw [monT]
          exact (mul_assoc _ _ _).symm
      rw [hyT]
      exact heq
  let f := h0_product_map (H := H) (M := M)
  have hf (a : E2 H SphereSpectrum 13 138) : f a = Sphere.Internal.product H M
      (s := 1) (t := 1) (s' := 13) (t' := 138) (Sphere.Internal.hi H M 0) a := h0_product_map_apply a
  have hprod (i : Fin 5) : f (I.realization.basis .sphere 13 138 i.val) =
      I.realization.sphere 14 139 (mulAt (dataH0) (z i)) := by
    as_aux_lemma =>
      rw [←he i,hf,←I.labels.h0]
      exact (I.products ⟨1,1,13,138⟩ (by simp [Raw.products]) (dataH0) (z i)).symm
  obtain ⟨y2,hy2,hey2⟩ := targetCSV (2 : Fin 3)
  have monTarget2 : projection (monomialOfString "0,2,425,1") = (generator ⟨0,by decide⟩^2)*(generator ⟨425,by decide⟩) := h0_obstruction_monTarget2
  have mul0 : mulAt dataH0 (z (0 : Fin 5))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨0,by decide⟩*(z (0 : Fin 5)).val=0
      rw [zv0,←mul_assoc,rel0,zero_mul]
  have mul1 : mulAt dataH0 (z (1 : Fin 5))=y2 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨0,by decide⟩*(z (1 : Fin 5)).val=y2.val
      rw [zv1,hy2]
      change _=projection (monomialOfString "0,2,425,1")
      rw [monTarget2]
      simpa only [mul_assoc] using rel1
  have mul2 : mulAt dataH0 (z (2 : Fin 5))=y2 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨0,by decide⟩*(z (2 : Fin 5)).val=y2.val
      rw [zv2,hy2]
      change _=projection (monomialOfString "0,2,425,1")
      rw [monTarget2]
      ring
  have mul3 : mulAt dataH0 (z (3 : Fin 5))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨0,by decide⟩*(z (3 : Fin 5)).val=0
      rw [zv3]
      calc
        _=generator ⟨0,by decide⟩^5*generator ⟨391,by decide⟩ := by ring
        _=0 := rel2
  have mul4 : mulAt dataH0 (z (4 : Fin 5))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨0,by decide⟩*(z (4 : Fin 5)).val=0
      rw [zv4]
      calc
        _=generator ⟨0,by decide⟩^6*generator ⟨375,by decide⟩ := by ring
        _=0 := rel3
  have target2coord : (e14_139 (I.realization.basis .sphere 14 139 2)) 1=0 := by
    as_aux_lemma =>
      rw [show I.realization.basis .sphere 14 139 2=e14_139.symm (Finsupp.single 2 1) from (he14_139 2).symm,
        LinearEquiv.apply_symm_apply]
      simp [Finsupp.single_apply,show (2 : Fin 3)≠1 by decide]
  have basisCoord (i : Fin 5) : (e14_139 (f (e13_138.symm (Finsupp.single i 1)))) 1=0 := by
    as_aux_lemma =>
      rw [he13_138,hprod]
      fin_cases i
      · change (e14_139 (I.realization.sphere 14 139 (mulAt dataH0 (z (0 : Fin 5))))) 1=0
        rw [mul0]
        rw [map_zero,map_zero]
        rfl
      · change (e14_139 (I.realization.sphere 14 139 (mulAt dataH0 (z (1 : Fin 5))))) 1=0
        rw [mul1]
        rw [hey2]
        exact target2coord
      · change (e14_139 (I.realization.sphere 14 139 (mulAt dataH0 (z (2 : Fin 5))))) 1=0
        rw [mul2]
        rw [hey2]
        exact target2coord
      · change (e14_139 (I.realization.sphere 14 139 (mulAt dataH0 (z (3 : Fin 5))))) 1=0
        rw [mul3]
        rw [map_zero,map_zero]
        rfl
      · change (e14_139 (I.realization.sphere 14 139 (mulAt dataH0 (z (4 : Fin 5))))) 1=0
        rw [mul4]
        rw [map_zero,map_zero]
        rfl
  have allCoord (a : E2 H SphereSpectrum 13 138) : (e14_139 (f a)) 1=0 := by
    as_aux_lemma =>
      rw [finite_basis_expansion e13_138 a,map_sum,map_sum,Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hc : (e13_138 a) i=0
      · simp only [hc,ite_true,map_zero,Finsupp.zero_apply]
      · simpa only [hc,ite_false] using basisCoord i
  rintro ⟨a,ha⟩
  have hz := allCoord a
  rw [hf,ha,labelT] at hz
  rw [show I.realization.basis .sphere 14 139 1=e14_139.symm (Finsupp.single 1 1) from (he14_139 1).symm,
    LinearEquiv.apply_symm_apply,Finsupp.single_eq_same] at hz
  exact one_ne_zero hz

private def h2_product_map : E2 H SphereSpectrum 13 135 →ₗ[ℤ] E2 H SphereSpectrum 14 139 where
  toFun := Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135)
    (Sphere.Internal.hi H M 2)
  map_add' := Sphere.Internal.product_add_right H M (s := 1) (t := 4) (s' := 13) (t' := 135) (Sphere.Internal.hi H M 2)
  map_smul' := by
    intro n a
    have hs := int_smul_eq_zsmul (ModuleCat.isModule (E2 H SphereSpectrum 13 135)) n a
    have ht := int_smul_eq_zsmul (ModuleCat.isModule (E2 H SphereSpectrum 14 139)) n
      (Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135) (Sphere.Internal.hi H M 2) a)
    exact (congrArg (Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135)
      (Sphere.Internal.hi H M 2)) hs).trans
        ((Sphere.Internal.product_zsmul_right H M (s := 1) (t := 4) (s' := 13) (t' := 135)
          (Sphere.Internal.hi H M 2) a n).trans ht.symm)


private theorem h2_product_map_apply (a : E2 H SphereSpectrum 13 135) :
    h2_product_map (H := H) (M := M) a = Sphere.Internal.product H M
      (s := 1) (t := 4) (s' := 13) (t' := 135) (Sphere.Internal.hi H M 2) a := rfl


attribute [local irreducible] h2_product_map

private theorem sphere_product_obstructions_hTnotH2
    (I : Inputs D L G) : ¬ ∃ a : E2 H SphereSpectrum 13 135,
      Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135)
        (Sphere.Internal.hi H M 2) a = I.realization.sphere 14 139 T  := by
  classical

  have hc0 := relation_member12
  have hc1 := relation_member0
  have hc2 := relation_member13
  classical
  let E := sequence D .sphere
  have rel0 : (generator ⟨2,by decide⟩)*(generator ⟨407,by decide⟩)=0 := h2_obstruction_rel0
  have rel1 : (generator ⟨2,by decide⟩)*(generator ⟨79,by decide⟩)=(generator ⟨0,by decide⟩)*(generator ⟨89,by decide⟩) := h2_obstruction_rel1
  have rel2 : (generator ⟨0,by decide⟩^3)*(generator ⟨89,by decide⟩)=0 := h2_obstruction_rel2
  obtain ⟨e13_135,he13_135⟩ := I.basis ⟨.sphere, 13, 135, ["407,1", "1,2,351,1", "0,2,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 206) (by rfl))
  change E2 H SphereSpectrum 13 135 ≃ₗ[ℤ] (Fin 3 →₀ F2) at e13_135
  change ∀i : Fin 3, e13_135.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 135 i.val at he13_135
  obtain ⟨e14_139,he14_139⟩ := I.basis ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl))
  change E2 H SphereSpectrum 14 139 ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_139
  change ∀i : Fin 3, e14_139.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 139 i.val at he14_139
  have hcsv := I.csv ⟨.sphere, 13, 135, ["407,1", "1,2,351,1", "0,2,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 206) (by rfl)) rfl
  choose z hz he using hcsv
  change Fin 3 → E2At 13 135 at z
  change ∀ i : Fin 3, I.realization.sphere 13 135 (z i) = I.realization.basis .sphere 13 135 i.val at he
  have mon0 : projection (monomialOfString "407,1") = (generator ⟨407,by decide⟩) := h2_obstruction_mon0
  have zv0 : (z (0 : Fin 3)).val = (generator ⟨407,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon0
  have mon1 : projection (monomialOfString "1,2,351,1") = (generator ⟨1,by decide⟩^2)*(generator ⟨351,by decide⟩) := h2_obstruction_mon1
  have zv1 : (z (1 : Fin 3)).val = (generator ⟨1,by decide⟩^2)*(generator ⟨351,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon1
  have mon2 : projection (monomialOfString "0,2,69,1,79,1") = (generator ⟨0,by decide⟩^2)*(generator ⟨69,by decide⟩)*(generator ⟨79,by decide⟩) := h2_obstruction_mon2
  have zv2 : (z (2 : Fin 3)).val = (generator ⟨0,by decide⟩^2)*(generator ⟨69,by decide⟩)*(generator ⟨79,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon2
  have monT : projection (monomialOfString "1,1,7,1,275,1") = (generator ⟨1,by decide⟩)*(generator ⟨7,by decide⟩)*(generator ⟨275,by decide⟩) := h2_obstruction_monT
  have targetCSV := I.csv ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl)) rfl
  have labelT : I.realization.sphere 14 139 T = I.realization.basis .sphere 14 139 1 := by
    as_aux_lemma =>
      obtain ⟨y,hy,heq⟩ := targetCSV (1 : Fin 3)
      have hyT : T=y := by
        as_aux_lemma =>
          apply Subtype.ext
          rw [hy]
          change generator ⟨1,by decide⟩*(generator ⟨7,by decide⟩*generator ⟨275,by decide⟩)=projection (monomialOfString "1,1,7,1,275,1")
          rw [monT]
          exact (mul_assoc _ _ _).symm
      rw [hyT]
      exact heq
  let f := h2_product_map (H := H) (M := M)
  have hf (a : E2 H SphereSpectrum 13 135) : f a = Sphere.Internal.product H M
      (s := 1) (t := 4) (s' := 13) (t' := 135) (Sphere.Internal.hi H M 2) a := h2_product_map_apply a
  have hprod (i : Fin 3) : f (I.realization.basis .sphere 13 135 i.val) =
      I.realization.sphere 14 139 (mulAt (atom .h2) (z i)) := by
    as_aux_lemma =>
      rw [←he i,hf,←I.labels.h2]
      exact (I.products ⟨1,4,13,135⟩ (by simp [Raw.products]) (atom .h2) (z i)).symm
  have mul0 : mulAt (atom .h2) (z (0 : Fin 3))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨2,by decide⟩*(z (0 : Fin 3)).val=0
      rw [zv0]
      exact rel0
  have mul1 : mulAt (atom .h2) (z (1 : Fin 3))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨2,by decide⟩*(z (1 : Fin 3)).val=0
      rw [zv1]
      have h12 : generator ⟨1,by decide⟩*generator ⟨2,by decide⟩=0 := h1_mul_h2_eq_zero
      calc
        _=(generator ⟨1,by decide⟩*generator ⟨2,by decide⟩)*
          (generator ⟨1,by decide⟩*generator ⟨351,by decide⟩) := by ring
        _=0 := by rw [h12,zero_mul]
  have mul2 : mulAt (atom .h2) (z (2 : Fin 3))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨2,by decide⟩*(z (2 : Fin 3)).val=0
      rw [zv2]
      calc
        _=generator ⟨0,by decide⟩^2*generator ⟨69,by decide⟩*
          (generator ⟨2,by decide⟩*generator ⟨79,by decide⟩) := by ring
        _=generator ⟨0,by decide⟩^2*generator ⟨69,by decide⟩*
          (generator ⟨0,by decide⟩*generator ⟨89,by decide⟩) := by rw [rel1]
        _=generator ⟨69,by decide⟩*(generator ⟨0,by decide⟩^3*generator ⟨89,by decide⟩) := by ring
        _=0 := by rw [rel2,mul_zero]
  have basisCoord (i : Fin 3) : (e14_139 (f (e13_135.symm (Finsupp.single i 1)))) 1=0 := by
    as_aux_lemma =>
      rw [he13_135,hprod]
      fin_cases i
      · change (e14_139 (I.realization.sphere 14 139 (mulAt (atom .h2) (z (0 : Fin 3))))) 1=0
        rw [mul0,map_zero,map_zero]
        rfl
      · change (e14_139 (I.realization.sphere 14 139 (mulAt (atom .h2) (z (1 : Fin 3))))) 1=0
        rw [mul1,map_zero,map_zero]
        rfl
      · change (e14_139 (I.realization.sphere 14 139 (mulAt (atom .h2) (z (2 : Fin 3))))) 1=0
        rw [mul2,map_zero,map_zero]
        rfl
  have allCoord (a : E2 H SphereSpectrum 13 135) : (e14_139 (f a)) 1=0 := by
    as_aux_lemma =>
      rw [finite_basis_expansion e13_135 a,map_sum,map_sum,Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hc : (e13_135 a) i=0
      · simp only [hc,ite_true,map_zero,Finsupp.zero_apply]
      · simpa only [hc,ite_false] using basisCoord i
  rintro ⟨a,ha⟩
  have hz := allCoord a
  rw [hf,ha,labelT] at hz
  rw [show I.realization.basis .sphere 14 139 1=e14_139.symm (Finsupp.single 1 1) from (he14_139 1).symm,
    LinearEquiv.apply_symm_apply,Finsupp.single_eq_same] at hz
  exact one_ne_zero hz

private theorem sphere_product_obstructions (I : Inputs D L G) :
    (Derived.Differential I.realization 2 (mulAt h0Six dataH6) (mulAt dataH0 B)) ∧
    (I.realization.sphere 10 134 (mulAt h5Sq B)=0) ∧
    (I.realization.sphere 14 139 (mulAt dataH1 correction)=0) ∧
    (IsBoundaryBy (sequence D .sphere) 2 (12,137)
      (I.realization.sphere 12 137 (mulAt P (atom .h2)))) ∧
    (IsBoundaryBy (sequence D .sphere) 2 (13,138)
      (I.realization.sphere 13 138 (mulAt Q (atom .h2)))) ∧
    (¬ ∃ a : E2 H SphereSpectrum 13 138,
      Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138)
        (Sphere.Internal.hi H M 0) a = I.realization.sphere 14 139 T) ∧
    (¬ ∃ a : E2 H SphereSpectrum 13 135,
      Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135)
        (Sphere.Internal.hi H M 2) a = I.realization.sphere 14 139 T) := by
  classical
  have hD2H0six : Derived.Differential I.realization 2 (mulAt h0Six dataH6) (mulAt dataH0 B)  := sphere_product_obstructions_hD2H0six I
  have hH5B : I.realization.sphere 10 134 (mulAt h5Sq B)=0  := sphere_product_obstructions_hH5B I
  have hH1Correction : I.realization.sphere 14 139 (mulAt dataH1 correction)=0  := sphere_product_obstructions_hH1Correction I
  have p_h2_boundary : IsBoundaryBy (sequence D .sphere) 2 (12,137)
      (I.realization.sphere 12 137 (mulAt P (atom .h2))) :=
    pq_p_boundary I relation_member0
  have q_h2_boundary : IsBoundaryBy (sequence D .sphere) 2 (13,138)
      (I.realization.sphere 13 138 (mulAt Q (atom .h2))) :=
    pq_q_boundary I relation_member1 relation_member2 relation_member3
  have hTnotH0 : ¬ ∃ a : E2 H SphereSpectrum 13 138,
      Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138)
        (Sphere.Internal.hi H M 0) a = I.realization.sphere 14 139 T  := sphere_product_obstructions_hTnotH0 I
  have hTnotH2 : ¬ ∃ a : E2 H SphereSpectrum 13 135,
      Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135)
        (Sphere.Internal.hi H M 2) a = I.realization.sphere 14 139 T  := sphere_product_obstructions_hTnotH2 I
  exact ⟨hD2H0six, hH5B, hH1Correction, p_h2_boundary, q_h2_boundary, hTnotH0, hTnotH2⟩

private theorem t_label (I : Inputs D L G) :
    I.realization.sphere 14 139 T = I.realization.basis .sphere 14 139 1 := by
  classical
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


private theorem t_permanent_cycle_h342 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (14,139) (I.realization.basis .sphere 14 139 1) := by
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

private theorem t_permanent_cycle (I : Inputs D L G) (V : SphereVanishingLine H) :
    IsPermanentCycle (sequence D .sphere) (14,139) (I.realization.sphere 14 139 T) := by
  classical
  let E := sequence D .sphere
  have h342 : ReachesPage E 1000 (14,139) (I.realization.basis .sphere 14 139 1) := t_permanent_cycle_h342 I
  rw [t_label I]
  apply isPermanentCycle_of_reachesPage E 1000 (by change (2:ℤ)≤1000; omega) (14,139) _ h342
  intro r hr
  haveI : Subsingleton (E.Page r ((14,139)+E.diffDeg r)) := by
    change Subsingleton (E.Page r ((14:ℤ)+r,(139:ℤ)+(r-1)))
    exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r (14+r) (139+(r-1))
      (by decide) (by omega) (V _ _ (by omega) (by omega))
  ext x
  exact Subsingleton.elim _ _


private theorem w_to_e6_h152 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 14 (3,130) (I.realization.basis .sphere 3 130 0) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,14,3,130,[0],3,130,[],"S0_AdamsE2_ss",2438⟩ (by
    exact List.mem_of_getElem? (i := 152) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 14 (3,130) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [0] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h175 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 4 (6,133) (I.realization.basis .sphere 6 133 0) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,4,6,133,[0],6,133,[],"S0_AdamsE2_ss",2633⟩ (by
    exact List.mem_of_getElem? (i := 175) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 4 (6,133) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [0] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h204 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 6 (8,134) (I.realization.basis .sphere 8 134 0 + I.realization.basis .sphere 8 134 3) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,6,8,134,[0, 3],8,134,[],"S0_AdamsE2_ss",2702⟩ (by
    exact List.mem_of_getElem? (i := 204) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 6 (8,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [0, 3] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h153 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (3,130) (5,131)
    (I.realization.basis .sphere 3 130 1) (I.realization.basis .sphere 5 131 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,3,130,[1],5,131,[0],"S0_AdamsE2_ss",2439⟩ (by
    exact List.mem_of_getElem? (i := 153) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (3,130) (5,131) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 5 131 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h158 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (4,131) (6,132)
    (I.realization.basis .sphere 4 131 0) (I.realization.basis .sphere 6 132 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,4,131,[0],6,132,[1],"S0_AdamsE2_ss",2495⟩ (by
    exact List.mem_of_getElem? (i := 158) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (4,131) (6,132) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 6 132 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h165 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (5,132) (7,133)
    (I.realization.basis .sphere 5 132 0) (I.realization.basis .sphere 7 133 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,5,132,[0],7,133,[1],"S0_AdamsE2_ss",2575⟩ (by
    exact List.mem_of_getElem? (i := 165) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,132) (7,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 133 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h176 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (6,133) (8,134)
    (I.realization.basis .sphere 6 133 1) (I.realization.basis .sphere 8 134 5) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,6,133,[1],8,134,[5],"S0_AdamsE2_ss",2634⟩ (by
    exact List.mem_of_getElem? (i := 176) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (6,133) (8,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 8 134 [5] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_w_survives6_coordinate (I : Inputs D L G) :
      SurvivesTo (sequence D .sphere) 6 (8,134)
        (I.realization.basis .sphere 8 134 0 + I.realization.basis .sphere 8 134 3) := by
  classical
  let E := sequence D .sphere
  have h152 : ReachesPage E 14 (3,130) (I.realization.basis .sphere 3 130 0) := w_to_e6_h152 I
  have h175 : ReachesPage E 4 (6,133) (I.realization.basis .sphere 6 133 0) := w_to_e6_h175 I
  have h204 : ReachesPage E 6 (8,134) (I.realization.basis .sphere 8 134 0 + I.realization.basis .sphere 8 134 3) := w_to_e6_h204 I
  have h153 : HasDifferential E 2 (3,130) (5,131)
      (I.realization.basis .sphere 3 130 1) (I.realization.basis .sphere 5 131 0) := w_to_e6_h153 I
  have h158 : HasDifferential E 2 (4,131) (6,132)
      (I.realization.basis .sphere 4 131 0) (I.realization.basis .sphere 6 132 1) := w_to_e6_h158 I
  have h165 : HasDifferential E 2 (5,132) (7,133)
      (I.realization.basis .sphere 5 132 0) (I.realization.basis .sphere 7 133 1) := w_to_e6_h165 I
  have h176 : HasDifferential E 2 (6,133) (8,134)
      (I.realization.basis .sphere 6 133 1) (I.realization.basis .sphere 8 134 5) := w_to_e6_h176 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,8,134,["395,1", "394,1", "393,1", "392,1", "69,1,85,1", "0,6,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 162) (by rfl))
  change E.Page 2 (8,134) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 8 134 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 6) 1) = I.realization.basis .sphere 8 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 6) 1) = I.realization.basis .sphere 8 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 6) 1) = I.realization.basis .sphere 8 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 6) 1) = I.realization.basis .sphere 8 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 6) 1) = I.realization.basis .sphere 8 134 4 := he 4
  have he5 : e.symm (Finsupp.single (5:Fin 6) 1) = I.realization.basis .sphere 8 134 5 := he 5
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,6,133,["377,1", "0,5,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 139) (by rfl))
  change E.Page 2 (6,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 6 133 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 6 133 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 6 133 1 := hf 1
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,5,132,["0,4,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 128) (by rfl))
  change E.Page 2 (5,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at g
  change ∀ i : Fin 1, g.symm (Finsupp.single i 1) = I.realization.basis .sphere 5 132 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 5 132 0 := hg 0
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,4,131,["0,3,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 120) (by rfl))
  change E.Page 2 (4,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at k
  change ∀ i : Fin 1, k.symm (Finsupp.single i 1) = I.realization.basis .sphere 4 131 i.val at hk
  have hk0 : k.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 4 131 0 := hk 0
  obtain ⟨m,hm⟩ := I.basis ⟨.sphere,3,130,["1,1,69,2", "0,2,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 109) (by rfl))
  change E.Page 2 (3,130) ≃ₗ[ℤ] (Fin 2 →₀ F2) at m
  change ∀ i : Fin 2, m.symm (Finsupp.single i 1) = I.realization.basis .sphere 3 130 i.val at hm
  have hm0 : m.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 3 130 0 := hm 0
  have hm1 : m.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 3 130 1 := hm 1
  obtain ⟨t5,ht5⟩ := I.basis ⟨.sphere,7,133,["1,1,69,1,76,1", "0,5,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 150) (by rfl))
  change E.Page 2 (7,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at t5
  change ∀ i : Fin 2, t5.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 133 i.val at ht5
  have ht50 : t5.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 7 133 0 := ht5 0
  have ht51 : t5.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 7 133 1 := ht5 1
  obtain ⟨t4,ht4⟩ := I.basis ⟨.sphere,6,132,["368,1", "0,4,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 138) (by rfl))
  change E.Page 2 (6,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at t4
  change ∀ i : Fin 2, t4.symm (Finsupp.single i 1) = I.realization.basis .sphere 6 132 i.val at ht4
  have ht40 : t4.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 6 132 0 := ht4 0
  have ht41 : t4.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 6 132 1 := ht4 1
  obtain ⟨t3,ht3⟩ := I.basis ⟨.sphere,5,131,["0,3,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 127) (by rfl))
  change E.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at t3
  change ∀ i : Fin 1, t3.symm (Finsupp.single i 1) = I.realization.basis .sphere 5 131 i.val at ht3
  have ht30 : t3.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 5 131 0 := ht3 0
  have one_cases {p : ℤ×ℤ} (j : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2)) (x : E.Page 2 p) :
      x=0 ∨ x=j.symm (Finsupp.single 0 1) := by
    as_aux_lemma =>
      have h : j x 0=0 ∨ j x 0=1 := by generalize j x 0=c; fin_cases c <;> simp
      rcases h with h|h
      · left
        apply j.injective
        apply Finsupp.ext
        intro i
        fin_cases i
        simpa using h
      · right
        apply j.injective
        apply Finsupp.ext
        intro i
        fin_cases i
        simpa using h
  have rank_one_zero {p : ℤ×ℤ} (j : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2))
      (hn : E.d 2 p (j.symm (Finsupp.single 0 1))≠0) : Subsingleton (E.Page 3 p) := by
    as_aux_lemma =>
      apply third_zero_of_second_kernel (by change (2:ℤ)≤2; omega) p
      intro x hx
      rcases one_cases j x with rfl|rfl
      · exact RepresentsOnPage.zero (by decide)
      · exact False.elim (hn hx)
  have h53 : Subsingleton (E.Page 3 (5,132)) := by
    as_aux_lemma =>
      apply rank_one_zero g
      have hd : E.d 2 (5,132) (I.realization.basis .sphere 5 132 0)=I.realization.basis .sphere 7 133 1 := h165.eq_on_page_two.2
      rw [hg0,hd]
      intro hz
      have hh := congrArg (fun x=>t5 x 1) hz
      rw [←ht51,LinearEquiv.apply_symm_apply,map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
  have h43 : Subsingleton (E.Page 3 (4,131)) := by
    as_aux_lemma =>
      apply rank_one_zero k
      have hd : E.d 2 (4,131) (I.realization.basis .sphere 4 131 0)=I.realization.basis .sphere 6 132 1 := h158.eq_on_page_two.2
      rw [hk0,hd]
      intro hz
      have hh := congrArg (fun x=>t4 x 1) hz
      rw [←ht41,LinearEquiv.apply_symm_apply,map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
  have hin3 : E.d 3 (5,132)=0 := by
    as_aux_lemma =>
      ext x
      change E.d 3 (5,132) x=0
      rw [h53.elim x 0,map_zero]
  have hin4 : E.d 4 (4,131)=0 := by
    as_aux_lemma =>
      have h44 : Subsingleton (E.Page 4 (4,131)) :=
        adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 3 4 4 131 (by decide) (by decide) h43
      ext x
      change E.d 4 (4,131) x=0
      rw [h44.elim x 0,map_zero]
  have hin5 : E.d 5 (3,130)=0 := by
    as_aux_lemma =>
      obtain ⟨a14,ha14⟩ := h152
      obtain ⟨a5,ha5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤14) ha14
      have hn : E.d 2 (3,130) (m.symm (Finsupp.single 1 1))≠0 := by
        as_aux_lemma =>
          have hd : E.d 2 (3,130) (I.realization.basis .sphere 3 130 1)=I.realization.basis .sphere 5 131 0 := h153.eq_on_page_two.2
          rw [hm1,hd]
          intro hz
          have hh := congrArg (fun x=>t3 x 0) hz
          rw [←ht30,LinearEquiv.apply_symm_apply,t3.map_zero] at hh
          norm_num [Finsupp.single_apply] at hh
      have hd0 : E.d 5 (3,130) a5=0 :=
        represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<14) ha5 ⟨a14,ha14⟩
      ext x
      change E.d 5 (3,130) x=0
      rcases frame_after_second (by change (2:ℤ)≤2; omega) (by decide : (3:ℤ)≤5) m (by rw [hm0]; exact ha5) hn x with rfl|rfl
      · exact map_zero _
      · exact hd0
  have hd0 : E.d 2 (6,133) (I.realization.basis .sphere 6 133 0)=0 := by
    as_aux_lemma =>
      obtain ⟨a4,ha4⟩ := h175
      obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) ha4
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) ha2 ⟨a4,ha4⟩
      simpa only [ha2.eq_on_page_two] using hh
  have hd1 : E.d 2 (6,133) (I.realization.basis .sphere 6 133 1)=I.realization.basis .sphere 8 134 5 := h176.eq_on_page_two.2
  have incoming2 (x : E.Page 2 (6,133)) : e (E.d 2 (6,133) x) 0=0 := by
    as_aux_lemma =>
      have hall (a : Fin 2 →₀ F2) : e (E.d 2 (6,133) (f.symm a)) 0=0 := by
        as_aux_lemma =>
          induction a using Finsupp.induction with
          | zero => simp
          | @single_add i c a hi hci ih =>
            rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
            fin_cases c
            · simp
            · change e (E.d 2 (6,133) (f.symm (Finsupp.single i 1))) 0=0
              fin_cases i
              · change e (E.d 2 (6,133) (f.symm (Finsupp.single 0 1))) 0=0
                simp only [hf0,hd0,map_zero,Finsupp.zero_apply]
              · change e (E.d 2 (6,133) (f.symm (Finsupp.single 1 1))) 0=0
                simp only [hf1,hd1,←he5,LinearEquiv.apply_symm_apply]
                norm_num [Finsupp.single_apply,Fin.ext_iff]
      simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨a6,ha6⟩ := h204
  obtain ⟨a5,ha5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤6) ha6
  obtain ⟨a4,ha4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) ha5
  obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha4
  have hn3 : a3≠0 := by
    apply represents_next_nonzero_of_not_incoming_at
      (r := 2) (p := (8,134)) (q := (6,133)) (by rfl)
      (by change (2:ℤ)≤2; omega) (by decide) ha3
      (represents_two_self _)
    intro x hx
    change E.d 2 (6,133) x =
      I.realization.basis .sphere 8 134 0 + I.realization.basis .sphere 8 134 3 at hx
    have hzero := incoming2 x
    rw [hx,map_add,←he0,←he3,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff] at hzero
  have hn4 : a4≠0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) (by exact hin3) ha4 ha3 hn3
  have hn5 : a5≠0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤4; omega) (by decide : (2:ℤ)≤4) (by exact hin4) ha5 ha4 hn4
  refine ⟨a6,ha6,?_⟩
  exact represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤5; omega) (by decide : (2:ℤ)≤5) (by exact hin5) ha6 ha5 hn5



private theorem w_to_e6_w_label (I : Inputs D L G) :
      I.realization.sphere 8 134 W = I.realization.basis .sphere 8 134 0 + I.realization.basis .sphere 8 134 3 := by
  classical
  let E := sequence D .sphere
  have hmem : (⟨.sphere,8,134,["395,1","394,1","393,1","392,1","69,1,85,1","0,6,69,2"]⟩ : Raw.Degree) ∈ Raw.degrees := by
    exact List.mem_of_getElem? (i := 162) (by rfl)
  have hc := I.csv _ hmem rfl
  have a : I.realization.sphere 8 134 (atom .x_126_8_4) = I.realization.basis .sphere 8 134 0 := by
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 6)
    have heq : atom .x_126_8_4=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨395,by decide⟩ = projection (monomialOfString "395,1")
      have hs : "395,1" ≠ "" := by decide
      have hp : (("395,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [395,1] := by
        have split : "395,1".splitOn "," = ["395","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul]
    rw [heq]
    exact he
  have b : I.realization.sphere 8 134 (atom .x_126_8) = I.realization.basis .sphere 8 134 3 := by
    obtain ⟨z,hz,he⟩ := hc (3 : Fin 6)
    have heq : atom .x_126_8=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨392,by decide⟩ = projection (monomialOfString "392,1")
      have hs : "392,1" ≠ "" := by decide
      have hp : (("392,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [392,1] := by
        have split : "392,1".splitOn "," = ["392","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul]
    rw [heq]
    exact he
  change I.realization.sphere 8 134 ((atom .x_126_8_4)+(atom .x_126_8))=_
  rw [map_add,a,b]


private theorem w_to_e6 (I : Inputs D L G) : Derived.Survival I.realization 6 W := by
  let E := sequence D .sphere
  classical

  change SurvivesTo E 6 (8,134) _
  rw [w_to_e6_w_label I]
  exact w_to_e6_w_survives6_coordinate I

private theorem w_d6_targets_h342 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (14,139) (I.realization.basis .sphere 14 139 1) := by
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

private theorem w_d6_targets_h341 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,138) (14,139)
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

private theorem w_d6_targets_h343 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (14,139) (16,140)
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

private theorem w_d6_targets_t_label (I : Inputs D L G) :
      I.realization.sphere 14 139 T = I.realization.basis .sphere 14 139 1 := by
  classical
  let E := sequence D .sphere
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



private theorem w_d6_targets_t_page6_frame (I : Inputs D L G) :
      ∃ a : (sequence D .sphere).Page 6 (14,139),
        RepresentsOnPage (sequence D .sphere) 6 (14,139) (I.realization.basis .sphere 14 139 1) a ∧
        ∀ y : (sequence D .sphere).Page 6 (14,139), y=0 ∨ y=a := by
  classical
  let E := sequence D .sphere
  have h342 : ReachesPage E 1000 (14,139) (I.realization.basis .sphere 14 139 1) := w_d6_targets_h342 I
  have h341 : HasDifferential E 2 (12,138) (14,139)
      (I.realization.basis .sphere 12 138 1) (I.realization.basis .sphere 14 139 2) := w_d6_targets_h341 I
  have h343 : HasDifferential E 2 (14,139) (16,140)
      (I.realization.basis .sphere 14 139 0) (I.realization.basis .sphere 16 140 2) := w_d6_targets_h343 I
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
  have hd0 : E.d 2 (14,139) (I.realization.basis .sphere 14 139 0)≠0 := by
    have hn : I.realization.basis .sphere 16 140 2≠0 := by
      rw [←hf2]
      exact basis_vector_ne_zero f 2
    exact fun h => hn (h343.eq_on_page_two.2.symm.trans h)
  refine ⟨a,ha,?_⟩
  exact choice_frame_of_three_basis (by decide) (by change (2:ℤ)≤2; omega)
    e _ _ _ he0 he1 he2 a ha hz2 hd0


private theorem w_d6_targets (I : Inputs D L G) :
    DifferentialTargets (sequence D .sphere) 6 (8,134)
      (I.realization.sphere 8 134 W) (I.realization.sphere 14 139 T) := by
  let E := sequence D .sphere
  classical

  obtain ⟨a,ha,hall⟩ := w_d6_targets_t_page6_frame I
  intro x hx
  rcases hall (E.d 6 (8,134) x) with hz|hz
  · exact Or.inl hz
  · exact Or.inr ⟨a,by rw [w_d6_targets_t_label I]; exact ha,hz⟩

private theorem t_incoming_y_incoming2_zero_h190 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
    ((I.realization.basis .sphere 7 134 1)) ((I.realization.basis .sphere 9 135 4)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,7,134,[1],9,135,[4],"S0_AdamsE2_ss",2709⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,134) (9,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem t_incoming_y_incoming2_zero_h191 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
    ((I.realization.basis .sphere 7 134 4)) ((I.realization.basis .sphere 9 135 5)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,7,134,[4],9,135,[5],"S0_AdamsE2_ss",2710⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,134) (9,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [5] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem t_incoming_y_incoming2_zero_h231 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    ((I.realization.basis .sphere 9 135 2)) ((I.realization.basis .sphere 13 138 0)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
    exact List.mem_of_getElem? (i := 231) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem t_incoming_y_incoming2_zero_h232 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    ((I.realization.basis .sphere 9 135 1)) ((I.realization.basis .sphere 13 138 2)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
    exact List.mem_of_getElem? (i := 232) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem t_incoming_y_incoming2_zero_h233 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    ((I.realization.basis .sphere 9 135 0)) ((I.realization.basis .sphere 12 137 3) + (I.realization.basis .sphere 12 137 4)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,135,[0],12,137,[3, 4],"S0_AdamsE2_ss",2792⟩ (by
    exact List.mem_of_getElem? (i := 233) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem t_incoming_y_incoming2_zero_h234 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    ((I.realization.basis .sphere 9 135 3)) ((I.realization.basis .sphere 12 137 3)) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,135,[3],12,137,[3],"S0_AdamsE2_ss",2793⟩ (by
    exact List.mem_of_getElem? (i := 234) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem t_incoming_y_incoming2_zero (I : Inputs D L G) : (sequence D .sphere).d 2 (9,135)=0 := by
  classical
  let E := sequence D .sphere
  have h190 : HasDifferential E 2 (7,134) (9,135)
      ((I.realization.basis .sphere 7 134 1)) ((I.realization.basis .sphere 9 135 4)) := t_incoming_y_incoming2_zero_h190 I
  have h191 : HasDifferential E 2 (7,134) (9,135)
      ((I.realization.basis .sphere 7 134 4)) ((I.realization.basis .sphere 9 135 5)) := t_incoming_y_incoming2_zero_h191 I
  have h231 : HasDifferential E 4 (9,135) (13,138)
      ((I.realization.basis .sphere 9 135 2)) ((I.realization.basis .sphere 13 138 0)) := t_incoming_y_incoming2_zero_h231 I
  have h232 : HasDifferential E 4 (9,135) (13,138)
      ((I.realization.basis .sphere 9 135 1)) ((I.realization.basis .sphere 13 138 2)) := t_incoming_y_incoming2_zero_h232 I
  have h233 : HasDifferential E 3 (9,135) (12,137)
      ((I.realization.basis .sphere 9 135 0)) ((I.realization.basis .sphere 12 137 3) + (I.realization.basis .sphere 12 137 4)) := t_incoming_y_incoming2_zero_h233 I
  have h234 : HasDifferential E 3 (9,135) (12,137)
      ((I.realization.basis .sphere 9 135 3)) ((I.realization.basis .sphere 12 137 3)) := t_incoming_y_incoming2_zero_h234 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,135,["414,1", "1,1,376,1", "1,1,375,1", "0,1,394,1", "0,1,392,1", "0,7,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 174) (by rfl))
  change E.Page 2 (9,135) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 135 i.val at he
  have d0 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h233
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d1 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 1) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h232
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d2 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 2) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h231
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d3 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 3) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h234
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d4 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 4)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(7,134)) ⟨_,h190.eq_on_page_two.2⟩
  have d5 : E.d 2 (9,135) (I.realization.basis .sphere 9 135 5)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(7,134)) ⟨_,h191.eq_on_page_two.2⟩
  have hall (a : Fin 6 →₀ F2) : E.d 2 (9,135) (e.symm a)=0 := by
    induction a using Finsupp.induction with
    | zero => simp
    | @single_add i c a hi hc ih =>
      rw [map_add,map_add,ih,add_zero]
      fin_cases c
      · simp
      · change E.d 2 (9,135) (e.symm (Finsupp.single i 1))=0
        rw [he i]
        fin_cases i
        · exact d0
        · exact d1
        · exact d2
        · exact d3
        · exact d4
        · exact d5
  ext x
  change E.d 2 (9,135) x=0
  simpa only [LinearEquiv.symm_apply_apply] using hall (e x)


private theorem t_incoming_t_label (I : Inputs D L G) :
    I.realization.sphere 14 139 T = I.realization.basis .sphere 14 139 1 := by
  classical
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


private theorem t_incoming_w_label (I : Inputs D L G) :
    I.realization.sphere 8 134 W = I.realization.basis .sphere 8 134 0 + I.realization.basis .sphere 8 134 3 := by
  classical
  have hmem : (⟨.sphere,8,134,["395,1","394,1","393,1","392,1","69,1,85,1","0,6,69,2"]⟩ : Raw.Degree) ∈ Raw.degrees := by
    exact List.mem_of_getElem? (i := 162) (by rfl)
  have hc := I.csv _ hmem rfl
  have a : I.realization.sphere 8 134 (atom .x_126_8_4) = I.realization.basis .sphere 8 134 0 := by
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 6)
    have heq : atom .x_126_8_4=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨395,by decide⟩ = projection (monomialOfString "395,1")
      have hs : "395,1" ≠ "" := by decide
      have hp : (("395,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [395,1] := by
        have split : "395,1".splitOn "," = ["395","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul]
    rw [heq]
    exact he
  have b : I.realization.sphere 8 134 (atom .x_126_8) = I.realization.basis .sphere 8 134 3 := by
    obtain ⟨z,hz,he⟩ := hc (3 : Fin 6)
    have heq : atom .x_126_8=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨392,by decide⟩ = projection (monomialOfString "392,1")
      have hs : "392,1" ≠ "" := by decide
      have hp : (("392,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [392,1] := by
        have split : "392,1".splitOn "," = ["392","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul]
    rw [heq]
    exact he
  change I.realization.sphere 8 134 ((atom .x_126_8_4)+(atom .x_126_8))=_
  rw [map_add,a,b]


private theorem t_incoming_t_incoming2_not_hit_h264 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,137) (12,138)
    (I.realization.basis .sphere 10 137 0) (I.realization.basis .sphere 12 138 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,137,[0],12,138,[0],"S0_AdamsE2_ss",2932⟩ (by
    exact List.mem_of_getElem? (i := 264) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,137) (12,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 138 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming2_not_hit_h265 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,137) (12,138)
    (I.realization.basis .sphere 10 137 1) (I.realization.basis .sphere 12 138 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,137,[1],12,138,[2],"S0_AdamsE2_ss",2933⟩ (by
    exact List.mem_of_getElem? (i := 265) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,137) (12,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 138 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming2_not_hit_h266 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,137) (12,138)
    (I.realization.basis .sphere 10 137 5) (I.realization.basis .sphere 12 138 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,137,[5],12,138,[4],"S0_AdamsE2_ss",2934⟩ (by
    exact List.mem_of_getElem? (i := 266) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,137) (12,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [5] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 138 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming2_not_hit_h313 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (12,138) (16,141)
    (I.realization.basis .sphere 12 138 3) (I.realization.basis .sphere 16 141 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,12,138,[3],16,141,[1],"S0_AdamsE2_ss",3016⟩ (by
    exact List.mem_of_getElem? (i := 313) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (12,138) (16,141) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming2_not_hit_h314 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (12,138) (14,139)
    (I.realization.basis .sphere 12 138 1) (I.realization.basis .sphere 14 139 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,12,138,[1],14,139,[2],"S0_AdamsE2_ss",3017⟩ (by
    exact List.mem_of_getElem? (i := 314) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,138) (14,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 139 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming2_not_hit (I : Inputs D L G) :
    ¬ HitOnPage (sequence D .sphere) 2 (14,139) (I.realization.basis .sphere 14 139 1) := by
  classical
  let E := sequence D .sphere
  have h264 : HasDifferential E 2 (10,137) (12,138)
      (I.realization.basis .sphere 10 137 0) (I.realization.basis .sphere 12 138 0) := t_incoming_t_incoming2_not_hit_h264 I
  have h265 : HasDifferential E 2 (10,137) (12,138)
      (I.realization.basis .sphere 10 137 1) (I.realization.basis .sphere 12 138 2) := t_incoming_t_incoming2_not_hit_h265 I
  have h266 : HasDifferential E 2 (10,137) (12,138)
      (I.realization.basis .sphere 10 137 5) (I.realization.basis .sphere 12 138 4) := t_incoming_t_incoming2_not_hit_h266 I
  have h313 : HasDifferential E 4 (12,138) (16,141)
      (I.realization.basis .sphere 12 138 3) (I.realization.basis .sphere 16 141 1) := t_incoming_t_incoming2_not_hit_h313 I
  have h314 : HasDifferential E 2 (12,138) (14,139)
      (I.realization.basis .sphere 12 138 1) (I.realization.basis .sphere 14 139 2) := t_incoming_t_incoming2_not_hit_h314 I
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,138,["25,1,190,1", "3,1,336,1", "0,1,427,1", "0,2,419,1", "0,10,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 202) (by rfl))
  change E.Page 2 (12,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 138 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 12 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 12 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 12 138 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 12 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 12 138 4 := hf 4
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,14,139,["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl))
  change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 14 139 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.realization.basis .sphere 14 139 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.realization.basis .sphere 14 139 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.realization.basis .sphere 14 139 2 := he 2
  have hd0 : E.d 2 (12,138) (I.realization.basis .sphere 12 138 0)=0 := by
    have he : E.d 2 (10,137) (I.realization.basis .sphere 10 137 0)=I.realization.basis .sphere 12 138 0 := h264.eq_on_page_two.2
    rw [←he]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (10,137)) _
  have hd2 : E.d 2 (12,138) (I.realization.basis .sphere 12 138 2)=0 := by
    have he : E.d 2 (10,137) (I.realization.basis .sphere 10 137 1)=I.realization.basis .sphere 12 138 2 := h265.eq_on_page_two.2
    rw [←he]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (10,137)) _
  have hd4 : E.d 2 (12,138) (I.realization.basis .sphere 12 138 4)=0 := by
    have he : E.d 2 (10,137) (I.realization.basis .sphere 10 137 5)=I.realization.basis .sphere 12 138 4 := h266.eq_on_page_two.2
    rw [←he]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (10,137)) _
  have hd3 : E.d 2 (12,138) (I.realization.basis .sphere 12 138 3)=0 := by
    obtain ⟨_,a4,b4,ha4,_,_⟩ := h313
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) ha4
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) ha2 ⟨a4,ha4⟩
    simpa only [ha2.eq_on_page_two] using hh
  have hd1 : E.d 2 (12,138) (I.realization.basis .sphere 12 138 1)=I.realization.basis .sphere 14 139 2 := h314.eq_on_page_two.2
  have hin (x : E.Page 2 (12,138)) : e (E.d 2 (12,138) x) 1=0 := by
    have hall (a : Fin 5 →₀ F2) : e (E.d 2 (12,138) (f.symm a)) 1=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change e (E.d 2 (12,138) (f.symm (Finsupp.single i 1))) 1=0
          rw [hf i]
          fin_cases i
          · change e (E.d 2 (12,138) (I.realization.basis .sphere 12 138 0)) 1=0
            rw [hd0,e.map_zero]
            rfl
          · change e (E.d 2 (12,138) (I.realization.basis .sphere 12 138 1)) 1=0
            rw [hd1,←he2,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · change e (E.d 2 (12,138) (I.realization.basis .sphere 12 138 2)) 1=0
            rw [hd2,e.map_zero]
            rfl
          · change e (E.d 2 (12,138) (I.realization.basis .sphere 12 138 3)) 1=0
            rw [hd3,e.map_zero]
            rfl
          · change e (E.d 2 (12,138) (I.realization.basis .sphere 12 138 4)) 1=0
            rw [hd4,e.map_zero]
            rfl
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  rintro ⟨p,hp,x,y,hy,hyn,hd⟩
  have hq : p=(12,138) := add_right_cancel (hp.trans (show (14,139)=(12,138)+E.diffDeg 2 from rfl))
  subst p
  change E.d 2 (12,138) x=y at hd
  have hh := hin x
  rw [hd,←hy.eq_on_page_two,←he1,LinearEquiv.apply_symm_apply] at hh
  norm_num [Finsupp.single_apply] at hh


private theorem t_incoming_t_incoming3_zero_h284 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,136) (11,137)
    (I.realization.basis .sphere 9 136 2) (I.realization.basis .sphere 11 137 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,9,136,[2],11,137,[4],"S0_AdamsE2_ss",2923⟩ (by
    exact List.mem_of_getElem? (i := 284) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,136) (11,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 137 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero_h285 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,136) (11,137)
    (I.realization.basis .sphere 9 136 4) (I.realization.basis .sphere 11 137 5) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,9,136,[4],11,137,[5],"S0_AdamsE2_ss",2924⟩ (by
    exact List.mem_of_getElem? (i := 285) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,136) (11,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 136 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 137 [5] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero_h287 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (11,137) (15,140)
    (I.realization.basis .sphere 11 137 2) (I.realization.basis .sphere 15 140 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,11,137,[2],15,140,[1],"S0_AdamsE2_ss",2926⟩ (by
    exact List.mem_of_getElem? (i := 287) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (11,137) (15,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 140 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero_h288 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    (I.realization.basis .sphere 11 137 0) (I.realization.basis .sphere 13 138 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
    exact List.mem_of_getElem? (i := 288) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,137) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero_h289 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    (I.realization.basis .sphere 11 137 3) (I.realization.basis .sphere 13 138 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
    exact List.mem_of_getElem? (i := 289) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,137) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero_h286 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (11,137) (I.realization.basis .sphere 11 137 1 + I.realization.basis .sphere 11 137 2) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,1000,11,137,[1, 2],11,137,[],"S0_AdamsE2_ss",2925⟩ (by
    exact List.mem_of_getElem? (i := 286) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (11,137) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [1, 2] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero (I : Inputs D L G) : (sequence D .sphere).d 3 (11,137)=0 := by
  classical
  let E := sequence D .sphere
  have h284 : HasDifferential E 2 (9,136) (11,137)
      (I.realization.basis .sphere 9 136 2) (I.realization.basis .sphere 11 137 4) := t_incoming_t_incoming3_zero_h284 I
  have h285 : HasDifferential E 2 (9,136) (11,137)
      (I.realization.basis .sphere 9 136 4) (I.realization.basis .sphere 11 137 5) := t_incoming_t_incoming3_zero_h285 I
  have h287 : HasDifferential E 4 (11,137) (15,140)
      (I.realization.basis .sphere 11 137 2) (I.realization.basis .sphere 15 140 1) := t_incoming_t_incoming3_zero_h287 I
  have h288 : HasDifferential E 2 (11,137) (13,138)
      (I.realization.basis .sphere 11 137 0) (I.realization.basis .sphere 13 138 3) := t_incoming_t_incoming3_zero_h288 I
  have h289 : HasDifferential E 2 (11,137) (13,138)
      (I.realization.basis .sphere 11 137 3) (I.realization.basis .sphere 13 138 4) := t_incoming_t_incoming3_zero_h289 I
  have h286 : ReachesPage E 1000 (11,137) (I.realization.basis .sphere 11 137 1 + I.realization.basis .sphere 11 137 2) := t_incoming_t_incoming3_zero_h286 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,11,137,["427,1", "1,1,413,1", "1,1,412,1", "0,1,419,1", "0,2,414,1", "0,9,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 193) (by rfl))
  change E.Page 2 (11,137) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 137 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 6) 1) = I.realization.basis .sphere 11 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 6) 1) = I.realization.basis .sphere 11 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 6) 1) = I.realization.basis .sphere 11 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 6) 1) = I.realization.basis .sphere 11 137 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 6) 1) = I.realization.basis .sphere 11 137 4 := he 4
  have he5 : e.symm (Finsupp.single (5:Fin 6) 1) = I.realization.basis .sphere 11 137 5 := he 5
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 209) (by rfl))
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 138 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 13 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 13 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 13 138 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 13 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 13 138 4 := hf 4
  have hr2 : ReachesPage E 4 (11,137) (I.realization.basis .sphere 11 137 2) := by
    obtain ⟨_,a,b,ha,_,_⟩ := h287
    exact ⟨a,ha⟩
  have hr1 : ReachesPage E 4 (11,137) (I.realization.basis .sphere 11 137 1) := by
    obtain ⟨a1000,ha1000⟩ := h286
    obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) ha1000
    obtain ⟨b,hb⟩ := hr2
    have hab := represents_add_tail ha hb
    have heq : (I.realization.basis .sphere 11 137 1+I.realization.basis .sphere 11 137 2)+I.realization.basis .sphere 11 137 2=I.realization.basis .sphere 11 137 1 := by
      apply e.injective
      simp only [map_add,←he1,←he2,LinearEquiv.apply_symm_apply]
      apply Finsupp.ext
      intro i
      fin_cases i <;> norm_num [Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff] <;> decide
    exact ⟨a+b,by simpa only [heq] using hab⟩
  have hr4 : ReachesPage E 4 (11,137) (I.realization.basis .sphere 11 137 4) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h284⟩
  have hr5 : ReachesPage E 4 (11,137) (I.realization.basis .sphere 11 137 5) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h285⟩
  have dz {x : E.Page 2 (11,137)} (hx : ReachesPage E 4 (11,137) x) : E.d 2 (11,137) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 0)=I.realization.basis .sphere 13 138 3 := h288.eq_on_page_two.2
  have hd3 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 3)=I.realization.basis .sphere 13 138 4 := h289.eq_on_page_two.2
  have hd1 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 1)=0 := dz hr1
  have hd2 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 2)=0 := dz hr2
  have hd4 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 4)=0 := dz hr4
  have hd5 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 5)=0 := dz hr5
  have coord0 (x : E.Page 2 (11,137)) : f (E.d 2 (11,137) x) 3=e x 0 := by
    have hall (c : Fin 6 →₀ F2) : f (E.d 2 (11,137) (e.symm c)) 3=c 0 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,Finsupp.add_apply,ih]
        congr 1
        fin_cases c
        · simp
        · change f (E.d 2 (11,137) (e.symm (Finsupp.single i 1))) 3=(Finsupp.single i (1:F2)) 0
          rw [he i]
          fin_cases i
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 0)) 3=(Finsupp.single (0:Fin 6) (1:F2)) 0
            rw [hd0,←hf3,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 1)) 3=(Finsupp.single (1:Fin 6) (1:F2)) 0
            rw [hd1,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 2)) 3=(Finsupp.single (2:Fin 6) (1:F2)) 0
            rw [hd2,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 3)) 3=(Finsupp.single (3:Fin 6) (1:F2)) 0
            rw [hd3,←hf4,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 4)) 3=(Finsupp.single (4:Fin 6) (1:F2)) 0
            rw [hd4,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 5)) 3=(Finsupp.single (5:Fin 6) (1:F2)) 0
            rw [hd5,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)
  have coord3 (x : E.Page 2 (11,137)) : f (E.d 2 (11,137) x) 4=e x 3 := by
    have hall (c : Fin 6 →₀ F2) : f (E.d 2 (11,137) (e.symm c)) 4=c 3 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,Finsupp.add_apply,ih]
        congr 1
        fin_cases c
        · simp
        · change f (E.d 2 (11,137) (e.symm (Finsupp.single i 1))) 4=(Finsupp.single i (1:F2)) 3
          rw [he i]
          fin_cases i
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 0)) 4=(Finsupp.single (0:Fin 6) (1:F2)) 3
            rw [hd0,←hf3,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 1)) 4=(Finsupp.single (1:Fin 6) (1:F2)) 3
            rw [hd1,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 2)) 4=(Finsupp.single (2:Fin 6) (1:F2)) 3
            rw [hd2,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 3)) 4=(Finsupp.single (3:Fin 6) (1:F2)) 3
            rw [hd3,←hf4,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 4)) 4=(Finsupp.single (4:Fin 6) (1:F2)) 3
            rw [hd4,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 5)) 4=(Finsupp.single (5:Fin 6) (1:F2)) 3
            rw [hd5,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)
  apply d_zero_of_second_kernel_extends (by change (2:ℤ)≤2; omega) (by decide : (3:ℤ)≤3)
  intro x hx
  have hc0 : e x 0=0 := by
    have h := coord0 x
    rw [hx,f.map_zero,Finsupp.zero_apply] at h
    exact h.symm
  have hc3 : e x 3=0 := by
    have h := coord3 x
    rw [hx,f.map_zero,Finsupp.zero_apply] at h
    exact h.symm
  apply reaches_from_support (by decide : (2:ℤ)≤4) e x
  intro i hi
  rw [he i]
  fin_cases i
  · change e x 0≠0 at hi
    exact False.elim (hi hc0)
  · exact hr1
  · exact hr2
  · change e x 3≠0 at hi
    exact False.elim (hi hc3)
  · exact hr4
  · exact hr5


private theorem t_incoming_t_incoming4_zero_h256 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.realization.basis .sphere 8 135 0) (I.realization.basis .sphere 10 136 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,135,[0],10,136,[1],"S0_AdamsE2_ss",2855⟩ (by
    exact List.mem_of_getElem? (i := 256) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming4_zero_h257 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.realization.basis .sphere 8 135 4) (I.realization.basis .sphere 10 136 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,135,[4],10,136,[3],"S0_AdamsE2_ss",2856⟩ (by
    exact List.mem_of_getElem? (i := 257) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming4_zero_h258 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.realization.basis .sphere 8 135 6) (I.realization.basis .sphere 10 136 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,135,[6],10,136,[4],"S0_AdamsE2_ss",2857⟩ (by
    exact List.mem_of_getElem? (i := 258) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [6] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming4_zero_h260 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,136) (12,137)
    (I.realization.basis .sphere 10 136 0) (I.realization.basis .sphere 12 137 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,136,[0],12,137,[2],"S0_AdamsE2_ss",2859⟩ (by
    exact List.mem_of_getElem? (i := 260) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,136) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming4_zero_h259 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (10,136) (I.realization.basis .sphere 10 136 2) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,1000,10,136,[2],10,136,[],"S0_AdamsE2_ss",2858⟩ (by
    exact List.mem_of_getElem? (i := 259) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (10,136) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [2] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming4_zero (I : Inputs D L G) : (sequence D .sphere).d 4 (10,136)=0 := by
  classical
  let E := sequence D .sphere
  have h256 : HasDifferential E 2 (8,135) (10,136)
      (I.realization.basis .sphere 8 135 0) (I.realization.basis .sphere 10 136 1) := t_incoming_t_incoming4_zero_h256 I
  have h257 : HasDifferential E 2 (8,135) (10,136)
      (I.realization.basis .sphere 8 135 4) (I.realization.basis .sphere 10 136 3) := t_incoming_t_incoming4_zero_h257 I
  have h258 : HasDifferential E 2 (8,135) (10,136)
      (I.realization.basis .sphere 8 135 6) (I.realization.basis .sphere 10 136 4) := t_incoming_t_incoming4_zero_h258 I
  have h260 : HasDifferential E 2 (10,136) (12,137)
      (I.realization.basis .sphere 10 136 0) (I.realization.basis .sphere 12 137 2) := t_incoming_t_incoming4_zero_h260 I
  have h259 : ReachesPage E 1000 (10,136) (I.realization.basis .sphere 10 136 2) := t_incoming_t_incoming4_zero_h259 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,136,["419,1", "0,1,414,1", "0,2,394,1", "0,2,392,1", "0,8,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 183) (by rfl))
  change E.Page 2 (10,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 136 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 10 136 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 10 136 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 10 136 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 10 136 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 10 136 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 137 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 12 137 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 12 137 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 12 137 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 12 137 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 12 137 4 := hf 4
  have hr2 : ReachesPage E 5 (10,136) (I.realization.basis .sphere 10 136 2) := by
    obtain ⟨a,ha⟩ := h259
    exact represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤1000) ha
  have hr1 : ReachesPage E 5 (10,136) (I.realization.basis .sphere 10 136 1) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h256⟩
  have hr3 : ReachesPage E 5 (10,136) (I.realization.basis .sphere 10 136 3) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h257⟩
  have hr4 : ReachesPage E 5 (10,136) (I.realization.basis .sphere 10 136 4) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h258⟩
  have dz {x : E.Page 2 (10,136)} (hx : ReachesPage E 5 (10,136) x) : E.d 2 (10,136) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 0)=I.realization.basis .sphere 12 137 2 := h260.eq_on_page_two.2
  have hd1 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 1)=0 := dz hr1
  have hd2 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 2)=0 := dz hr2
  have hd3 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 3)=0 := dz hr3
  have hd4 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 4)=0 := dz hr4
  have coord0 (x : E.Page 2 (10,136)) : f (E.d 2 (10,136) x) 2=e x 0 := by
    have hall (c : Fin 5 →₀ F2) : f (E.d 2 (10,136) (e.symm c)) 2=c 0 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,Finsupp.add_apply,ih]
        congr 1
        fin_cases c
        · simp
        · change f (E.d 2 (10,136) (e.symm (Finsupp.single i 1))) 2=(Finsupp.single i (1:F2)) 0
          rw [he i]
          fin_cases i
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 0)) 2=(Finsupp.single (0:Fin 5) (1:F2)) 0
            rw [hd0,←hf2,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 1)) 2=(Finsupp.single (1:Fin 5) (1:F2)) 0
            rw [hd1,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 2)) 2=(Finsupp.single (2:Fin 5) (1:F2)) 0
            rw [hd2,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 3)) 2=(Finsupp.single (3:Fin 5) (1:F2)) 0
            rw [hd3,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 4)) 2=(Finsupp.single (4:Fin 5) (1:F2)) 0
            rw [hd4,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)
  apply d_zero_of_second_kernel_extends (by change (2:ℤ)≤2; omega) (by decide : (3:ℤ)≤4)
  intro x hx
  have hc0 : e x 0=0 := by
    have h := coord0 x
    rw [hx,f.map_zero,Finsupp.zero_apply] at h
    exact h.symm
  apply reaches_from_support (by decide : (2:ℤ)≤5) e x
  intro i hi
  rw [he i]
  fin_cases i
  · change e x 0≠0 at hi
    exact False.elim (hi hc0)
  · exact hr1
  · exact hr2
  · exact hr3
  · exact hr4


private theorem t_incoming_t_source10_d3_zero_h256 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.realization.basis .sphere 8 135 0) (I.realization.basis .sphere 10 136 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,135,[0],10,136,[1],"S0_AdamsE2_ss",2855⟩ (by
    exact List.mem_of_getElem? (i := 256) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_source10_d3_zero_h257 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.realization.basis .sphere 8 135 4) (I.realization.basis .sphere 10 136 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,135,[4],10,136,[3],"S0_AdamsE2_ss",2856⟩ (by
    exact List.mem_of_getElem? (i := 257) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_source10_d3_zero_h258 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.realization.basis .sphere 8 135 6) (I.realization.basis .sphere 10 136 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,135,[6],10,136,[4],"S0_AdamsE2_ss",2857⟩ (by
    exact List.mem_of_getElem? (i := 258) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [6] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_source10_d3_zero_h260 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,136) (12,137)
    (I.realization.basis .sphere 10 136 0) (I.realization.basis .sphere 12 137 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,136,[0],12,137,[2],"S0_AdamsE2_ss",2859⟩ (by
    exact List.mem_of_getElem? (i := 260) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,136) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_source10_d3_zero_h259 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (10,136) (I.realization.basis .sphere 10 136 2) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,1000,10,136,[2],10,136,[],"S0_AdamsE2_ss",2858⟩ (by
    exact List.mem_of_getElem? (i := 259) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (10,136) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [2] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_source10_d3_zero (I : Inputs D L G) : (sequence D .sphere).d 3 (10,136)=0 := by
  classical
  let E := sequence D .sphere
  have h256 : HasDifferential E 2 (8,135) (10,136)
      (I.realization.basis .sphere 8 135 0) (I.realization.basis .sphere 10 136 1) := t_incoming_t_source10_d3_zero_h256 I
  have h257 : HasDifferential E 2 (8,135) (10,136)
      (I.realization.basis .sphere 8 135 4) (I.realization.basis .sphere 10 136 3) := t_incoming_t_source10_d3_zero_h257 I
  have h258 : HasDifferential E 2 (8,135) (10,136)
      (I.realization.basis .sphere 8 135 6) (I.realization.basis .sphere 10 136 4) := t_incoming_t_source10_d3_zero_h258 I
  have h260 : HasDifferential E 2 (10,136) (12,137)
      (I.realization.basis .sphere 10 136 0) (I.realization.basis .sphere 12 137 2) := t_incoming_t_source10_d3_zero_h260 I
  have h259 : ReachesPage E 1000 (10,136) (I.realization.basis .sphere 10 136 2) := t_incoming_t_source10_d3_zero_h259 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,136,["419,1", "0,1,414,1", "0,2,394,1", "0,2,392,1", "0,8,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 183) (by rfl))
  change E.Page 2 (10,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 136 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 10 136 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 10 136 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 10 136 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 10 136 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 10 136 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 137 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 12 137 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 12 137 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 12 137 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 12 137 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 12 137 4 := hf 4
  have hr2 : ReachesPage E 4 (10,136) (I.realization.basis .sphere 10 136 2) := by
    obtain ⟨a,ha⟩ := h259
    exact represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) ha
  have hr1 : ReachesPage E 4 (10,136) (I.realization.basis .sphere 10 136 1) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h256⟩
  have hr3 : ReachesPage E 4 (10,136) (I.realization.basis .sphere 10 136 3) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h257⟩
  have hr4 : ReachesPage E 4 (10,136) (I.realization.basis .sphere 10 136 4) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h258⟩
  have dz {x : E.Page 2 (10,136)} (hx : ReachesPage E 4 (10,136) x) : E.d 2 (10,136) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 0)=I.realization.basis .sphere 12 137 2 := h260.eq_on_page_two.2
  have hd1 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 1)=0 := dz hr1
  have hd2 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 2)=0 := dz hr2
  have hd3 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 3)=0 := dz hr3
  have hd4 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 4)=0 := dz hr4
  have coord0 (x : E.Page 2 (10,136)) : f (E.d 2 (10,136) x) 2=e x 0 := by
    have hall (c : Fin 5 →₀ F2) : f (E.d 2 (10,136) (e.symm c)) 2=c 0 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,Finsupp.add_apply,ih]
        congr 1
        fin_cases c
        · simp
        · change f (E.d 2 (10,136) (e.symm (Finsupp.single i 1))) 2=(Finsupp.single i (1:F2)) 0
          rw [he i]
          fin_cases i
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 0)) 2=(Finsupp.single (0:Fin 5) (1:F2)) 0
            rw [hd0,←hf2,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 1)) 2=(Finsupp.single (1:Fin 5) (1:F2)) 0
            rw [hd1,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 2)) 2=(Finsupp.single (2:Fin 5) (1:F2)) 0
            rw [hd2,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 3)) 2=(Finsupp.single (3:Fin 5) (1:F2)) 0
            rw [hd3,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 4)) 2=(Finsupp.single (4:Fin 5) (1:F2)) 0
            rw [hd4,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)
  apply d_zero_of_second_kernel_extends (by change (2:ℤ)≤2; omega) (by decide : (3:ℤ)≤3)
  intro x hx
  have hc0 : e x 0=0 := by
    have h := coord0 x
    rw [hx,f.map_zero,Finsupp.zero_apply] at h
    exact h.symm
  apply reaches_from_support (by decide : (2:ℤ)≤4) e x
  intro i hi
  rw [he i]
  fin_cases i
  · change e x 0≠0 at hi
    exact False.elim (hi hc0)
  · exact hr1
  · exact hr2
  · exact hr3
  · exact hr4


private theorem t_incoming_t_d3_targets_independent_h256 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.realization.basis .sphere 8 135 0) (I.realization.basis .sphere 10 136 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,135,[0],10,136,[1],"S0_AdamsE2_ss",2855⟩ (by
    exact List.mem_of_getElem? (i := 256) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d3_targets_independent_h257 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.realization.basis .sphere 8 135 4) (I.realization.basis .sphere 10 136 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,135,[4],10,136,[3],"S0_AdamsE2_ss",2856⟩ (by
    exact List.mem_of_getElem? (i := 257) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d3_targets_independent_h258 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.realization.basis .sphere 8 135 6) (I.realization.basis .sphere 10 136 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,135,[6],10,136,[4],"S0_AdamsE2_ss",2857⟩ (by
    exact List.mem_of_getElem? (i := 258) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [6] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d3_targets_independent_h260 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (10,136) (12,137)
    (I.realization.basis .sphere 10 136 0) (I.realization.basis .sphere 12 137 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,10,136,[0],12,137,[2],"S0_AdamsE2_ss",2859⟩ (by
    exact List.mem_of_getElem? (i := 260) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,136) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d3_targets_independent_h259 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (10,136) (I.realization.basis .sphere 10 136 2) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,1000,10,136,[2],10,136,[],"S0_AdamsE2_ss",2858⟩ (by
    exact List.mem_of_getElem? (i := 259) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (10,136) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [2] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d3_targets_independent (I : Inputs D L G)
    (a b : (sequence D .sphere).Page 3 (12,137))
    (ha : RepresentsOnPage (sequence D .sphere) 3 (12,137)
      (I.realization.basis .sphere 12 137 3+I.realization.basis .sphere 12 137 4) a)
    (hb : RepresentsOnPage (sequence D .sphere) 3 (12,137) (I.realization.basis .sphere 12 137 3) b) :
    a≠0 ∧ b≠0 ∧ a+b≠0 := by
  classical
  let E := sequence D .sphere
  have h256 : HasDifferential E 2 (8,135) (10,136)
      (I.realization.basis .sphere 8 135 0) (I.realization.basis .sphere 10 136 1) := t_incoming_t_d3_targets_independent_h256 I
  have h257 : HasDifferential E 2 (8,135) (10,136)
      (I.realization.basis .sphere 8 135 4) (I.realization.basis .sphere 10 136 3) := t_incoming_t_d3_targets_independent_h257 I
  have h258 : HasDifferential E 2 (8,135) (10,136)
      (I.realization.basis .sphere 8 135 6) (I.realization.basis .sphere 10 136 4) := t_incoming_t_d3_targets_independent_h258 I
  have h260 : HasDifferential E 2 (10,136) (12,137)
      (I.realization.basis .sphere 10 136 0) (I.realization.basis .sphere 12 137 2) := t_incoming_t_d3_targets_independent_h260 I
  have h259 : ReachesPage E 1000 (10,136) (I.realization.basis .sphere 10 136 2) := t_incoming_t_d3_targets_independent_h259 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,136,["419,1", "0,1,414,1", "0,2,394,1", "0,2,392,1", "0,8,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 183) (by rfl))
  change E.Page 2 (10,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 136 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 10 136 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 10 136 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 10 136 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 10 136 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 10 136 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 12 137 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 12 137 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 12 137 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 12 137 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 12 137 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 12 137 4 := hf 4
  have hr2 : ReachesPage E 5 (10,136) (I.realization.basis .sphere 10 136 2) := by
    obtain ⟨a,ha⟩ := h259
    exact represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤1000) ha
  have hr1 : ReachesPage E 5 (10,136) (I.realization.basis .sphere 10 136 1) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h256⟩
  have hr3 : ReachesPage E 5 (10,136) (I.realization.basis .sphere 10 136 3) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h257⟩
  have hr4 : ReachesPage E 5 (10,136) (I.realization.basis .sphere 10 136 4) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h258⟩
  have dz {x : E.Page 2 (10,136)} (hx : ReachesPage E 5 (10,136) x) : E.d 2 (10,136) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 0)=I.realization.basis .sphere 12 137 2 := h260.eq_on_page_two.2
  have hd1 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 1)=0 := dz hr1
  have hd2 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 2)=0 := dz hr2
  have hd3 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 3)=0 := dz hr3
  have hd4 : E.d 2 (10,136) (I.realization.basis .sphere 10 136 4)=0 := dz hr4
  have hin (j : Fin 5) (hj : j≠2) (x : E.Page 2 (10,136)) : f (E.d 2 (10,136) x) j=0 := by
    have hall (c : Fin 5 →₀ F2) : f (E.d 2 (10,136) (e.symm c)) j=0 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change f (E.d 2 (10,136) (e.symm (Finsupp.single i 1))) j=0
          rw [he i]
          fin_cases i
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 0)) j=0
            rw [hd0,←hf2,LinearEquiv.apply_symm_apply]
            simp [Finsupp.single_apply,Ne.symm hj]
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 1)) j=0
            rw [hd1,f.map_zero]
            rfl
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 2)) j=0
            rw [hd2,f.map_zero]
            rfl
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 3)) j=0
            rw [hd3,f.map_zero]
            rfl
          · change f (E.d 2 (10,136) (I.realization.basis .sphere 10 136 4)) j=0
            rw [hd4,f.map_zero]
            rfl
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)

  have nz {x : E.Page 2 (12,137)} {v : E.Page 3 (12,137)} (hv : RepresentsOnPage E 3 (12,137) x v)
      (j : Fin 5) (hj : j≠2) (hx : f x j=1) : v≠0 := by
    obtain ⟨_,z,hz2,hz3⟩ := hv
    intro hzero
    obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (10,136) z).mp (hz3.trans hzero)
    have he : E.d 2 (10,136) u=x := hu.trans hz2
    have hh := hin j hj u
    rw [he,hx] at hh
    exact one_ne_zero hh
  refine ⟨nz ha 4 (by decide) ?_,nz hb 3 (by decide) ?_,nz (represents_add_tail ha hb) 4 (by decide) ?_⟩ <;>
    simp only [map_add,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply] <;>
    norm_num [Finsupp.single_apply,Fin.ext_iff]


private theorem t_incoming_t_d4_targets_independent_h284 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,136) (11,137)
    (I.realization.basis .sphere 9 136 2) (I.realization.basis .sphere 11 137 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,9,136,[2],11,137,[4],"S0_AdamsE2_ss",2923⟩ (by
    exact List.mem_of_getElem? (i := 284) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,136) (11,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 137 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent_h285 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (9,136) (11,137)
    (I.realization.basis .sphere 9 136 4) (I.realization.basis .sphere 11 137 5) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,9,136,[4],11,137,[5],"S0_AdamsE2_ss",2924⟩ (by
    exact List.mem_of_getElem? (i := 285) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,136) (11,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 136 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 137 [5] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent_h287 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (11,137) (15,140)
    (I.realization.basis .sphere 11 137 2) (I.realization.basis .sphere 15 140 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,11,137,[2],15,140,[1],"S0_AdamsE2_ss",2926⟩ (by
    exact List.mem_of_getElem? (i := 287) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (11,137) (15,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 140 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent_h288 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    (I.realization.basis .sphere 11 137 0) (I.realization.basis .sphere 13 138 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
    exact List.mem_of_getElem? (i := 288) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,137) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent_h289 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    (I.realization.basis .sphere 11 137 3) (I.realization.basis .sphere 13 138 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
    exact List.mem_of_getElem? (i := 289) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,137) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent_h286 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 1000 (11,137) (I.realization.basis .sphere 11 137 1 + I.realization.basis .sphere 11 137 2) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,1000,11,137,[1, 2],11,137,[],"S0_AdamsE2_ss",2925⟩ (by
    exact List.mem_of_getElem? (i := 286) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (11,137) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [1, 2] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent (I : Inputs D L G)
    (a b : (sequence D .sphere).Page 4 (13,138))
    (ha : RepresentsOnPage (sequence D .sphere) 4 (13,138) (I.realization.basis .sphere 13 138 2) a)
    (hb : RepresentsOnPage (sequence D .sphere) 4 (13,138) (I.realization.basis .sphere 13 138 0) b) :
    a≠0 ∧ b≠0 ∧ a+b≠0 := by
  classical
  let E := sequence D .sphere
  have h284 : HasDifferential E 2 (9,136) (11,137)
      (I.realization.basis .sphere 9 136 2) (I.realization.basis .sphere 11 137 4) := t_incoming_t_d4_targets_independent_h284 I
  have h285 : HasDifferential E 2 (9,136) (11,137)
      (I.realization.basis .sphere 9 136 4) (I.realization.basis .sphere 11 137 5) := t_incoming_t_d4_targets_independent_h285 I
  have h287 : HasDifferential E 4 (11,137) (15,140)
      (I.realization.basis .sphere 11 137 2) (I.realization.basis .sphere 15 140 1) := t_incoming_t_d4_targets_independent_h287 I
  have h288 : HasDifferential E 2 (11,137) (13,138)
      (I.realization.basis .sphere 11 137 0) (I.realization.basis .sphere 13 138 3) := t_incoming_t_d4_targets_independent_h288 I
  have h289 : HasDifferential E 2 (11,137) (13,138)
      (I.realization.basis .sphere 11 137 3) (I.realization.basis .sphere 13 138 4) := t_incoming_t_d4_targets_independent_h289 I
  have h286 : ReachesPage E 1000 (11,137) (I.realization.basis .sphere 11 137 1 + I.realization.basis .sphere 11 137 2) := t_incoming_t_d4_targets_independent_h286 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,11,137,["427,1", "1,1,413,1", "1,1,412,1", "0,1,419,1", "0,2,414,1", "0,9,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 193) (by rfl))
  change E.Page 2 (11,137) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 137 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 6) 1) = I.realization.basis .sphere 11 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 6) 1) = I.realization.basis .sphere 11 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 6) 1) = I.realization.basis .sphere 11 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 6) 1) = I.realization.basis .sphere 11 137 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 6) 1) = I.realization.basis .sphere 11 137 4 := he 4
  have he5 : e.symm (Finsupp.single (5:Fin 6) 1) = I.realization.basis .sphere 11 137 5 := he 5
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 209) (by rfl))
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 13 138 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 13 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 13 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 13 138 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 13 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 13 138 4 := hf 4
  have hr2 : ReachesPage E 4 (11,137) (I.realization.basis .sphere 11 137 2) := by
    obtain ⟨_,a,b,ha,_,_⟩ := h287
    exact ⟨a,ha⟩
  have hr1 : ReachesPage E 4 (11,137) (I.realization.basis .sphere 11 137 1) := by
    obtain ⟨a1000,ha1000⟩ := h286
    obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) ha1000
    obtain ⟨b,hb⟩ := hr2
    have hab := represents_add_tail ha hb
    have heq : (I.realization.basis .sphere 11 137 1+I.realization.basis .sphere 11 137 2)+I.realization.basis .sphere 11 137 2=I.realization.basis .sphere 11 137 1 := by
      apply e.injective
      simp only [map_add,←he1,←he2,LinearEquiv.apply_symm_apply]
      apply Finsupp.ext
      intro i
      fin_cases i <;> norm_num [Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff] <;> decide
    exact ⟨a+b,by simpa only [heq] using hab⟩
  have hr4 : ReachesPage E 4 (11,137) (I.realization.basis .sphere 11 137 4) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h284⟩
  have hr5 : ReachesPage E 4 (11,137) (I.realization.basis .sphere 11 137 5) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h285⟩
  have dz {x : E.Page 2 (11,137)} (hx : ReachesPage E 4 (11,137) x) : E.d 2 (11,137) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 0)=I.realization.basis .sphere 13 138 3 := h288.eq_on_page_two.2
  have hd3 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 3)=I.realization.basis .sphere 13 138 4 := h289.eq_on_page_two.2
  have hd1 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 1)=0 := dz hr1
  have hd2 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 2)=0 := dz hr2
  have hd4 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 4)=0 := dz hr4
  have hd5 : E.d 2 (11,137) (I.realization.basis .sphere 11 137 5)=0 := dz hr5
  have hin (j : Fin 5) (hj : j≠3 ∧ j≠4) (x : E.Page 2 (11,137)) : f (E.d 2 (11,137) x) j=0 := by
    have hall (c : Fin 6 →₀ F2) : f (E.d 2 (11,137) (e.symm c)) j=0 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change f (E.d 2 (11,137) (e.symm (Finsupp.single i 1))) j=0
          rw [he i]
          fin_cases i
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 0)) j=0
            rw [hd0,←hf3,LinearEquiv.apply_symm_apply]
            simp [Finsupp.single_apply,Ne.symm hj.1]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 1)) j=0
            rw [hd1,f.map_zero]
            rfl
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 2)) j=0
            rw [hd2,f.map_zero]
            rfl
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 3)) j=0
            rw [hd3,←hf4,LinearEquiv.apply_symm_apply]
            simp [Finsupp.single_apply,Ne.symm hj.2]
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 4)) j=0
            rw [hd4,f.map_zero]
            rfl
          · change f (E.d 2 (11,137) (I.realization.basis .sphere 11 137 5)) j=0
            rw [hd5,f.map_zero]
            rfl
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)

  have nz3 {x : E.Page 2 (13,138)} {v : E.Page 3 (13,138)} (hv : RepresentsOnPage E 3 (13,138) x v)
      (j : Fin 5) (hj : j≠3 ∧ j≠4) (hx : f x j=1) : v≠0 := by
    obtain ⟨_,z,hz2,hz3⟩ := hv
    intro hzero
    obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (11,137) z).mp (hz3.trans hzero)
    have he : E.d 2 (11,137) u=x := hu.trans hz2
    have hh := hin j hj u
    rw [he,hx] at hh
    exact one_ne_zero hh
  have nz4 {x : E.Page 2 (13,138)} {v : E.Page 4 (13,138)} (hv : RepresentsOnPage E 4 (13,138) x v)
      (j : Fin 5) (hj : j≠3 ∧ j≠4) (hx : f x j=1) : v≠0 := by
    obtain ⟨v3,hv3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hv
    exact represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤3; omega)
      (by decide : (2:ℤ)≤3) (by exact t_incoming_t_source10_d3_zero I) hv hv3 (nz3 hv3 j hj hx)
  refine ⟨nz4 ha 2 (by decide) ?_,nz4 hb 0 (by decide) ?_,nz4 (represents_add_tail ha hb) 2 (by decide) ?_⟩ <;>
    simp only [map_add,←hf0,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply] <;>
    norm_num [Finsupp.single_apply,Fin.ext_iff]


private theorem t_incoming_t_incoming5_source_five_h229 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
    (I.realization.basis .sphere 7 134 1) (I.realization.basis .sphere 9 135 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,7,134,[1],9,135,[4],"S0_AdamsE2_ss",2788⟩ (by
    exact List.mem_of_getElem? (i := 229) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,134) (9,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five_h230 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
    (I.realization.basis .sphere 7 134 4) (I.realization.basis .sphere 9 135 5) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,7,134,[4],9,135,[5],"S0_AdamsE2_ss",2789⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,134) (9,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [5] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five_h231 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    (I.realization.basis .sphere 9 135 2) (I.realization.basis .sphere 13 138 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
    exact List.mem_of_getElem? (i := 231) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five_h232 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    (I.realization.basis .sphere 9 135 1) (I.realization.basis .sphere 13 138 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
    exact List.mem_of_getElem? (i := 232) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five_h233 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    (I.realization.basis .sphere 9 135 0) (I.realization.basis .sphere 12 137 3 + I.realization.basis .sphere 12 137 4) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,135,[0],12,137,[3, 4],"S0_AdamsE2_ss",2792⟩ (by
    exact List.mem_of_getElem? (i := 233) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3, 4] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five_h234 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    (I.realization.basis .sphere 9 135 3) (I.realization.basis .sphere 12 137 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,9,135,[3],12,137,[3],"S0_AdamsE2_ss",2793⟩ (by
    exact List.mem_of_getElem? (i := 234) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (9,135)) := by
  classical
  let E := sequence D .sphere
  have h229 : HasDifferential E 2 (7,134) (9,135)
      (I.realization.basis .sphere 7 134 1) (I.realization.basis .sphere 9 135 4) := t_incoming_t_incoming5_source_five_h229 I
  have h230 : HasDifferential E 2 (7,134) (9,135)
      (I.realization.basis .sphere 7 134 4) (I.realization.basis .sphere 9 135 5) := t_incoming_t_incoming5_source_five_h230 I
  have h231 : HasDifferential E 4 (9,135) (13,138)
      (I.realization.basis .sphere 9 135 2) (I.realization.basis .sphere 13 138 0) := t_incoming_t_incoming5_source_five_h231 I
  have h232 : HasDifferential E 4 (9,135) (13,138)
      (I.realization.basis .sphere 9 135 1) (I.realization.basis .sphere 13 138 2) := t_incoming_t_incoming5_source_five_h232 I
  have h233 : HasDifferential E 3 (9,135) (12,137)
      (I.realization.basis .sphere 9 135 0) (I.realization.basis .sphere 12 137 3 + I.realization.basis .sphere 12 137 4) := t_incoming_t_incoming5_source_five_h233 I
  have h234 : HasDifferential E 3 (9,135) (12,137)
      (I.realization.basis .sphere 9 135 3) (I.realization.basis .sphere 12 137 3) := t_incoming_t_incoming5_source_five_h234 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,135,["414,1", "1,1,376,1", "1,1,375,1", "0,1,394,1", "0,1,392,1", "0,7,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 174) (by rfl))
  change E.Page 2 (9,135) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 9 135 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 6) 1) = I.realization.basis .sphere 9 135 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 6) 1) = I.realization.basis .sphere 9 135 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 6) 1) = I.realization.basis .sphere 9 135 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 6) 1) = I.realization.basis .sphere 9 135 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 6) 1) = I.realization.basis .sphere 9 135 4 := he 4
  have he5 : e.symm (Finsupp.single (5:Fin 6) 1) = I.realization.basis .sphere 9 135 5 := he 5
  obtain ⟨_,a0,y0,ha0,hy0,hd0⟩ := h233
  obtain ⟨_,a3,y3,ha3,hy3,hd3⟩ := h234
  obtain ⟨_,a1,y1,ha1,hy1,hd1⟩ := h232
  obtain ⟨_,a2,y2,ha2,hy2,hd2⟩ := h231
  have d0 : E.d 3 (9,135) a0=y0 := hd0
  have d3 : E.d 3 (9,135) a3=y3 := hd3
  have d1 : E.d 4 (9,135) a1=y1 := hd1
  have d2 : E.d 4 (9,135) a2=y2 := hd2
  obtain ⟨b1,hb1⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha1
  obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha2
  have db1 : E.d 3 (9,135) b1=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) hb1 ⟨a1,ha1⟩
  have db2 : E.d 3 (9,135) b2=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) hb2 ⟨a2,ha2⟩
  obtain ⟨ny0,ny3,nys⟩ := t_incoming_t_d3_targets_independent I y0 y3 hy0 hy3
  obtain ⟨ny1,ny2,nyt⟩ := t_incoming_t_d4_targets_independent I y1 y2 hy1 hy2
  have hz4 : RepresentsOnPage E 5 (9,135) (I.realization.basis .sphere 9 135 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h229
  have hz5 : RepresentsOnPage E 5 (9,135) (I.realization.basis .sphere 9 135 5) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h230
  have hall (z : E.Page 5 (9,135)) : z=0 := by
    obtain ⟨x,hx⟩ := page_has_representative (by decide : (2:ℤ)≤5) z
    have hcb : RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 4 (e x 4)+Finsupp.single 5 (e x 5))) 0 := by
      generalize e x 4=c4,e x 5=c5
      fin_cases c4 <;> fin_cases c5
      · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 4 (0:F2)+Finsupp.single 5 (0:F2))) 0
        simpa only [Finsupp.single_zero,zero_add,add_zero,map_zero,map_add,he4,he5] using RepresentsOnPage.zero (by decide : (2:ℤ)≤5)
      · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 4 (0:F2)+Finsupp.single 5 (1:F2))) 0
        simpa only [Finsupp.single_zero,zero_add,add_zero,map_zero,map_add,he4,he5] using hz5
      · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 4 (1:F2)+Finsupp.single 5 (0:F2))) 0
        simpa only [Finsupp.single_zero,zero_add,add_zero,map_zero,map_add,he4,he5] using hz4
      · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 4 (1:F2)+Finsupp.single 5 (1:F2))) 0
        simpa only [Finsupp.single_zero,zero_add,add_zero,map_zero,map_add,he4,he5] using represents_add_tail hz4 hz5
    have hclean : x-e.symm (Finsupp.single 4 (e x 4)+Finsupp.single 5 (e x 5)) =
        e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)) := by
      apply e.injective
      simp only [map_sub,LinearEquiv.apply_symm_apply]
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [Finsupp.sub_apply,Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff]
    have hz := represents_sub_tail hx hcb
    rw [hclean,sub_zero] at hz
    generalize e x 0=c0,e x 1=c1,e x 2=c2,e x 3=c3 at hz
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      exact represents_unique hz (RepresentsOnPage.zero (by decide : (2:ℤ)≤5))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) ha3 ⟨z,hz⟩
      exact False.elim (ny3 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) ha2 ⟨z,hz⟩
      exact False.elim (ny2 (by simpa only [map_add,d1,d2] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail hb2 ha3) ⟨z,hz⟩
      exact False.elim (ny3 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) ha1 ⟨z,hz⟩
      exact False.elim (ny1 (by simpa only [map_add,d1,d2] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail hb1 ha3) ⟨z,hz⟩
      exact False.elim (ny3 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) (represents_add_tail ha1 ha2) ⟨z,hz⟩
      exact False.elim (nyt (by simpa only [map_add,d1,d2] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail (represents_add_tail hb1 hb2) ha3) ⟨z,hz⟩
      exact False.elim (ny3 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) ha0 ⟨z,hz⟩
      exact False.elim (ny0 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail ha0 ha3) ⟨z,hz⟩
      exact False.elim (nys (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail ha0 hb2) ⟨z,hz⟩
      exact False.elim (ny0 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail (represents_add_tail ha0 hb2) ha3) ⟨z,hz⟩
      exact False.elim (nys (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail ha0 hb1) ⟨z,hz⟩
      exact False.elim (ny0 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail (represents_add_tail ha0 hb1) ha3) ⟨z,hz⟩
      exact False.elim (nys (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail (represents_add_tail ha0 hb1) hb2) ⟨z,hz⟩
      exact False.elim (ny0 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he1,he2,he3,map_zero] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail (represents_add_tail (represents_add_tail ha0 hb1) hb2) ha3) ⟨z,hz⟩
      exact False.elim (nys (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
  exact ⟨fun a b=>(hall a).trans (hall b).symm⟩


private theorem t_incoming_t_incoming6_image_h176 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (6,133) (8,134)
    (I.realization.basis .sphere 6 133 1) (I.realization.basis .sphere 8 134 5) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,6,133,[1],8,134,[5],"S0_AdamsE2_ss",2634⟩ (by
    exact List.mem_of_getElem? (i := 176) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (6,133) (8,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 8 134 [5] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image_h205 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    (I.realization.basis .sphere 8 134 3) (I.realization.basis .sphere 11 136 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2703⟩ (by
    exact List.mem_of_getElem? (i := 205) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image_h206 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    (I.realization.basis .sphere 8 134 2) (I.realization.basis .sphere 11 136 2) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,3,8,134,[2],11,136,[2],"S0_AdamsE2_ss",2704⟩ (by
    exact List.mem_of_getElem? (i := 206) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [2] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image_h207 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (8,134) (10,135)
    (I.realization.basis .sphere 8 134 1) (I.realization.basis .sphere 10 135 3) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2705⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,134) (10,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image_h203 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 17 (8,134) (I.realization.basis .sphere 8 134 4) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,17,8,134,[4],8,134,[],"S0_AdamsE2_ss",2701⟩ (by
    exact List.mem_of_getElem? (i := 203) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 17 (8,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [4] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image_h204 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 6 (8,134) (I.realization.basis .sphere 8 134 0 + I.realization.basis .sphere 8 134 3) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,6,8,134,[0, 3],8,134,[],"S0_AdamsE2_ss",2702⟩ (by
    exact List.mem_of_getElem? (i := 204) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 6 (8,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [0, 3] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image (I : Inputs D L G) :
    ∃ w : (sequence D .sphere).Page 6 (8,134),
      RepresentsOnPage (sequence D .sphere) 6 (8,134)
        (I.realization.basis .sphere 8 134 0+I.realization.basis .sphere 8 134 3) w ∧
      ∀ z : (sequence D .sphere).Page 6 (8,134),
        (sequence D .sphere).d 6 (8,134) z=0 ∨
        (sequence D .sphere).d 6 (8,134) z=(sequence D .sphere).d 6 (8,134) w := by
  classical
  let E := sequence D .sphere
  have h176 : HasDifferential E 2 (6,133) (8,134)
      (I.realization.basis .sphere 6 133 1) (I.realization.basis .sphere 8 134 5) := t_incoming_t_incoming6_image_h176 I
  have h205 : HasDifferential E 3 (8,134) (11,136)
      (I.realization.basis .sphere 8 134 3) (I.realization.basis .sphere 11 136 1) := t_incoming_t_incoming6_image_h205 I
  have h206 : HasDifferential E 3 (8,134) (11,136)
      (I.realization.basis .sphere 8 134 2) (I.realization.basis .sphere 11 136 2) := t_incoming_t_incoming6_image_h206 I
  have h207 : HasDifferential E 2 (8,134) (10,135)
      (I.realization.basis .sphere 8 134 1) (I.realization.basis .sphere 10 135 3) := t_incoming_t_incoming6_image_h207 I
  have h203 : ReachesPage E 17 (8,134) (I.realization.basis .sphere 8 134 4) := t_incoming_t_incoming6_image_h203 I
  have h204 : ReachesPage E 6 (8,134) (I.realization.basis .sphere 8 134 0 + I.realization.basis .sphere 8 134 3) := t_incoming_t_incoming6_image_h204 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,8,134,["395,1", "394,1", "393,1", "392,1", "69,1,85,1", "0,6,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 162) (by rfl))
  change E.Page 2 (8,134) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 8 134 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 6) 1) = I.realization.basis .sphere 8 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 6) 1) = I.realization.basis .sphere 8 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 6) 1) = I.realization.basis .sphere 8 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 6) 1) = I.realization.basis .sphere 8 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 6) 1) = I.realization.basis .sphere 8 134 4 := he 4
  have he5 : e.symm (Finsupp.single (5:Fin 6) 1) = I.realization.basis .sphere 8 134 5 := he 5
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.realization.basis .sphere 10 135 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 10 135 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 10 135 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 10 135 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 10 135 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 10 135 4 := hf 4
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 192) (by rfl))
  change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I.realization.basis .sphere 11 136 i.val at hk
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = I.realization.basis .sphere 11 136 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = I.realization.basis .sphere 11 136 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = I.realization.basis .sphere 11 136 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = I.realization.basis .sphere 11 136 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = I.realization.basis .sphere 11 136 4 := hk 4
  obtain ⟨w,hw⟩ := h204
  obtain ⟨b17,hb17⟩ := h203
  obtain ⟨b6,hb6⟩ := represents_before (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤17) hb17
  obtain ⟨w3,hw3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤6) hw
  obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤17) hb17
  obtain ⟨_,a3,y1,ha3,hy1,hda3⟩ := h205
  obtain ⟨_,a2,y2,ha2,hy2,hda2⟩ := h206
  have hd3a : E.d 3 (8,134) a3=y1 := hda3
  have hd2' : E.d 3 (8,134) a2=y2 := hda2
  have hdw3 : E.d 3 (8,134) w3=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hw3 ⟨w,hw⟩
  have hdb3 : E.d 3 (8,134) b3=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<17) hb3 ⟨b17,hb17⟩
  have hdb6 : E.d 6 (8,134) b6=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤6; omega) (by decide : (6:ℤ)<17) hb6 ⟨b17,hb17⟩
  have heq : (I.realization.basis .sphere 8 134 0+I.realization.basis .sphere 8 134 3)+I.realization.basis .sphere 8 134 3=I.realization.basis .sphere 8 134 0 := by
    apply e.injective
    simp only [map_add,map_sub,←he0,←he3,LinearEquiv.apply_symm_apply]
    apply Finsupp.ext
    intro i
    fin_cases i <;> norm_num [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.single_apply,Fin.ext_iff] <;> decide
  have ha0 : RepresentsOnPage E 3 (8,134) (I.realization.basis .sphere 8 134 0) (w3+a3) := by
    simpa only [heq] using represents_add_tail hw3 ha3
  have hd0' : E.d 3 (8,134) (w3+a3)=y1 := by rw [map_add,hdw3,hd3a,zero_add]
  have hz5 : RepresentsOnPage E 6 (8,134) (I.realization.basis .sphere 8 134 5) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h176
  have dz {x : E.Page 2 (8,134)} {r : ℤ} (hr : 3≤r) (hx : ReachesPage E r (8,134) x) : E.d 2 (8,134) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega : (2:ℤ)<r) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 0)=0 := dz (by decide) ⟨_,ha0⟩
  have hd1 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 1)=I.realization.basis .sphere 10 135 3 := h207.eq_on_page_two.2
  have hd2 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 2)=0 := dz (by decide) ⟨_,ha2⟩
  have hd3 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 3)=0 := dz (by decide) ⟨_,ha3⟩
  have hd4 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 4)=0 := dz (by decide) ⟨_,hb17⟩
  have hd5 : E.d 2 (8,134) (I.realization.basis .sphere 8 134 5)=0 := dz (by decide) ⟨_,hz5⟩
  have coord1 (x : E.Page 2 (8,134)) : f (E.d 2 (8,134) x) 3=e x 1 := by
    have hall (c : Fin 6 →₀ F2) : f (E.d 2 (8,134) (e.symm c)) 3=c 1 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,Finsupp.add_apply,ih]
        congr 1
        fin_cases c
        · simp
        · change f (E.d 2 (8,134) (e.symm (Finsupp.single i 1))) 3=(Finsupp.single i (1:F2)) 1
          rw [he i]
          fin_cases i
          · change f (E.d 2 (8,134) (I.realization.basis .sphere 8 134 0)) 3=(Finsupp.single (0:Fin 6) (1:F2)) 1
            rw [hd0,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (8,134) (I.realization.basis .sphere 8 134 1)) 3=(Finsupp.single (1:Fin 6) (1:F2)) 1
            rw [hd1,←hf3,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (8,134) (I.realization.basis .sphere 8 134 2)) 3=(Finsupp.single (2:Fin 6) (1:F2)) 1
            rw [hd2,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (8,134) (I.realization.basis .sphere 8 134 3)) 3=(Finsupp.single (3:Fin 6) (1:F2)) 1
            rw [hd3,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (8,134) (I.realization.basis .sphere 8 134 4)) 3=(Finsupp.single (4:Fin 6) (1:F2)) 1
            rw [hd4,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (8,134) (I.realization.basis .sphere 8 134 5)) 3=(Finsupp.single (5:Fin 6) (1:F2)) 1
            rw [hd5,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)

  have nonzero3 {x : E.Page 2 (11,136)} {a : E.Page 3 (11,136)} (ha : RepresentsOnPage E 3 (11,136) x a) (hn : x≠0) : a≠0 := by
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) ha
    rw [←ha2.eq_on_page_two] at ha2
    exact represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤2; omega)
      (by decide : (2:ℤ)≤2) (by exact t_incoming_y_incoming2_zero I) ha ha2 hn
  refine ⟨w,hw,?_⟩
  intro z
  obtain ⟨x,hx⟩ := page_has_representative (by decide : (2:ℤ)≤6) z
  have hx2 : E.d 2 (8,134) x=0 := dz (by decide) ⟨z,hx⟩
  have hc1 : e x 1=0 := by
    have hh := coord1 x
    rw [hx2,f.map_zero,Finsupp.zero_apply] at hh
    exact hh.symm
  have hcb : RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 5 (e x 5))) 0 := by
    generalize e x 5=c
    fin_cases c
    · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 5 (0:F2))) 0
      simpa only [Finsupp.single_zero,map_zero] using (RepresentsOnPage.zero (by decide) : RepresentsOnPage E 6 (8,134) 0 0)
    · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 5 (1:F2))) 0
      simpa only [he5] using hz5
  have hclean : x-e.symm (Finsupp.single 5 (e x 5)) =
      e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4)) := by
    apply e.injective
    simp only [map_sub,LinearEquiv.apply_symm_apply]
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.sub_apply,Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff,hc1]
  have hz := represents_sub_tail hx hcb
  rw [hclean,sub_zero] at hz
  generalize e x 0=c0,e x 2=c2,e x 3=c3,e x 4=c4 at hz
  fin_cases c0 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    left
    have hz0 := represents_unique hz (RepresentsOnPage.zero (by decide : (2:ℤ)≤6))
    rw [hz0,map_zero]
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    left
    have hz' := represents_unique hz hb6
    rw [hz',hdb6]
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := ha3
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1)≠0 := by
      apply nonzero3 hy1
      intro hez
      have hez' := congrArg (fun t=>k t 1) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := (represents_add_tail ha3 hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+0)≠0 := by
      apply nonzero3 (represents_add_tail hy1 (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 1) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := ha2
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y2)≠0 := by
      apply nonzero3 hy2
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := (represents_add_tail ha2 hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y2+0)≠0 := by
      apply nonzero3 (represents_add_tail hy2 (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := (represents_add_tail ha2 ha3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y2+y1)≠0 := by
      apply nonzero3 (represents_add_tail hy2 hy1)
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := (represents_add_tail (represents_add_tail ha2 ha3) hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y2+y1+0)≠0 := by
      apply nonzero3 (represents_add_tail (represents_add_tail hy2 hy1) (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := ha0
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1)≠0 := by
      apply nonzero3 hy1
      intro hez
      have hez' := congrArg (fun t=>k t 1) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := (represents_add_tail ha0 hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+0)≠0 := by
      apply nonzero3 (represents_add_tail hy1 (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 1) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    right
    have hz' := represents_unique hz hw
    rw [hz']
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    right
    have hz' := represents_unique hz (represents_add_tail hw hb6)
    rw [hz',map_add,hdb6,add_zero]
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := (represents_add_tail ha0 ha2)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+y2)≠0 := by
      apply nonzero3 (represents_add_tail hy1 hy2)
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := (represents_add_tail (represents_add_tail ha0 ha2) hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+y2+0)≠0 := by
      apply nonzero3 (represents_add_tail (represents_add_tail hy1 hy2) (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := (represents_add_tail (represents_add_tail ha0 ha2) ha3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+y2+y1)≠0 := by
      apply nonzero3 (represents_add_tail (represents_add_tail hy1 hy2) hy1)
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he0,he2,he3,he4,map_zero] at hz
    have hrep := (represents_add_tail (represents_add_tail (represents_add_tail ha0 ha2) ha3) hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+y2+y1+0)≠0 := by
      apply nonzero3 (represents_add_tail (represents_add_tail (represents_add_tail hy1 hy2) hy1) (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))


private theorem t_incoming_t_incoming7_zero_h186 (I : Inputs D L G) : ReachesPage (sequence D .sphere) 18 (7,133) (I.realization.basis .sphere 7 133 0) := by
  classical
  have hrow := I.results ⟨.sphere,.reaches,18,7,133,[0],7,133,[],"S0_AdamsE2_ss",2632⟩ (by
    exact List.mem_of_getElem? (i := 186) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 18 (7,133) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 133 [0] = true := rfl
  simp only [Realization.decode,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming7_zero_h185 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (5,132) (7,133)
    (I.realization.basis .sphere 5 132 0) (I.realization.basis .sphere 7 133 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,5,132,[0],7,133,[1],"S0_AdamsE2_ss",2631⟩ (by
    exact List.mem_of_getElem? (i := 185) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,132) (7,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 133 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming7_zero (I : Inputs D L G) : (sequence D .sphere).d 7 (7,133)=0 := by
  classical
  let E := sequence D .sphere
  have h186 : ReachesPage E 18 (7,133) (I.realization.basis .sphere 7 133 0) := t_incoming_t_incoming7_zero_h186 I
  have h185 : HasDifferential E 2 (5,132) (7,133)
      (I.realization.basis .sphere 5 132 0) (I.realization.basis .sphere 7 133 1) := t_incoming_t_incoming7_zero_h185 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,7,133,["1,1,69,1,76,1", "0,5,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 150) (by rfl))
  change E.Page 2 (7,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 133 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 7 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 7 133 1 := he 1
  obtain ⟨a18,ha18⟩ := h186
  obtain ⟨a7,ha7⟩ := represents_before (by decide : (2:ℤ)≤7) (by decide : (7:ℤ)≤18) ha18
  have hdz : E.d 7 (7,133) a7=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤7; omega) (by decide : (7:ℤ)<18) ha7 ⟨a18,ha18⟩
  have hz : RepresentsOnPage E 7 (7,133) (I.realization.basis .sphere 7 133 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h185
  ext y
  change E.d 7 (7,133) y=0
  obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤7) e
    (fun i=>if i=0 then a7 else 0) (by
      intro i
      rw [he i]
      fin_cases i
      · change RepresentsOnPage E 7 (7,133) (I.realization.basis .sphere 7 133 0) a7
        exact ha7
      · change RepresentsOnPage E 7 (7,133) (I.realization.basis .sphere 7 133 1) 0
        exact hz) y
  rw [hc,map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs <;> simp [hdz]


private theorem t_incoming_t_incoming9_zero_h164 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (3,130) (5,131)
    (I.realization.basis .sphere 3 130 1) (I.realization.basis .sphere 5 131 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,3,130,[1],5,131,[0],"S0_AdamsE2_ss",2494⟩ (by
    exact List.mem_of_getElem? (i := 164) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (3,130) (5,131) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 5 131 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming9_zero (I : Inputs D L G) : (sequence D .sphere).d 9 (5,131)=0 := by
  classical
  let E := sequence D .sphere
  have h164 : HasDifferential E 2 (3,130) (5,131)
      (I.realization.basis .sphere 3 130 1) (I.realization.basis .sphere 5 131 0) := t_incoming_t_incoming9_zero_h164 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,5,131,["0,3,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 127) (by rfl))
  change E.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 5 131 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 5 131 0 := he 0
  have hz : RepresentsOnPage E 9 (5,131) (I.realization.basis .sphere 5 131 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h164
  have hall (y : E.Page 9 (5,131)) : y=0 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤9) e (fun _=>0) (by
      intro i
      rw [he i]
      fin_cases i
      exact hz) y
    simpa using hc
  ext y
  change E.d 9 (5,131) y=0
  rw [hall y,map_zero]


private theorem t_incoming_t_incoming11_zero_h151 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (1,128) (3,129)
    (I.realization.basis .sphere 1 128 0) (I.realization.basis .sphere 3 129 0) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,1,128,[0],3,129,[0],"S0_AdamsE2_ss",2380⟩ (by
    exact List.mem_of_getElem? (i := 151) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (1,128) (3,129) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 1 128 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 3 129 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming11_zero (I : Inputs D L G) : (sequence D .sphere).d 11 (3,129)=0 := by
  classical
  let E := sequence D .sphere
  have h151 : HasDifferential E 2 (1,128) (3,129)
      (I.realization.basis .sphere 1 128 0) (I.realization.basis .sphere 3 129 0) := t_incoming_t_incoming11_zero_h151 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,3,129,["0,1,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 108) (by rfl))
  change E.Page 2 (3,129) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 3 129 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 3 129 0 := he 0
  have hz : RepresentsOnPage E 11 (3,129) (I.realization.basis .sphere 3 129 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h151
  have hall (y : E.Page 11 (3,129)) : y=0 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤11) e (fun _=>0) (by
      intro i
      rw [he i]
      fin_cases i
      exact hz) y
    simpa using hc
  ext y
  change E.d 11 (3,129) y=0
  rw [hall y,map_zero]


private theorem t_incoming_t_incoming_late_zero (I : Inputs D L G) (r : ℤ) (hr : 13≤r) :
    (sequence D .sphere).d r ((14,139)-(sequence D .sphere).diffDeg r)=0 := by
  classical
  let E := sequence D .sphere
  have he : Subsingleton (E.Page r ((14,139)-E.diffDeg r)) := by
    by_cases h15 : 15≤r
    · change Subsingleton (E.Page r (14-r,139-(r-1)))
      exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r (14-r) (139-(r-1)) (by omega)
    · have hrs : r=13 ∨ r=14 := by omega
      rcases hrs with rfl|rfl
      · change Subsingleton (E.Page 13 (1,127))
        obtain ⟨e,he⟩ := I.basis ⟨.sphere,1,127,[]⟩ (by
          exact List.mem_of_getElem? (i := 90) (by rfl))
        change E.Page 2 (1,127) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
        change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 1 127 i.val at he
        exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 13 1 127
          (by decide) (by decide) e.injective.subsingleton
      · change Subsingleton (E.Page 14 (0,126))
        obtain ⟨e,he⟩ := I.basis ⟨.sphere,0,126,[]⟩ (by
          exact List.mem_of_getElem? (i := 77) (by rfl))
        change E.Page 2 (0,126) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
        change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 0 126 i.val at he
        exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 14 0 126
          (by decide) (by decide) e.injective.subsingleton
  ext y
  change E.d r ((14,139)-E.diffDeg r) y=0
  rw [he.elim y 0,map_zero]


private theorem t_incoming_t_incoming8_source_four_h173 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (4,131) (6,132)
    (I.realization.basis .sphere 4 131 0) (I.realization.basis .sphere 6 132 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,4,131,[0],6,132,[1],"S0_AdamsE2_ss",2573⟩ (by
    exact List.mem_of_getElem? (i := 173) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (4,131) (6,132) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 6 132 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming8_source_four (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (6,132)) := by
  classical
  let E := sequence D .sphere
  have h173 : HasDifferential E 2 (4,131) (6,132)
      (I.realization.basis .sphere 4 131 0) (I.realization.basis .sphere 6 132 1) := t_incoming_t_incoming8_source_four_h173 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,6,132,["368,1", "0,4,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 138) (by rfl))
  change E.Page 2 (6,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 6 132 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 6 132 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 6 132 1 := he 1
  have n659 : ¬ HasDifferential E 3 (6,132) (9,134) (I.realization.basis .sphere 6 132 0) (0) := by
    have hh := I.results ⟨.sphere,.refutation,3,6,132,[0],9,134,[],"proofs.db/log",2047477⟩ (by
      exact List.mem_of_getElem? (i := 659) (by rfl))
    dsimp only [Statement] at hh
    obtain ⟨x,hx,y,hy,hh⟩ := hh
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 9 134 []=true := rfl
    simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hh
    exact hh
  have hz1 : RepresentsOnPage E 4 (6,132) (I.realization.basis .sphere 6 132 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h173
  have hn {a : E.Page 4 (6,132)} (ha : RepresentsOnPage E 4 (6,132) (I.realization.basis .sphere 6 132 0) a) : False := by
    obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    have hd : E.d 3 (6,132) a3=0 := represents_d_zero_of_later
      (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) ha3 ⟨a,ha⟩
    apply n659
    refine ⟨rfl,a3,0,ha3,RepresentsOnPage.zero (by decide),?_⟩
    exact hd
  have hall (a : E.Page 4 (6,132)) : a=0 := by
    let A := E.ssData (6,132)
    haveI : Epi (A.pageπ 2) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 2)).mp inferInstance a
    let x := (Subobject.ofLE (A.Z 2) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤2)) ≫ A.pageπ 0) z
    have hx : RepresentsOnPage E 4 (6,132) x a := ⟨by decide,z,rfl,hz⟩
    have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [Finsupp.single_apply]
    have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    fin_cases c0 <;> fin_cases c1
    · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,e.symm.map_zero] at hxe
      rw [hxe] at hx
      exact represents_unique hx (RepresentsOnPage.zero (by decide))
    · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,he1] at hxe
      rw [hxe] at hx
      exact represents_unique hx hz1
    · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,he0] at hxe
      rw [hxe] at hx
      exact False.elim (hn hx)
    · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)) at hxe
      simp only [map_add,he0,he1] at hxe
      rw [hxe] at hx
      have hh := represents_add_tail hx hz1
      have heq : (I.realization.basis .sphere 6 132 0 + I.realization.basis .sphere 6 132 1) + I.realization.basis .sphere 6 132 1 = I.realization.basis .sphere 6 132 0 := by
        apply e.injective
        simp only [map_add,←he0,←he1,LinearEquiv.apply_symm_apply]
        apply Finsupp.ext
        intro i
        fin_cases i <;> norm_num [Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff] <;> decide
      rw [heq,add_zero] at hh
      exact False.elim (hn hh)
  exact ⟨fun a b=>(hall a).trans (hall b).symm⟩


private theorem x1264_d3_coordinate
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : Model H M Syn}
    {L : Labels H} {G : KIP126.Literature.Route.TmfLabels H} (I : Inputs D L G) :
    HasNonzeroDifferential (sequence D .sphere) 3 (4,130) (7,132)
      (I.realization.basis .sphere 4 130 0) (I.realization.basis .sphere 7 132 0) := by
  let E := sequence D .sphere
  obtain ⟨e5_131,he5_131⟩ := I.basis ⟨.sphere, 5, 131, ["0,3,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 127) (by rfl))
  change E.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e5_131
  change ∀i : Fin 1, e5_131.symm (Finsupp.single i 1) = I.realization.basis .sphere 5 131 i.val at he5_131
  obtain ⟨e7_132,he7_132⟩ := I.basis ⟨.sphere, 7, 132, ["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e7_132
  change ∀i : Fin 1, e7_132.symm (Finsupp.single i 1) = I.realization.basis .sphere 7 132 i.val at he7_132
  have h153 : HasDifferential E 2 (3,130) (5,131) (I.realization.basis .sphere 3 130 1) (I.realization.basis .sphere 5 131 0) := sphere_named_differentials_hD3x1264_h153 I
  have h655 : HasDifferential E 3 (4,130) (7,132) (I.realization.basis .sphere 4 130 0) (I.realization.basis .sphere 7 132 0) := sphere_named_differentials_hD3x1264_h655 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    as_aux_lemma =>
      exact represents_two_self _
  have d2_5 : E.d 2 (5,131)=0 := by
    obtain ⟨y,hy,hd⟩ := differential_target_cycle h153
    have d0 : E.d 2 (5,131) (I.realization.basis .sphere 5 131 0)=0 := by
      exact (congrArg (fun z => E.d 2 (5,131) z) hy.eq_on_page_two).trans hd
    apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e5_131
    intro i
    fin_cases i
    refine ⟨I.realization.basis .sphere 5 131 0,?_,d0⟩
    rw [he5_131]
    exact represents_two_self _
  obtain ⟨hdeg,xr,yr,hxr,hyr,hd⟩ := h655
  refine ⟨hdeg,xr,yr,hxr,hyr,hd,?_⟩
  have bne : I.realization.basis .sphere 7 132 0≠0 := by
    rw [show I.realization.basis .sphere 7 132 0 = e7_132.symm (Finsupp.single 0 1) from (he7_132 0).symm]
    exact basis_vector_ne_zero e7_132 0
  exact represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)≤2)
    d2_5 hyr (hrep2 _) bne


private theorem t_incoming_t_incoming10_source_four_h156 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (2,129) (4,130)
    (I.realization.basis .sphere 2 129 0) (I.realization.basis .sphere 4 130 1) := by
  classical
  have hrow := I.results ⟨.sphere,.equation,2,2,129,[0],4,130,[1],"S0_AdamsE2_ss",2436⟩ (by
    exact List.mem_of_getElem? (i := 156) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (2,129) (4,130) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 2 129 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 4 130 [1] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming10_source_four (I : Inputs D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (4,130)) := by
  classical
  let E := sequence D .sphere
  have h156 : HasDifferential E 2 (2,129) (4,130)
      (I.realization.basis .sphere 2 129 0) (I.realization.basis .sphere 4 130 1) := t_incoming_t_incoming10_source_four_h156 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,4,130,["341,1", "0,2,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 119) (by rfl))
  change E.Page 2 (4,130) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 4 130 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.realization.basis .sphere 4 130 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.realization.basis .sphere 4 130 1 := he 1
  obtain ⟨_,a3,b3,ha3,hb3,hd,hbn⟩ := x1264_d3_coordinate I
  have hd3 : E.d 3 (4,130) a3=b3 := hd
  have hz1 : RepresentsOnPage E 3 (4,130) (I.realization.basis .sphere 4 130 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h156
  have frame (a : E.Page 3 (4,130)) : a=0 ∨ a=a3 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e
      (fun i=>if i=0 then a3 else 0) (by
        intro i
        rw [he i]
        fin_cases i
        · change RepresentsOnPage E 3 (4,130) (I.realization.basis .sphere 4 130 0) a3
          exact ha3
        · change RepresentsOnPage E 3 (4,130) (I.realization.basis .sphere 4 130 1) 0
          exact hz1) a
    simp only [Fin.sum_univ_two] at hc
    change a=(if c 0=0 then 0 else a3)+(if c 1=0 then 0 else 0) at hc
    simp only [ite_self,add_zero] at hc
    by_cases hc0 : c 0=0
    · exact Or.inl (by simpa only [hc0,ite_true] using hc)
    · exact Or.inr (by simpa only [hc0,ite_false] using hc)
  have ker0 (a : E.Page 3 (4,130)) (ha : E.d 3 (4,130) a=0) : a=0 := by
    rcases frame a with h|rfl
    · exact h
    · exact False.elim (hbn (hd3.symm.trans ha))
  have hall (a : E.Page 4 (4,130)) : a=0 := by
    have h := next_page_two_of_kernel E 3 (by change (2:ℤ)≤3; omega) (4,130) 0
      (fun b hb=>Or.inl (ker0 b hb)) a
    rcases h with h|h
    · exact h
    · simpa only [map_zero] using h
  exact ⟨fun a b=>(hall a).trans (hall b).symm⟩


private theorem t_incoming_t_incoming12 (I : Inputs D L G)
    (hit : HitOnPage (sequence D .sphere) 12 (14,139) (I.realization.sphere 14 139 T)) :
    Derived.Differential I.realization 12 dataH6Sq T := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,2,128,["69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 100) (by rfl))
  change E.Page 2 (2,128) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.realization.basis .sphere 2 128 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.realization.basis .sphere 2 128 0 := he 0
  have label : I.realization.sphere 2 128 dataH6Sq=I.realization.basis .sphere 2 128 0 := by
    have hc := I.csv (⟨.sphere,2,128,["69,2"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 100) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 1)
    have heq : dataH6Sq=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨69,by decide⟩ ^ 2 = projection (monomialOfString "69,2")
      have hs : "69,2"≠"" := by decide
      have hp : (("69,2".splitOn ",").map (fun n=>n.toNat?.getD 0))=[69,2] := by
        have split : "69,2".splitOn ","=["69","2"] := by simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,map_pow,pow_two]
    rw [heq]
    exact he
  obtain ⟨p,hp,z,y,hy,hyn,hd⟩ := hit
  have hq : p=(2,128) := add_right_cancel (hp.trans (show (14,139)=(2,128)+E.diffDeg 12 from rfl))
  subst p
  have hd' : E.d 12 (2,128) z=y := hd
  let A := E.ssData (2,128)
  haveI : Epi (A.pageπ 10) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨c,hc⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 10)).mp inferInstance z
  let x := (Subobject.ofLE (A.Z 10) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤10)) ≫ A.pageπ 0) c
  have hx : RepresentsOnPage E 12 (2,128) x z := ⟨by decide,c,rfl,hc⟩
  have hcases : x=0 ∨ x=I.realization.basis .sphere 2 128 0 := by
    have h : e x 0=0 ∨ e x 0=1 := by generalize e x 0=a; fin_cases a <;> simp
    rcases h with h|h
    · left
      apply e.injective
      apply Finsupp.ext
      intro i
      fin_cases i
      simpa using h
    · right
      rw [←he0]
      apply e.injective
      apply Finsupp.ext
      intro i
      fin_cases i
      simpa using h
  rcases hcases with h|h
  · rw [h] at hx
    have hz : z=0 := represents_unique hx (RepresentsOnPage.zero (by decide))
    exact False.elim (hyn (hd'.symm.trans (by rw [hz,map_zero])))
  · rw [h] at hx
    refine ⟨rfl,z,y,?_,hy,hd,hyn⟩
    rw [label]
    exact hx

private theorem t_only_incoming_h153 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 2 (3,130) (5,131) (I.realization.basis .sphere 3 130 1) (I.realization.basis .sphere 5 131 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 2, 3, 130, [1], 5, 131, [0], "S0_AdamsE2_ss", 2439⟩ (by
    exact List.mem_of_getElem? (i := 153) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (3,130) (5,131) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 5 131 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem t_only_incoming_h655 (I : Inputs D L G) : HasDifferential (sequence D .sphere) 3 (4,130) (7,132) (I.realization.basis .sphere 4 130 0) (I.realization.basis .sphere 7 132 0) := by
  classical
  have hrow := I.results ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "proofs.db/log", 929469⟩ (by
    exact List.mem_of_getElem? (i := 655) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (4,130) (7,132) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0] = true := rfl
  simp only [Realization.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem t_only_incoming (I : Inputs D L G) : Derived.OnlyIncomingT I.realization := by
  classical


  let E := sequence D .sphere
  have nohit (r : ℤ) (hd : E.d r ((14,139)-E.diffDeg r)=0) :
      ¬HitOnPage E r (14,139) (I.realization.sphere 14 139 T) := by
    rintro ⟨p,hp,z,y,hy,hyn,hzy⟩
    have he : p=(14,139)-E.diffDeg r := eq_sub_iff_add_eq.mpr hp
    subst p
    rw [hd] at hzy
    have hez : y=0 := by simpa using hzy.symm
    exact hyn hez
  have h6 (hit : HitOnPage E 6 (14,139) (I.realization.sphere 14 139 T)) :
      Derived.Differential I.realization 6 W T := by
    obtain ⟨p,hp,z,y,hy,hyn,hd⟩ := hit
    have hq : p=(8,134) := add_right_cancel (hp.trans (show (14,139)=(8,134)+E.diffDeg 6 from rfl))
    subst p
    have hd' : E.d 6 (8,134) z=y := hd
    obtain ⟨w,hw,hframe⟩ := t_incoming_t_incoming6_image I
    rcases hframe z with hz|hz
    · exact False.elim (hyn (hd'.symm.trans hz))
    · refine ⟨rfl,w,y,?_,hy,?_,hyn⟩
      · rw [t_incoming_w_label I]
        exact hw
      · change E.d 6 (8,134) w=y
        exact hz.symm.trans hd'
  intro r hit
  have hr : 2≤r := by
    obtain ⟨_,_,_,_,hy,_,_⟩ := hit
    exact hy.1
  by_cases hl : 13≤r
  · exact False.elim (nohit r (t_incoming_t_incoming_late_zero I r hl) hit)
  have hr' : r≤12 := by omega
  interval_cases r
  · exact False.elim (t_incoming_t_incoming2_not_hit I (by simpa only [t_incoming_t_label I] using hit))
  · exact False.elim (nohit 3 (by exact t_incoming_t_incoming3_zero I) hit)
  · exact False.elim (nohit 4 (by exact t_incoming_t_incoming4_zero I) hit)
  · have hs := t_incoming_t_incoming5_source_five I
    apply False.elim (nohit 5 ?_ hit)
    ext x
    change E.d 5 (9,135) x=0
    rw [hs.elim x 0,map_zero]
  · exact Or.inl ⟨rfl,h6 hit⟩
  · exact False.elim (nohit 7 (by exact t_incoming_t_incoming7_zero I) hit)
  · have hs : Subsingleton (E.Page 8 (6,132)) :=
      adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 8 6 132 (by decide) (by decide) (t_incoming_t_incoming8_source_four I)
    apply False.elim (nohit 8 ?_ hit)
    ext x
    change E.d 8 (6,132) x=0
    rw [hs.elim x 0,map_zero]
  · exact False.elim (nohit 9 (by exact t_incoming_t_incoming9_zero I) hit)
  · have hs : Subsingleton (E.Page 10 (4,130)) :=
      adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 10 4 130 (by decide) (by decide) (t_incoming_t_incoming10_source_four I)
    apply False.elim (nohit 10 ?_ hit)
    ext x
    change E.d 10 (4,130) x=0
    rw [hs.elim x 0,map_zero]
  · exact False.elim (nohit 11 (by exact t_incoming_t_incoming11_zero I) hit)
  · exact Or.inr ⟨rfl,t_incoming_t_incoming12 I hit⟩

private theorem sphere_t_incoming_and_survival (I : Inputs D L G) (V : SphereVanishingLine H) :
    (IsPermanentCycle (sequence D .sphere) (14,139) (I.realization.sphere 14 139 T)) ∧
    (Derived.Survival I.realization 6 W) ∧
    (DifferentialTargets (sequence D .sphere) 6 (8,134)
        (I.realization.sphere 8 134 W) (I.realization.sphere 14 139 T)) ∧
    (Derived.OnlyIncomingT I.realization) := by
  classical
  exact ⟨t_permanent_cycle I V, w_to_e6 I, w_d6_targets I, t_only_incoming I⟩

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
      -- Remaining subgoal of the original sphere_facts theorem: Prove the E3 target is nonzero: control d2 on the remaining source basis vector 23,1,190,1 (basis index 2 of Fin 5) in E2(14,138), in addition to the four computed directions.
      sorry
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
      -- Remaining subgoal of the original sphere_facts theorem: Exclude r=9 from E9(2,128) to Y in E9(11,136). ReachesPage 7 for h6^2 does not by itself rule out this differential.
      sorry
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

section CnuDifferential
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
local notation "E" => sequence D KIP126.Computation.Route.Raw.Spectrum.nuCofiber

/-- A common representative on page at least three is a d₂ cycle. -/
private theorem cnu_d2_zero_of_reaches (r : ℤ) (hr : 3 ≤ r)
    (x : (E).Page 2 (9,135)) (hx : ReachesPage E r (9,135) x) :
    (E).d 2 (9,135) x = 0 := by
  obtain ⟨xr, hr', z, hz, _⟩ := hx
  change x ∈ LinearMap.ker ((E).d 2 (9,135)).hom
  rw [← subobjectModule_kernel, (E).Z_succ 2 (9,135) (by change (2 : ℤ) ≤ 2; omega), subobjectModule_image]
  let A := (E).ssData (9,135)
  have hle : (1 : WithTop ℕ) ≤ ↑(r-2).toNat := by
    exact_mod_cast (show 1 ≤ (r-2).toNat by omega)
  refine ⟨(Subobject.ofLE (A.Z ↑(r-2).toNat) (A.Z 1) (A.Z_anti hle)) z, ?_⟩
  change (Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0)
    ((Subobject.ofLE (A.Z ↑(r-2).toNat) (A.Z 1) _) z) = x
  rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
  exact hz

/-- The complete five-element degree-(9,135) basis gives the whole d₂ map. -/
private theorem cnu_d2_decode (I : Inputs D L G) (i : Fin 5) : I.realization.decode .nuCofiber 9 135 [i.val] =
    some (I.realization.basis .nuCofiber 9 135 i.val) := by
  have hv : Raw.coordinatesValid Raw.degrees .nuCofiber 9 135 [i.val] = true := by
    fin_cases i <;> decide
  simp [Realization.decode, hv]

private theorem cnu_d2_target (p q : ℤ × ℤ) (x : (E).Page 2 p) (y : (E).Page 2 q)
    (h : HasDifferential E 2 p q x y) : (E).d 2 q y = 0 := by
  obtain ⟨rfl, hd⟩ := h.eq_on_page_two
  have hd' : (E).d 2 p x = y := by
    simpa only [eqToHom_refl, Category.comp_id] using hd
  exact IsPageBoundary.d_eq_zero (r := 2) (p := p) ⟨x, hd'⟩

private theorem cnu_d2_zero_h0 (I : Inputs D L G) : ((sequence D .nuCofiber)).d 2 (9,135) (I.realization.basis .nuCofiber 9 135 0) = 0 := by
  classical
  have hrow := I.results _ (List.mem_of_getElem? (i := 51) (by rfl))
  obtain ⟨x, hx, y, hy, h⟩ := hrow
  have hx' : x = I.realization.basis .nuCofiber 9 135 0 :=
    Option.some.inj (hx.symm.trans (cnu_d2_decode I ⟨0, by decide⟩))
  subst x
  obtain ⟨_, xr, yr, hxr, _, _⟩ := h
  exact cnu_d2_zero_of_reaches 3 (by decide) _ ⟨xr, hxr⟩

private theorem cnu_d2_zero_h1 (I : Inputs D L G) : ((sequence D .nuCofiber)).d 2 (9,135) (I.realization.basis .nuCofiber 9 135 1) = 0 := by
  classical
  have hrow := I.results _ (List.mem_of_getElem? (i := 49) (by rfl))
  obtain ⟨x, hx, h⟩ := hrow
  have hx' : x = I.realization.basis .nuCofiber 9 135 1 :=
    Option.some.inj (hx.symm.trans (cnu_d2_decode I ⟨1, by decide⟩))
  subst x
  exact cnu_d2_zero_of_reaches 16 (by decide) _ h

private theorem cnu_d2_zero_h2 (I : Inputs D L G) : ((sequence D .nuCofiber)).d 2 (9,135) (I.realization.basis .nuCofiber 9 135 2) = 0 := by
  classical
  have hrow := I.results _ (List.mem_of_getElem? (i := 50) (by rfl))
  obtain ⟨x, hx, y, hy, h⟩ := hrow
  have hx' : x = I.realization.basis .nuCofiber 9 135 2 :=
    Option.some.inj (hx.symm.trans (cnu_d2_decode I ⟨2, by decide⟩))
  subst x
  obtain ⟨_, xr, yr, hxr, _, _⟩ := h
  exact cnu_d2_zero_of_reaches 4 (by decide) _ ⟨xr, hxr⟩

private theorem cnu_d2_zero_h3 (I : Inputs D L G) : ((sequence D .nuCofiber)).d 2 (9,135) (I.realization.basis .nuCofiber 9 135 3) = 0 := by
  classical
  have hrow := I.results _ (List.mem_of_getElem? (i := 47) (by rfl))
  obtain ⟨x, hx, y, hy, h⟩ := hrow
  have hy' : y = I.realization.basis .nuCofiber 9 135 3 :=
    Option.some.inj (hy.symm.trans (cnu_d2_decode I ⟨3, by decide⟩))
  subst y
  exact cnu_d2_target (7,134) (9,135) x _ h

private theorem cnu_d2_zero_h4 (I : Inputs D L G) : ((sequence D .nuCofiber)).d 2 (9,135) (I.realization.basis .nuCofiber 9 135 4) = 0 := by
  classical
  have hrow := I.results _ (List.mem_of_getElem? (i := 48) (by rfl))
  obtain ⟨x, hx, y, hy, h⟩ := hrow
  have hy' : y = I.realization.basis .nuCofiber 9 135 4 :=
    Option.some.inj (hy.symm.trans (cnu_d2_decode I ⟨4, by decide⟩))
  subst y
  exact cnu_d2_target (7,134) (9,135) x _ h

private theorem cnu_d2_zero (I : Inputs D L G) : (E).d 2 (9,135) = 0 := by
  have h0 : (E).d 2 (9,135) (I.realization.basis .nuCofiber 9 135 0) = 0 := cnu_d2_zero_h0 I
  have h1 : (E).d 2 (9,135) (I.realization.basis .nuCofiber 9 135 1) = 0 := cnu_d2_zero_h1 I
  have h2 : (E).d 2 (9,135) (I.realization.basis .nuCofiber 9 135 2) = 0 := cnu_d2_zero_h2 I
  have h3 : (E).d 2 (9,135) (I.realization.basis .nuCofiber 9 135 3) = 0 := cnu_d2_zero_h3 I
  have h4 : (E).d 2 (9,135) (I.realization.basis .nuCofiber 9 135 4) = 0 := cnu_d2_zero_h4 I
  have hb := I.basis _ (List.mem_of_getElem? (i := 34) (by rfl))
  obtain ⟨e, he⟩ := hb
  change (E).Page 2 (9,135) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .nuCofiber 9 135 i.val at he
  have hone (i : Fin 5) : (E).d 2 (9,135) (e.symm (Finsupp.single i 1)) = 0 := by
    rw [he i]
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hall (f : Fin 5 →₀ KIP126.Core.Algebra.F2) : (E).d 2 (9,135) (e.symm f) = 0 := by
    induction f using Finsupp.induction with
    | zero => simp
    | @single_add i a f hi ha ih =>
      rw [map_add, map_add, ih, add_zero]
      fin_cases a
      · simp
      · exact hone i
  ext x
  simpa only [LinearEquiv.symm_apply_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using hall (e x)


/-- Add actual common cycle representatives, before quotienting on either page. -/
private theorem represents_add
    {R : Type*} [Ring R] {ESeq : KIP126.Core.SpectralSequence (ModuleCat R) (ℤ × ℤ)}
    {r : ℤ} {p : ℤ × ℤ} {x y : ESeq.Page 2 p} {xr yr : ESeq.Page r p}
    (hx : RepresentsOnPage ESeq r p x xr) (hy : RepresentsOnPage ESeq r p y yr) :
    RepresentsOnPage ESeq r p (x+y) (xr+yr) := by
  obtain ⟨hr, zx, hx, hxr⟩ := hx
  obtain ⟨_, zy, hy, hyr⟩ := hy
  exact ⟨hr, zx+zy, by rw [map_add, hx, hy], by rw [map_add, hxr, hyr]⟩

private theorem differential_add
    {R : Type*} [Ring R] {ESeq : KIP126.Core.SpectralSequence (ModuleCat R) (ℤ × ℤ)}
    {r : ℤ} {p q : ℤ × ℤ} {x x' : ESeq.Page 2 p} {y y' : ESeq.Page 2 q}
    (h : HasDifferential ESeq r p q x y) (h' : HasDifferential ESeq r p q x' y') :
    HasDifferential ESeq r p q (x+x') (y+y') := by
  obtain ⟨hdeg, xr, yr, hx, hy, hd⟩ := h
  obtain ⟨_, xr', yr', hx', hy', hd'⟩ := h'
  exact ⟨hdeg, xr+xr', yr+yr', represents_add hx hx', represents_add hy hy',
    by rw [map_add, hd, hd']⟩

/-- Unchanged boundaries preserve nonzero common representatives. -/
private theorem page_projection_nonzero
    {R : Type*} [Ring R] (A : SSData (ModuleCat R))
    (n m : WithTop ℕ) (hnm : n ≤ m) (hB : A.B m = A.B n)
    (z : (Subobject.underlying.obj (A.Z m) : ModuleCat R))
    (hne : (Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm) ≫ A.pageπ n) z ≠ 0) :
    A.pageπ m z ≠ 0 := by
  intro hz
  have hmem := (subobject_cokernel_π_eq_zero_iff (A.B m) (A.Z m) (A.B_le_Z m) z).mp hz
  apply hne
  rw [hB] at hmem
  change A.pageπ n ((Subobject.ofLE (A.Z m) (A.Z n) (A.Z_anti hnm)) z) = 0
  apply (subobject_cokernel_π_eq_zero_iff (A.B n) (A.Z n) (A.B_le_Z n) _).mpr
  change (Subobject.ofLE (A.Z m) (A.Z n) _ ≫ (A.Z n).arrow) z ∈ _
  rwa [Subobject.ofLE_arrow]


/-- Source [0,3,4] is the sum of the three Cnu source rows; the target is
bottom-cell [3].  The top/bottom identifications remain the fields of I,
so the later Mahowald application uses exactly D.auxiliary.nuMap. -/
theorem cnu_d3 (I : Inputs D L G) : Derived.CnuDifferential I.realization := by
  have hdecode (s t : ℕ) (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber s t indices = true) :
      I.realization.decode .nuCofiber s t indices =
        some ((indices.map (I.realization.basis .nuCofiber s t)).sum) := by
    simp only [Realization.decode, hv, ite_true]
  obtain ⟨x0, hx0, y0, hy0, h0⟩ :=
    I.results _ (List.mem_of_getElem? (i := 657) (by rfl))
  obtain ⟨x3, hx3, y3, hy3, h3⟩ :=
    I.results _ (List.mem_of_getElem? (i := 34) (by rfl))
  obtain ⟨x4, hx4, y4, hy4, h4⟩ :=
    I.results _ (List.mem_of_getElem? (i := 33) (by rfl))
  change Page D .nuCofiber 8 134 at x0 x3 x4
  change Page D .nuCofiber 11 136 at y0 y3 y4
  change HasDifferential E 3 (8,134) (11,136) x0 y0 at h0
  change HasDifferential E 3 (8,134) (11,136) x3 y3 at h3
  change HasDifferential E 3 (8,134) (11,136) x4 y4 at h4
  have hx0' : x0 = I.realization.basis .nuCofiber 8 134 0 := by
    have h := Option.some.inj (hx0.symm.trans (hdecode 8 134 [0] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using h
  have hx3' : x3 = I.realization.basis .nuCofiber 8 134 3 := by
    have h := Option.some.inj (hx3.symm.trans (hdecode 8 134 [3] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using h
  have hx4' : x4 = I.realization.basis .nuCofiber 8 134 4 := by
    have h := Option.some.inj (hx4.symm.trans (hdecode 8 134 [4] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using h
  have hy0' : y0 = I.realization.basis .nuCofiber 11 136 1 +
      I.realization.basis .nuCofiber 11 136 2 + I.realization.basis .nuCofiber 11 136 3 := by
    have h := Option.some.inj (hy0.symm.trans (hdecode 11 136 [1,2,3] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc] using h
  have hy3' : y3 = I.realization.basis .nuCofiber 11 136 2 := by
    have h := Option.some.inj (hy3.symm.trans (hdecode 11 136 [2] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using h
  have hy4' : y4 = I.realization.basis .nuCofiber 11 136 1 := by
    have h := Option.some.inj (hy4.symm.trans (hdecode 11 136 [1] (by decide)))
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using h
  obtain ⟨e, he⟩ := I.basis _ (List.mem_of_getElem? (i := 43) (by rfl))
  change (E).Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .nuCofiber 11 136 i.val at he
  have htwo (y : (E).Page 2 (11,136)) : y+y = 0 := by
    apply e.injective
    rw [map_add, map_zero]
    ext i
    exact CharTwo.add_self_eq_zero ((e y) i)
  have hne : I.realization.basis .nuCofiber 11 136 3 ≠ 0 := by
    rw [← he ⟨3, by decide⟩]
    intro hz
    have h := congrArg e hz
    simp only [LinearEquiv.apply_symm_apply, map_zero] at h
    change (Finsupp.single (⟨3, by decide⟩ : Fin 5) (1 : KIP126.Core.Algebra.F2)) = 0 at h
    exact Finsupp.single_ne_zero.mpr one_ne_zero h
  have hsum : y0+y3+y4 = I.realization.basis .nuCofiber 11 136 3 := by
    rw [hy0', hy3', hy4']
    calc
      _ = (I.realization.basis .nuCofiber 11 136 1 + I.realization.basis .nuCofiber 11 136 1) +
          (I.realization.basis .nuCofiber 11 136 2 + I.realization.basis .nuCofiber 11 136 2) +
          I.realization.basis .nuCofiber 11 136 3 := by abel
      _ = _ := by rw [htwo, htwo, zero_add, zero_add]
  have hd := differential_add (differential_add h0 h3) h4
  rw [hsum] at hd
  refine ⟨x0+x3+x4, I.realization.basis .nuCofiber 11 136 3, ?_, ?_, ?_⟩
  · rw [hdecode 8 134 [0,3,4] (by decide), hx0', hx3', hx4']
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]
  · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
      hdecode 11 136 [3] (by decide)
  · obtain ⟨hdeg, xr, yr, hxr, hyr, hd⟩ := hd
    refine ⟨hdeg, xr, yr, hxr, hyr, hd, ?_⟩
    obtain ⟨_, z, hz2, hz3⟩ := hyr
    have hB : ((E).ssData (11,136)).B 1 = ((E).ssData (11,136)).B 0 :=
      boundaries_succ_of_zero E 2 (by change (2 : ℤ) ≤ 2; omega) (9,135) (cnu_d2_zero I)
    rw [← hz3]
    exact page_projection_nonzero _ 0 1 (by simp) hB z (hz2 ▸ hne)

end CnuDifferential

open CategoryTheory.Limits in
/-- The finite Cnu incoming exclusion used at the end of Proposition 7.9.
It uses complete degrees, not just the single level-9000 target row. -/
private theorem cnu_d2_d3_incoming14_zero (I : Inputs D L G) :
    ((sequence D Raw.Spectrum.nuCofiber)).d 2 (11,137) = 0 ∧ ((sequence D Raw.Spectrum.nuCofiber)).d 3 (11,137) = 0 := by
  classical
  have hdecode (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber 11 137 indices = true) :
      I.realization.decode .nuCofiber 11 137 indices =
        some ((indices.map (I.realization.basis .nuCofiber 11 137)).sum) := by
    simp only [Realization.decode,hv,ite_true]
  have h0 : ∃ xr : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (11,137),
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (11,137) (I.realization.basis .nuCofiber 11 137 0) xr ∧
      ((sequence D Raw.Spectrum.nuCofiber)).d 3 (11,137) xr = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.results _ (List.mem_of_getElem? (i := 76) (by rfl))
    have hy' : y = I.realization.basis .nuCofiber 11 137 0 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode [0] (by decide)))
    subst y
    exact differential_target_cycle h
  have h3 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (11,137) (I.realization.basis .nuCofiber 11 137 3) 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.results _ (List.mem_of_getElem? (i := 75) (by rfl))
    have hy' : y = I.realization.basis .nuCofiber 11 137 3 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode [3] (by decide)))
    subst y
    exact differential_target_later_zero (by change (2 : ℤ) ≤ 2; omega) (by decide) h
  have h12 : ReachesPage (sequence D Raw.Spectrum.nuCofiber) 1000 (11,137)
      (I.realization.basis .nuCofiber 11 137 1 + I.realization.basis .nuCofiber 11 137 2) := by
    obtain ⟨x,hx,h⟩ := I.results _ (List.mem_of_getElem? (i := 77) (by rfl))
    have hx' : x = I.realization.basis .nuCofiber 11 137 1 + I.realization.basis .nuCofiber 11 137 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode [1,2] (by decide)))
    exact hx' ▸ h
  have h2 : ReachesPage (sequence D Raw.Spectrum.nuCofiber) 14 (11,137) (I.realization.basis .nuCofiber 11 137 2) := by
    obtain ⟨x,hx,h⟩ := I.results _ (List.mem_of_getElem? (i := 78) (by rfl))
    have hx' : x = I.realization.basis .nuCofiber 11 137 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode [2] (by decide)))
    exact hx' ▸ h
  obtain ⟨x12,hx12⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 1000) h12
  obtain ⟨x2,hx2⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 14) h2
  have hd12 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (11,137) x12 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 3; omega) (by decide) hx12 h12
  have hd2 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (11,137) x2 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 3; omega) (by decide) hx2 h2
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 44) (by rfl))
  change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (11,137) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .nuCofiber 11 137 i.val at he
  have hgen (i : Fin 4) : ∃ xr : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (11,137),
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (11,137) (e.symm (Finsupp.single i 1)) xr ∧ ((sequence D Raw.Spectrum.nuCofiber)).d 3 (11,137) xr = 0 := by
    rw [he]
    fin_cases i
    · exact h0
    · exact ⟨x12-x2, by simpa only [add_sub_cancel_right] using represents_sub hx12 hx2,
        by rw [map_sub,hd12,hd2,sub_self]⟩
    · exact ⟨x2,hx2,hd2⟩
    · exact ⟨0,h3,map_zero _⟩
  refine ⟨?_,d_zero_of_complete_representatives (by decide) e hgen⟩
  apply d_zero_of_complete_representatives (by decide) e
  intro i
  obtain ⟨xr,hxr,_⟩ := hgen i
  refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
  exact represents_d_zero_of_later (by change (2 : ℤ) ≤ 2; omega) (by decide)
    (represents_two_self _) ⟨xr,hxr⟩


private theorem cnu_10_136_data (I : Inputs D L G) :
    ((sequence D Raw.Spectrum.nuCofiber)).d 2 (10,136) = 0 ∧
    (∀ a : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (10,136),
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) 0 (((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a) ∨
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) (I.realization.basis .nuCofiber 13 138 1) (((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a)) ∧
    Subsingleton (((sequence D Raw.Spectrum.nuCofiber)).Page 4 (10,136)) := by
  classical
  have hdecode (s t : ℕ) (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber s t indices = true) :
      I.realization.decode .nuCofiber s t indices =
        some ((indices.map (I.realization.basis .nuCofiber s t)).sum) := by
    simp only [Realization.decode,hv,ite_true]
  obtain ⟨x,hx,y,hy,h⟩ := I.results _ (List.mem_of_getElem? (i := 64) (by rfl))
  have hx' : x = I.realization.basis .nuCofiber 10 136 0 := by
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
      Option.some.inj (hx.symm.trans (hdecode 10 136 [0] (by decide)))
  have hy' : y = I.realization.basis .nuCofiber 13 138 1 := by
    simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
      Option.some.inj (hy.symm.trans (hdecode 13 138 [1] (by decide)))
  subst x y
  change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 3 (10,136) (13,138) _ _ at h
  obtain ⟨hdeg,xr,yr,hxr,hyr,hd⟩ := h
  have hd' : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) xr = yr := by
    change ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) xr = yr at hd
    exact hd
  have hne : yr ≠ 0 := by
    obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 51) (by rfl))
    change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (13,138) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Core.Algebra.F2) at e
    change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .nuCofiber 13 138 i.val at he
    have hn : I.realization.basis .nuCofiber 13 138 1 ≠ 0 := by
      rw [← he ⟨1,by decide⟩]
      intro hz
      have hh := congrArg e hz
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      change (Finsupp.single (⟨1,by decide⟩ : Fin 4) (1 : KIP126.Core.Algebra.F2)) = 0 at hh
      exact Finsupp.single_ne_zero.mpr one_ne_zero hh
    obtain ⟨_,z,hz2,hz3⟩ := hyr
    have hB : (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).B 1 = (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).B 0 :=
      boundaries_succ_of_zero (sequence D Raw.Spectrum.nuCofiber) 2 (by change (2 : ℤ) ≤ 2; omega) (11,137)
        (cnu_d2_d3_incoming14_zero I).1
    rw [← hz3]
    exact page_projection_nonzero _ 0 1 (by simp) hB z (hz2 ▸ hn)
  have h1 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (10,136) (I.realization.basis .nuCofiber 10 136 1) 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.results _ (List.mem_of_getElem? (i := 62) (by rfl))
    have hy' : y = I.realization.basis .nuCofiber 10 136 1 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 10 136 [1] (by decide)))
    subst y
    exact differential_target_later_zero (by change (2 : ℤ) ≤ 2; omega) (by decide) h
  have h2 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (10,136) (I.realization.basis .nuCofiber 10 136 2) 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.results _ (List.mem_of_getElem? (i := 63) (by rfl))
    have hy' : y = I.realization.basis .nuCofiber 10 136 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 10 136 [2] (by decide)))
    subst y
    exact differential_target_later_zero (by change (2 : ℤ) ≤ 2; omega) (by decide) h
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 39) (by rfl))
  change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (10,136) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.realization.basis .nuCofiber 10 136 i.val at he
  have hbas (i : Fin 3) : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (10,136) (e.symm (Finsupp.single i 1)) (![xr,0,0] i) := by
    rw [he]
    fin_cases i
    · exact hxr
    · exact h1
    · exact h2
  have hd2 : ((sequence D Raw.Spectrum.nuCofiber)).d 2 (10,136) = 0 := by
    apply d_zero_of_complete_representatives (by decide) e
    intro i
    refine ⟨e.symm (Finsupp.single i 1),represents_two_self _,?_⟩
    exact represents_d_zero_of_later (by change (2 : ℤ) ≤ 2; omega) (by decide)
      (represents_two_self _) ⟨_,hbas i⟩
  have himage (a : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (10,136)) :
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) 0 (((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a) ∨
      RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) (I.realization.basis .nuCofiber 13 138 1) (((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a) := by
    obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e ![xr,0,0] hbas a
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,ite_self] at hc
    by_cases hc0 : c 0 = 0
    · have ha : a = 0 := by simpa only [hc0,ite_true] using hc
      left
      have hda : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a = (0 : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (13,138)) := by rw [ha,map_zero]
      exact hda.symm ▸ (RepresentsOnPage.zero (E := (sequence D Raw.Spectrum.nuCofiber)) (p := (13,138)) (by decide))
    · have ha : a = xr := by simpa only [hc0,ite_false] using hc
      right
      have hda : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a = yr := (congrArg (((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136)) ha).trans hd'
      exact hda.symm ▸ hyr
  have hzero (a : ((sequence D Raw.Spectrum.nuCofiber)).Page 4 (10,136)) : a = 0 := by
    haveI : Epi ((((sequence D Raw.Spectrum.nuCofiber)).ssData (10,136)).pageπ 2) := by
      change Epi (cokernel.π _)
      infer_instance
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective ((((sequence D Raw.Spectrum.nuCofiber)).ssData (10,136)).pageπ 2)).mp inferInstance a
    let x : ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (10,136) := (Subobject.ofLE _ _ ((((sequence D Raw.Spectrum.nuCofiber)).ssData (10,136)).Z_anti
      (show (0 : WithTop ℕ) ≤ 2 by simp)) ≫ (((sequence D Raw.Spectrum.nuCofiber)).ssData (10,136)).pageπ 0) z
    have hx4 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 4 (10,136) x a := ⟨by decide,z,rfl,hz⟩
    obtain ⟨ar,har⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 4) ⟨a,hx4⟩
    have hda : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) ar = 0 := represents_d_zero_of_later
      (by change (2 : ℤ) ≤ 3; omega) (by decide) har ⟨a,hx4⟩
    obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e ![xr,0,0] hbas ar
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,ite_self] at hc
    have ha0 : ar = 0 := by
      by_cases hc0 : c 0 = 0
      · simpa only [hc0,ite_true] using hc
      · have ha : ar = xr := by simpa only [hc0,ite_false] using hc
        rw [ha,hd'] at hda
        exact False.elim (hne hda)
    exact represents_later_zero (by decide : (3 : ℤ) ≤ 4) (ha0 ▸ har) hx4
  exact ⟨hd2,himage,⟨fun a b => (hzero a).trans (hzero b).symm⟩⟩


private theorem cnu_page4_target3_nonzero (I : Inputs D L G)
    (yr : ((sequence D Raw.Spectrum.nuCofiber)).Page 4 (13,138))
    (hy : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 4 (13,138) (I.realization.basis .nuCofiber 13 138 3) yr) : yr ≠ 0 := by
  classical
  have hB : (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).B 1 = (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).B 0 :=
    boundaries_succ_of_zero (sequence D Raw.Spectrum.nuCofiber) 2 (by change (2 : ℤ) ≤ 2; omega) (11,137)
      (cnu_d2_d3_incoming14_zero I).1
  have hback (x y : ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (13,138)) (a : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (13,138))
      (hx : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) x a) (hy : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) y a) : x = y := by
    obtain ⟨_,z,hz2,hz3⟩ := hx
    obtain ⟨_,z',hz2',hz3'⟩ := hy
    exact hz2.symm.trans ((same_boundaries_projection_eq _ 0 1 (by simp) hB z z'
      (hz3.trans hz3'.symm)).trans hz2')
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 51) (by rfl))
  change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (13,138) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .nuCofiber 13 138 i.val at he
  have hn0 : I.realization.basis .nuCofiber 13 138 3 ≠ 0 := by
    rw [← he ⟨3,by decide⟩]
    intro hz
    have hh := congrArg e hz
    simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
    change (Finsupp.single (⟨3,by decide⟩ : Fin 4) (1 : KIP126.Core.Algebra.F2)) = 0 at hh
    exact Finsupp.single_ne_zero.mpr one_ne_zero hh
  have hn1 : I.realization.basis .nuCofiber 13 138 3 ≠ I.realization.basis .nuCofiber 13 138 1 := by
    rw [← he ⟨3,by decide⟩,← he ⟨1,by decide⟩]
    intro hz
    have hh := e.symm.injective hz
    have hval := congrArg (fun f : Fin 4 →₀ KIP126.Core.Algebra.F2 => f ⟨3,by decide⟩) hh
    simp [Finsupp.single_apply] at hval
  intro hz
  obtain ⟨_,z,hz2,hz4⟩ := hy
  let ar : ((sequence D Raw.Spectrum.nuCofiber)).Page 3 (13,138) := (Subobject.ofLE _ _ ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z_anti
    (show (1 : WithTop ℕ) ≤ 2 by simp)) ≫ (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).pageπ 1) z
  have har : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) (I.realization.basis .nuCofiber 13 138 3) ar := by
    refine ⟨by decide,Subobject.ofLE _ _ ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z_anti
      (show (1 : WithTop ℕ) ≤ 2 by simp)) z,?_,rfl⟩
    change (Subobject.ofLE ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z 1) ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z 0) _ ≫
      (((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).pageπ 0)
      ((Subobject.ofLE ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z 2) ((((sequence D Raw.Spectrum.nuCofiber)).ssData (13,138)).Z 1) _) z) = _
    rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz2
  have hh := (next_projection_zero_iff_incoming (sequence D Raw.Spectrum.nuCofiber) 3
    (by change (2 : ℤ) ≤ 3; omega) (10,136) z).mp (hz4.trans hz)
  obtain ⟨a,ha⟩ := hh
  change ((sequence D Raw.Spectrum.nuCofiber)).d 3 (10,136) a = ar at ha
  rcases (cnu_10_136_data I).2.1 a with h0 | h1
  · have h0' : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) 0 ar := ha ▸ h0
    exact hn0 (hback _ _ _ har h0')
  · have h1' : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (13,138) (I.realization.basis .nuCofiber 13 138 1) ar := ha ▸ h1
    exact hn1 (hback _ _ _ har h1')


private theorem cnu_d5_incoming14_zero (I : Inputs D L G) : ((sequence D Raw.Spectrum.nuCofiber)).d 5 (9,135) = 0 := by
  classical
  have hdecode (s t : ℕ) (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber s t indices = true) :
      I.realization.decode .nuCofiber s t indices =
        some ((indices.map (I.realization.basis .nuCofiber s t)).sum) := by
    as_aux_lemma =>
      simp only [Realization.decode,hv,ite_true]
  obtain ⟨x0,hx0,y0,hy0,h0⟩ := I.results _ (List.mem_of_getElem? (i := 51) (by rfl))
  have hx0' : x0 = I.realization.basis .nuCofiber 9 135 0 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx0.symm.trans (hdecode 9 135 [0] (by decide)))
  have hy0' : y0 = I.realization.basis .nuCofiber 12 137 4 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy0.symm.trans (hdecode 12 137 [4] (by decide)))
  subst x0 y0
  change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 3 (9,135) (12,137) _ _ at h0
  obtain ⟨_,xr0,yr0,hxr0,hyr0,hd0⟩ := h0
  change ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) xr0 = yr0 at hd0
  have hn0 : yr0 ≠ 0 := by
    as_aux_lemma =>
      obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 47) (by rfl))
      change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Core.Algebra.F2) at e
      change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .nuCofiber 12 137 i.val at he
      have hn : I.realization.basis .nuCofiber 12 137 4 ≠ 0 := by
        as_aux_lemma =>
          rw [← he ⟨4,by decide⟩]
          intro hz
          have hh := congrArg e hz
          simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
          change (Finsupp.single (⟨4,by decide⟩ : Fin 5) (1 : KIP126.Core.Algebra.F2)) = 0 at hh
          exact Finsupp.single_ne_zero.mpr one_ne_zero hh
      obtain ⟨_,z,hz2,hz3⟩ := hyr0
      have hB : (((sequence D Raw.Spectrum.nuCofiber)).ssData (12,137)).B 1 = (((sequence D Raw.Spectrum.nuCofiber)).ssData (12,137)).B 0 :=
        boundaries_succ_of_zero (sequence D Raw.Spectrum.nuCofiber) 2 (by change (2 : ℤ) ≤ 2; omega) (10,136) (cnu_10_136_data I).1
      rw [← hz3]
      exact page_projection_nonzero _ 0 1 (by simp) hB z (hz2 ▸ hn)
  obtain ⟨x2,hx2,y2,hy2,h2⟩ := I.results _ (List.mem_of_getElem? (i := 50) (by rfl))
  have hx2' : x2 = I.realization.basis .nuCofiber 9 135 2 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx2.symm.trans (hdecode 9 135 [2] (by decide)))
  have hy2' : y2 = I.realization.basis .nuCofiber 13 138 3 := by
    as_aux_lemma =>
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy2.symm.trans (hdecode 13 138 [3] (by decide)))
  subst x2 y2
  change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 4 (9,135) (13,138) _ _ at h2
  obtain ⟨_,xr2,yr2,hxr2,hyr2,hd2⟩ := h2
  change ((sequence D Raw.Spectrum.nuCofiber)).d 4 (9,135) xr2 = yr2 at hd2
  have hn2 : yr2 ≠ 0 := cnu_page4_target3_nonzero I yr2 hyr2
  obtain ⟨x23,hx23⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 4) ⟨xr2,hxr2⟩
  have hd23 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) x23 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 3; omega) (by decide) hx23 ⟨xr2,hxr2⟩
  have h1 : ReachesPage (sequence D Raw.Spectrum.nuCofiber) 16 (9,135) (I.realization.basis .nuCofiber 9 135 1) := by
    as_aux_lemma =>
      obtain ⟨x,hx,h⟩ := I.results _ (List.mem_of_getElem? (i := 49) (by rfl))
      have hx' : x = I.realization.basis .nuCofiber 9 135 1 := by
        as_aux_lemma =>
          simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
            Option.some.inj (hx.symm.trans (hdecode 9 135 [1] (by decide)))
      exact hx' ▸ h
  obtain ⟨x13,hx13⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 16) h1
  obtain ⟨x14,hx14⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 4) (by decide : (4 : ℤ) ≤ 16) h1
  obtain ⟨x15,hx15⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 5) (by decide : (5 : ℤ) ≤ 16) h1
  have hd13 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) x13 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 3; omega) (by decide) hx13 h1
  have hd14 : ((sequence D Raw.Spectrum.nuCofiber)).d 4 (9,135) x14 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 4; omega) (by decide) hx14 h1
  have hd15 : ((sequence D Raw.Spectrum.nuCofiber)).d 5 (9,135) x15 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 5; omega) (by decide) hx15 h1
  have h3 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (9,135) (I.realization.basis .nuCofiber 9 135 3) 0 := by
    as_aux_lemma =>
      obtain ⟨x,hx,y,hy,h⟩ := I.results _ (List.mem_of_getElem? (i := 47) (by rfl))
      have hy' : y = I.realization.basis .nuCofiber 9 135 3 := by
        as_aux_lemma =>
          simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
            Option.some.inj (hy.symm.trans (hdecode 9 135 [3] (by decide)))
      subst y
      exact differential_target_later_zero (by change (2 : ℤ) ≤ 2; omega) (by decide) h
  have h4 : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (9,135) (I.realization.basis .nuCofiber 9 135 4) 0 := by
    as_aux_lemma =>
      obtain ⟨x,hx,y,hy,h⟩ := I.results _ (List.mem_of_getElem? (i := 48) (by rfl))
      have hy' : y = I.realization.basis .nuCofiber 9 135 4 := by
        as_aux_lemma =>
          simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
            Option.some.inj (hy.symm.trans (hdecode 9 135 [4] (by decide)))
      subst y
      exact differential_target_later_zero (by change (2 : ℤ) ≤ 2; omega) (by decide) h
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 34) (by rfl))
  change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (9,135) ≃ₗ[ℤ] (Fin 5 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.realization.basis .nuCofiber 9 135 i.val at he
  have hbas (i : Fin 5) : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (9,135) (e.symm (Finsupp.single i 1)) (![xr0,x13,x23,0,0] i) := by
    as_aux_lemma =>
      rw [he]
      fin_cases i
      · exact hxr0
      · exact hx13
      · exact hx23
      · exact h3
      · exact h4
  ext a
  change ((sequence D Raw.Spectrum.nuCofiber)).d 5 (9,135) a = 0
  obtain ⟨x,hx5⟩ := page_has_initial_representative (by decide) a
  obtain ⟨ar3,har3⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≤ 5) ⟨a,hx5⟩
  obtain ⟨ar4,har4⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 4) (by decide : (4 : ℤ) ≤ 5) ⟨a,hx5⟩
  have hda3 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) ar3 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 3; omega) (by decide) har3 ⟨a,hx5⟩
  have hda4 : ((sequence D Raw.Spectrum.nuCofiber)).d 4 (9,135) ar4 = 0 := represents_d_zero_of_later
    (by change (2 : ℤ) ≤ 4; omega) (by decide) har4 ⟨a,hx5⟩
  obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e ![xr0,x13,x23,0,0] hbas ar3
  have ha3 : ar3 = (if c 0=0 then 0 else xr0)+(if c 1=0 then 0 else x13)+(if c 2=0 then 0 else x23) := by
    as_aux_lemma =>
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,
        Matrix.cons_val_succ,ite_self,← add_assoc] at hc
      exact hc
  have hb13 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) (if c 1=0 then 0 else x13) = 0 := by
    as_aux_lemma =>
      split_ifs
      · exact map_zero _
      · exact hd13
  have hb23 : ((sequence D Raw.Spectrum.nuCofiber)).d 3 (9,135) (if c 2=0 then 0 else x23) = 0 := by
    as_aux_lemma =>
      split_ifs
      · exact map_zero _
      · exact hd23
  have hc0 : c 0=0 := by
    as_aux_lemma =>
      by_contra hne
      rw [ha3,map_add,map_add,hb13,hb23,add_zero,add_zero,if_neg hne,hd0] at hda3
      exact hn0 hda3
  have ha3' : ar3 = (if c 1=0 then 0 else x13)+(if c 2=0 then 0 else x23) := by
    as_aux_lemma =>
      simpa only [hc0,ite_true,zero_add] using ha3
  have hbit3 := represents_add (represents_bit (c 1) hx13) (represents_bit (c 2) hx23)
  have hbit3' : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 3 (9,135) _ ar3 := ha3'.symm ▸ hbit3
  have hbit4 := represents_add (represents_bit (c 1) hx14) (represents_bit (c 2) hxr2)
  have ha4 := represents_transport_eq (by decide : (3 : ℤ) ≤ 4) har3 hbit3' har4 hbit4
  have hb14 : ((sequence D Raw.Spectrum.nuCofiber)).d 4 (9,135) (if c 1=0 then 0 else x14) = 0 := by
    as_aux_lemma =>
      split_ifs
      · exact map_zero _
      · exact hd14
  have hc2 : c 2=0 := by
    as_aux_lemma =>
      by_contra hne
      rw [ha4,map_add,hb14,zero_add,if_neg hne,hd2] at hda4
      exact hn2 hda4
  have ha4' : ar4 = (if c 1=0 then 0 else x14) := by simpa only [hc2,ite_true,add_zero] using ha4
  have hbit4' : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 4 (9,135) _ ar4 := ha4'.symm ▸ (represents_bit (c 1) hx14)
  have ha5 := represents_transport_eq (by decide : (4 : ℤ) ≤ 5) har4 hbit4' hx5 (represents_bit (c 1) hx15)
  rw [ha5]
  split_ifs
  · exact map_zero _
  · exact hd15


private theorem cnu_d2_incoming14_image (I : Inputs D L G) (a : ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (12,138)) :
    ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) a = 0 ∨
    ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) a = I.realization.basis .nuCofiber 14 139 3 := by
  classical
  have hdecode (s t : ℕ) (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber s t indices = true) :
      I.realization.decode .nuCofiber s t indices =
        some ((indices.map (I.realization.basis .nuCofiber s t)).sum) := by
    simp only [Realization.decode,hv,ite_true]
  have h0 : ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) (I.realization.basis .nuCofiber 12 138 0) = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.results _ (List.mem_of_getElem? (i := 92) (by rfl))
    have hx' : x = I.realization.basis .nuCofiber 12 138 0 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode 12 138 [0] (by decide)))
    subst x
    obtain ⟨_,xr,_,hxr,_,_⟩ := h
    exact represents_d_zero_of_later (by change (2 : ℤ) ≤ 2; omega) (by decide)
      (represents_two_self _) ⟨xr,hxr⟩
  have h1 : ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) (I.realization.basis .nuCofiber 12 138 1) = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.results _ (List.mem_of_getElem? (i := 90) (by rfl))
    have hy' : y = I.realization.basis .nuCofiber 12 138 1 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 12 138 [1] (by decide)))
    subst y
    change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 2 (10,137) (12,138) x _ at h
    obtain ⟨yr,hyr,hd⟩ := differential_target_cycle h
    exact (congrArg (((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138)) hyr.eq_on_page_two).trans hd
  have h3 : ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) (I.realization.basis .nuCofiber 12 138 3) = 0 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.results _ (List.mem_of_getElem? (i := 91) (by rfl))
    have hy' : y = I.realization.basis .nuCofiber 12 138 3 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 12 138 [3] (by decide)))
    subst y
    change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 2 (10,137) (12,138) x _ at h
    obtain ⟨yr,hyr,hd⟩ := differential_target_cycle h
    exact (congrArg (((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138)) hyr.eq_on_page_two).trans hd
  have h2 : ((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138) (I.realization.basis .nuCofiber 12 138 2) =
      I.realization.basis .nuCofiber 14 139 3 := by
    obtain ⟨x,hx,y,hy,h⟩ := I.results _ (List.mem_of_getElem? (i := 93) (by rfl))
    have hx' : x = I.realization.basis .nuCofiber 12 138 2 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hx.symm.trans (hdecode 12 138 [2] (by decide)))
    have hy' : y = I.realization.basis .nuCofiber 14 139 3 := by
      simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
        Option.some.inj (hy.symm.trans (hdecode 14 139 [3] (by decide)))
    subst x y
    change HasDifferential (sequence D Raw.Spectrum.nuCofiber) 2 (12,138) (14,139) _ _ at h
    exact differential_two_direct h
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 48) (by rfl))
  change ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (12,138) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .nuCofiber 12 138 i.val at he
  have hbas (i : Fin 4) : RepresentsOnPage (sequence D Raw.Spectrum.nuCofiber) 2 (12,138) (e.symm (Finsupp.single i 1))
      (I.realization.basis .nuCofiber 12 138 i.val) := (he i) ▸ represents_two_self _
  obtain ⟨c,hc⟩ := page_eq_sum_of_complete_representatives (by decide) e
    (fun i => I.realization.basis .nuCofiber 12 138 i.val) hbas a
  have ha : a = (if c 0=0 then 0 else I.realization.basis .nuCofiber 12 138 0)+
      (if c 1=0 then 0 else I.realization.basis .nuCofiber 12 138 1)+
      (if c 2=0 then 0 else I.realization.basis .nuCofiber 12 138 2)+
      (if c 3=0 then 0 else I.realization.basis .nuCofiber 12 138 3) := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,← add_assoc] at hc
    exact hc
  let f : ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (12,138) →+ ((sequence D Raw.Spectrum.nuCofiber)).Page 2 (14,139) := (((sequence D Raw.Spectrum.nuCofiber)).d 2 (12,138)).hom.toAddMonoidHom
  change f (I.realization.basis .nuCofiber 12 138 0) = 0 at h0
  change f (I.realization.basis .nuCofiber 12 138 1) = 0 at h1
  change f (I.realization.basis .nuCofiber 12 138 2) = I.realization.basis .nuCofiber 14 139 3 at h2
  change f (I.realization.basis .nuCofiber 12 138 3) = 0 at h3
  have hd : f a = if c 2=0 then 0 else I.realization.basis .nuCofiber 14 139 3 := by
    rw [ha,map_add,map_add,map_add]
    split_ifs <;> simp only [map_zero,h0,h1,h2,h3,zero_add,add_zero]

  change f a = 0 ∨ f a = I.realization.basis .nuCofiber 14 139 3
  by_cases hc2 : c 2=0
  · exact Or.inl (by simpa only [hc2,ite_true] using hd)
  · exact Or.inr (by simpa only [hc2,ite_false] using hd)


theorem cnu_target_through5 (I : Inputs D L G) :
    Derived.CnuTargetThrough5 I.realization := by
  let S := sequence D Raw.Spectrum.nuCofiber

  -- Common representatives and actual boundary subobjects control passage between pages.
  -- Reconstruct all incoming maps from the complete degree-local bases.
  -- The nonzero d3 and d4 eliminate two source coordinates; the remaining class reaches page 16.
  -- At the final target, pages 3--5 add no boundaries, and the page-2 image is coordinate [3].
  have hdecode (indices : List ℕ)
      (hv : Raw.coordinatesValid Raw.degrees .nuCofiber 14 139 indices = true) :
      I.realization.decode .nuCofiber 14 139 indices =
        some ((indices.map (I.realization.basis .nuCofiber 14 139)).sum) := by
    as_aux_lemma =>
      simp only [Realization.decode,hv,ite_true]
  have hreach : ReachesPage S 1000 (14,139) (I.realization.basis .nuCofiber 14 139 2) := by
    as_aux_lemma =>
      obtain ⟨x,hx,h⟩ := I.results _ (List.mem_of_getElem? (i := 110) (by rfl))
      have hx' : x = I.realization.basis .nuCofiber 14 139 2 := by
        as_aux_lemma =>
          simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using
            Option.some.inj (hx.symm.trans (hdecode [2] (by decide)))
      exact hx' ▸ h
  obtain ⟨e,he⟩ := I.basis _ (List.mem_of_getElem? (i := 54) (by rfl))
  change (S).Page 2 (14,139) ≃ₗ[ℤ] (Fin 4 →₀ KIP126.Core.Algebra.F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.realization.basis .nuCofiber 14 139 i.val at he
  have hn0 : I.realization.basis .nuCofiber 14 139 2 ≠ 0 := by
    as_aux_lemma =>
      rw [← he ⟨2,by decide⟩]
      intro hz
      have hh := congrArg e hz
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      change (Finsupp.single (⟨2,by decide⟩ : Fin 4) (1 : KIP126.Core.Algebra.F2)) = 0 at hh
      exact Finsupp.single_ne_zero.mpr one_ne_zero hh
  have hn3 : I.realization.basis .nuCofiber 14 139 2 ≠ I.realization.basis .nuCofiber 14 139 3 := by
    as_aux_lemma =>
      rw [← he ⟨2,by decide⟩,← he ⟨3,by decide⟩]
      intro hz
      have hh := e.symm.injective hz
      have hval := congrArg (fun f : Fin 4 →₀ KIP126.Core.Algebra.F2 => f ⟨2,by decide⟩) hh
      simp [Finsupp.single_apply] at hval
  have hd4 : (S).d 4 (10,136) = 0 := by
    as_aux_lemma =>
      haveI := (cnu_10_136_data I).2.2
      ext x
      change (S).d 4 (10,136) x = 0
      rw [Subsingleton.elim x 0,map_zero]
  have hB2 : ((S).ssData (14,139)).B 2 = ((S).ssData (14,139)).B 1 :=
    boundaries_succ_of_zero S 3 (by change (2 : ℤ) ≤ 3; omega) (11,137) (cnu_d2_d3_incoming14_zero I).2
  have hB3 : ((S).ssData (14,139)).B 3 = ((S).ssData (14,139)).B 2 :=
    boundaries_succ_of_zero S 4 (by change (2 : ℤ) ≤ 4; omega) (10,136) hd4
  have hB4 : ((S).ssData (14,139)).B 4 = ((S).ssData (14,139)).B 3 :=
    boundaries_succ_of_zero S 5 (by change (2 : ℤ) ≤ 5; omega) (9,135) (cnu_d5_incoming14_zero I)
  have hB : ((S).ssData (14,139)).B 4 = ((S).ssData (14,139)).B 1 := hB4.trans (hB3.trans hB2)
  obtain ⟨yr,hyr⟩ := reaches_earlier (by decide : (2 : ℤ) ≤ 6) (by decide : (6 : ℤ) ≤ 1000) hreach
  have hne : yr ≠ 0 := by
    as_aux_lemma =>
      obtain ⟨_,z,hz2,hz6⟩ := hyr
      let z1 := (Subobject.ofLE (((S).ssData (14,139)).Z 4) (((S).ssData (14,139)).Z 1)
        (((S).ssData (14,139)).Z_anti (by simp))) z
      have hπ1 : ((S).ssData (14,139)).pageπ 1 z1 ≠ 0 := by
        as_aux_lemma =>
          intro hz1
          have hh := (next_projection_zero_iff_incoming S 2
            (by change (2 : ℤ) ≤ 2; omega) (12,138) z1).mp hz1
          obtain ⟨a,ha⟩ := hh
          have hπ2 : (Subobject.ofLE (((S).ssData (14,139)).Z 1) (((S).ssData (14,139)).Z 0)
              (((S).ssData (14,139)).Z_anti (by simp)) ≫
              ((S).ssData (14,139)).pageπ 0) z1 = I.realization.basis .nuCofiber 14 139 2 := by
            as_aux_lemma =>
              dsimp only [z1]
              rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
              exact hz2
          change (S).d 2 (12,138) a = (Subobject.ofLE (((S).ssData (14,139)).Z 1)
            (((S).ssData (14,139)).Z 0) _ ≫ ((S).ssData (14,139)).pageπ 0) z1 at ha
          rw [hπ2] at ha
          rcases cnu_d2_incoming14_image I a with hh | hh
          · exact hn0 (ha.symm.trans hh)
          · exact hn3 (ha.symm.trans hh)
      rw [← hz6]
      exact page_projection_nonzero _ 1 4 (by simp) hB z hπ1
  refine ⟨I.realization.basis .nuCofiber 14 139 2,?_,⟨yr,hyr,hne⟩,?_⟩
  · simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] using hdecode [2] (by decide)
  · refine ⟨by decide,by decide,?_⟩
    intro r hr hr5
    rintro ⟨q,hdeg,z,y,hy,hyne,hd⟩
    obtain ⟨x,hx⟩ := page_has_initial_representative hr z
    have hzero := differential_target_later_zero
      (by change (2 : ℤ) ≤ r; omega) (by omega : r < 6) ⟨hdeg,z,y,hx,hy,hd⟩
    exact hne (represents_unique hyr hzero)

/-- Public route expressions are exactly the CSV expressions interpreted
through I. The target equality includes associativity of the actual cobar
product: the two files parenthesize h1*h4*x_109_12 differently. -/
theorem route_expression_labels (I : Inputs D L G) :
    I.realization.sphere 8 134 W = L.W ∧
    I.realization.sphere 10 134 U = L.U M ∧
    I.realization.sphere 14 139 T = L.target M := by
  have hU := I.products ⟨2, 2, 8, 132⟩ (by simp [Raw.products]) h0Sq (atom .x_124_8)
  have h14 := I.products ⟨1, 2, 1, 16⟩ (by simp [Raw.products]) dataH1 (atom .h4)
  have hT := I.products ⟨2, 18, 12, 121⟩ (by simp [Raw.products])
    (mulAt dataH1 (atom .h4)) (atom .x_109_12)
  dsimp only at hU h14 hT
  have hAssoc : T = mulAt (mulAt dataH1 (atom .h4)) (atom .x_109_12) := by
    apply Subtype.ext
    exact (mul_assoc _ _ _).symm
  refine ⟨?_, ?_, ?_⟩
  · change I.realization.sphere 8 134
      (atom .x_126_8_4 + atom .x_126_8) = L.x_126_8_4 + L.x_126_8
    rw [map_add, I.labels.x_126_8_4, I.labels.x_126_8]
  · simpa only [U, Labels.U, I.labels.h0_square, I.labels.x_124_8] using hU
  · rw [hAssoc, hT, h14, I.labels.h1, I.labels.h4, I.labels.x_109_12]
    rfl

/-- The high class used by the C tables and the high class used by the tmf
source have precisely the same product and factors, on this same M. -/
theorem high125_label (I : Inputs D L G) :
    I.realization.sphere 25 150 highClass = G.high125 M := by
  have h2 := I.products ⟨4, 24, 4, 24⟩ (by simp [Raw.products]) (atom .g) (atom .g)
  have h4 := I.products ⟨8, 48, 8, 48⟩ (by simp [Raw.products])
    (mulAt (atom .g) (atom .g)) (mulAt (atom .g) (atom .g))
  have hHigh := I.products ⟨16, 96, 9, 54⟩ (by simp [Raw.products])
    (mulAt (mulAt (atom .g) (atom .g)) (mulAt (atom .g) (atom .g)))
    (atom .delta_h_1_mul_g)
  dsimp only at h2 h4 hHigh
  change I.realization.sphere 25 150
    (mulAt (mulAt (mulAt (atom .g) (atom .g)) (mulAt (atom .g) (atom .g)))
      (atom .delta_h_1_mul_g)) = _
  rw [hHigh, h4, h2, I.labels.g, I.labels.delta_h_1_mul_g]
  rfl

/-- The classical F26 vanishing needed to remove the indeterminacy of BMQ's
high125 detector.  Associated-graded convergence alone is insufficient:
Hausdorffness of this actual classical filtration is an explicit hypothesis.
It is a structural proof obligation, not an additional numerical A/C input. -/
theorem classical_stem125_filtration26_zero (I : Inputs D L G)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (a : HomotopyGroup (C := C) 125 SphereSpectrum)
    (ha : a ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 26 125) : a = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    have hpage (s : ℕ) (hs : 26 ≤ s) :
        Subsingleton ((sequence D .sphere).Page 5 (s, (s : ℤ) + 125)) := by
      by_cases h64 : s ≤ 64
      · exact stem125_e5_zero_finite I s hs h64
      · exact sphere_page_zero_stem125_tail (D := D) V 5 s (by omega) (by omega)
    have hstep (s : ℕ) (hs : 26 ≤ s)
        (has : a ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum s 125) :
        a ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum (s + 1) 125 := by
      let E := (sequence D .sphere).ssData (s, (s : ℤ) + 125)
      haveI : Subsingleton (E.page 3) := hpage s hs
      have hInf (z : E.eInfty) : z = 0 := by
        haveI : Epi (E.pageπ ⊤) := inferInstanceAs
          (Epi (CategoryTheory.Limits.cokernel.π _))
        obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (E.pageπ ⊤)).mp inferInstance z
        have h := E.infinity_projection_eq_of_page_projection_eq 3 y 0
          (Subsingleton.elim _ _)
        change E.pageπ ⊤ y = 0
        simpa only [map_zero] using h
      have e : E.eInfty ≅
          (TowerDetection.filtration H.unit SphereSpectrum).associatedGraded s 125 := by
        dsimp only [E, sequence, object]
        simpa only [ClassicalObject.obj, add_sub_cancel_left] using
          (D.classicalConvergence .sphere).identification (s, (s : ℤ) + 125)
      have hmem : a ∈ (ModuleCat.subobjectModule _)
          ((TowerDetection.filtration H.unit SphereSpectrum).F s 125) := by
        simpa only [TowerDetection.filtration, OrderIso.apply_symm_apply] using has
      obtain ⟨b, hb⟩ := hmem
      change ((TowerDetection.filtration H.unit SphereSpectrum).F s 125).arrow b = a at hb
      have hzero : (TowerDetection.filtration H.unit SphereSpectrum).toAssociatedGraded
          s 125 b = 0 := by
        have h := congrArg e.hom (hInf
          (e.inv ((TowerDetection.filtration H.unit SphereSpectrum).toAssociatedGraded s 125 b)))
        simpa only [← CategoryTheory.comp_apply, Category.assoc, Iso.inv_hom_id,
          Category.comp_id, map_zero] using h
      have hnext := (subobject_cokernel_π_eq_zero_iff
        ((TowerDetection.filtration H.unit SphereSpectrum).F ((s : ℤ) + 1) 125)
        ((TowerDetection.filtration H.unit SphereSpectrum).F s 125)
        ((TowerDetection.filtration H.unit SphereSpectrum).mono s 125) b).mp hzero
      rw [hb] at hnext
      simpa only [TowerDetection.filtration, OrderIso.apply_symm_apply] using hnext
    apply S 125 a
    intro s
    by_cases hs : s ≤ 26
    · exact TowerDetection.filtrationSubmodule_antitone H.unit SphereSpectrum 125
        (by exact_mod_cast hs) ha
    · have h26 : 26 ≤ s := by omega
      clear hs
      induction s, h26 using Nat.le_induction with
      | base => exact ha
      | succ n hn ih =>
        simpa only [Nat.cast_add, Nat.cast_one] using hstep n hn ih

/-- Equality of two classical representatives follows only after proving
the higher-filtration indeterminacy zero.  The detection relation itself
remains associated-graded equality; it has not been replaced by strict equality. -/
theorem high125_detected_choice_unique (I : Inputs D L G)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (a b : HomotopyGroup (C := C) 125 SphereSpectrum)
    (ha : TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (I.realization.sphere 25 150 highClass) a)
    (hb : TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (I.realization.sphere 25 150 highClass) b) : a = b := by
  set_option backward.isDefEq.respectTransparency false in
    dsimp only [TowerDetection.Detects, ClassicalObject.obj] at ha hb
    obtain ⟨z, hz, a', ha', hga⟩ := ha
    obtain ⟨z', hz', b', hb', hgb⟩ := hb
    have heq := ((sequence D .sphere).ssData (25, 150)).infinity_projection_eq_of_page_projection_eq 0 z z' (hz.trans hz'.symm)
    have hzero : (TowerDetection.filtration H.unit SphereSpectrum).toAssociatedGraded 25 (150 - 25) (a' - b') = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (hga.symm.trans
        ((congrArg ((D.classicalConvergence .sphere).identification (25, 150)).hom heq).trans hgb))
    have hmem := (subobject_cokernel_π_eq_zero_iff
      ((TowerDetection.filtration H.unit SphereSpectrum).F 26 (150 - 25))
      ((TowerDetection.filtration H.unit SphereSpectrum).F 25 (150 - 25))
      ((TowerDetection.filtration H.unit SphereSpectrum).mono 25 (150 - 25))
      (a' - b')).mp hzero
    rw [map_sub, ha', hb'] at hmem
    have hab : a - b ∈
        TowerDetection.filtrationSubmodule H.unit SphereSpectrum 26 (150 - 25) := by
      simpa only [TowerDetection.filtration, OrderIso.apply_symm_apply] using hmem
    exact sub_eq_zero.mp (classical_stem125_filtration26_zero I V S (a - b) hab)

end
end KIP126.Computation.Route
