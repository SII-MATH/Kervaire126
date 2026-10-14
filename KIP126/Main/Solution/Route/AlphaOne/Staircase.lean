module

public import KIP126.Def.Kervaire.Route.Section7.AlphaOne
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.LinProgram.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Main.Solution.Computation.Route.Bounds


import all Init.Data.String.Search
import all Init.Data.String.Slice

import all Init.Data.String.Legacy

@[expose] public section


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
open KIP126.Literature.Route
noncomputable section

-- Preserve the outer local attribute preceding this section in AlphaOne.
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
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
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
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]; first | decide | exact (List.mergeSort_of_pairwise (by decide)).symm
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

end
end KIP126.Main.Solution.Route.Section7
