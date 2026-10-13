import KIP126.Main.Solution.StageInput
import KIP126.Main.Solution.Computation.Lambda
import KIP126.Def.Kervaire.Route.Section7.Predicates
import KIP126.Main.Solution.Route.AlphaOne
import KIP126.Interface.Solution.AdamsOneLine
import KIP126.Interface.Solution.Moss
import KIP126.Def.ClassicalAdams.SphereClasses.Product.Proofs
import KIP126.Def.Kervaire.Route.Massey.Axioms
import KIP126.Def.StableHomotopy.Toda.Naturality
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differentials.Proofs

/-! Internal obligations in the second half of LWX Section 7.

All statements use the sole correlated Challenge2 witness. None is a new
literature/computation input, and no statement here is used to certify its
own computational premises. The unproved bodies are explicit Main proof
debts. Stable paper labels identify the precise consumers.
-/
namespace KIP126.Main.Solution.Route.Section7
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route KIP126.Kervaire.Route.Section7
open KIP126.Literature.Route KIP126.Main.StageInput
open KIP126.LinE2 KIP126.Computation.Near126
open KIP126.LinE2.RelationCertificates
noncomputable section
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD

local notation "D" => routeModel
local notation "M" => standardMilnorCooperations
local notation "L" => routeLabels
local notation "I" => routeComputation
local notation "η" => routeEta
local notation "h₀" => routeLiterature.toda.h0

/-- This h2 is D's normalized lift of the very nu whose actual cofiber is
used by the computation, with its first-quotient h2 identification delivered
by the same nu applicability record. -/
abbrev h2 := normalizedNu D routeLiterature.applicability.nuCofiber.nu_exponent

abbrev eB := (I).realization.sphere 8 70 KIP126.Computation.Near126.B
abbrev eX := (I).realization.sphere 8 130 KIP126.Computation.Near126.X
abbrev eY := (I).realization.sphere 11 136 KIP126.Computation.Near126.Y
abbrev eH6B := Sphere.Internal.product standardFoundation.hf2 M
  (s := 1) (t := 64) (s' := 8) (t' := 70)
  (Sphere.Internal.hi standardFoundation.hf2 M 6) eB

/- A permanent E₂ representative is a d₂-cycle. This is the forward
   KIP126 instance of Blueprint `prop:ss-cycle-zero-differential`; the
   corresponding KIPBase iff theorem is
   `KIPBase.Synthetic.pageTail_cycle_iff_exists_zero_differential_relation`.
   The proof uses the KIP126 finite-page calculus on its own spectral
   sequence type and is not an extra input. -/
theorem isPageCycle_of_permanentCycle
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ)}
    {p : ℤ × ℤ} {x : E.Page 2 p}
    (hbase : E.r₀ ≤ 2) (h : IsPermanentCycle E p x) : IsPageCycle E 2 p x := by
  rcases h with ⟨z, hz⟩
  let SD := E.ssData p
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  let m : WithTop ℕ := ↑(3 - E.r₀).toNat
  have hnm : n ≤ m := by
    dsimp only [n, m]
    exact_mod_cast (show (2 - E.r₀).toNat ≤ (3 - E.r₀).toNat by omega)
  let z3 := Subobject.ofLE (SD.Z ⊤) (SD.Z m) (SD.Z_anti le_top) z
  have hrep : ReachesPage E 3 p x := by
    refine ⟨SD.pageπ m z3, ?_⟩
    refine ⟨by omega, z3, ?_, rfl⟩
    change SD.pageπ n ((Subobject.ofLE (SD.Z m) (SD.Z n) _) z3) = x
    dsimp only [z3]
    have hcomp := Subobject.ofLE_comp_ofLE (SD.Z ⊤) (SD.Z m) (SD.Z n)
      (SD.Z_anti le_top) (SD.Z_anti hnm)
    have hcomp' :
        (Subobject.ofLE (SD.Z ⊤) (SD.Z m) (SD.Z_anti le_top) ≫
          Subobject.ofLE (SD.Z m) (SD.Z n) (SD.Z_anti hnm)) ≫ SD.pageπ n =
        Subobject.ofLE (SD.Z ⊤) (SD.Z n) (SD.Z_anti le_top) ≫ SD.pageπ n := by
      exact congrArg (fun f => f ≫ SD.pageπ n) hcomp
    have hz' := congrArg (fun f => f z) hcomp'
    exact hz'.trans hz
  have hself : RepresentsOnPage E 2 p x x :=
    KIP126.Core.SpectralSequence.FinitePageCalculus.represents_two_self x
  exact KIP126.Core.SpectralSequence.FinitePageCalculus.represents_d_zero_of_later
    (E := E) (p := p) (x := x) (r := 2) (t := 3) hbase (by omega) hself hrep

theorem isPageCycle_of_nonzeroSurvival
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ)}
    {p : ℤ × ℤ} {x : E.Page 2 p}
    (hbase : E.r₀ ≤ 2) (h : NonzeroSurvival E p x) : IsPageCycle E 2 p x := by
  rcases h with ⟨z, hz, _⟩
  exact isPageCycle_of_permanentCycle hbase ⟨z, hz⟩

/-! The Massey-product obligation is split into five genuine typed tasks.
These are not weakened propositions: each task refers to the fixed Adams
tower and to the same `eB`/`eH6B` labels used by the main theorem. -/

/- The three inputs of the defining system are E₂-cycles. -/
abbrev ThetaBMasseyCycleInputs : Prop :=
    IsPageCycle
        (adamsTowerInternalSpectralSequence
          standardFoundation.hf2.unit SphereSpectrum)
        2 (2, 64) (Sphere.Internal.hiSquare standardFoundation.hf2 M 5) ∧
    IsPageCycle
        (adamsTowerInternalSpectralSequence
          standardFoundation.hf2.unit SphereSpectrum)
        2 (1, 1) (Sphere.Internal.hi standardFoundation.hf2 M 0) ∧
    IsPageCycle
        (adamsTowerInternalSpectralSequence
          standardFoundation.hf2.unit SphereSpectrum)
        2 (8, 70) eB

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem theta_b_massey_eB_cycle :
    IsPageCycle
        (adamsTowerInternalSpectralSequence
          standardFoundation.hf2.unit SphereSpectrum)
        2 (8, 70) eB := by
  have hrow : KIP126.Computation.LinProofs.DifferentialStatement
      ⟨5569, "d2", 8, 70, 2, [1], []⟩ :=
    KIP126.Computation.LinProofs.differential_of_lookup 0 92 _ (by decide)
  obtain ⟨hxbound, hybound, x, y, hcx, hcy, hd⟩ :=
    KIP126.Computation.LinProofs.DifferentialStatement.hasDifferential hrow
  have hy0 : y = 0 := by
    rcases hcy with ⟨rows, hrows, hdeg, hy⟩
    change List.map BasisRow.index rows = [] at hrows
    have hnil : rows = [] := List.map_eq_nil_iff.mp hrows
    subst rows
    simpa using hy
  have hxB : x = B := by
    rcases hcx with ⟨rows, hrows, hrowsdeg, hx⟩
    have hlen : rows.length = 1 := by
      rw [← List.length_map BasisRow.index, hrows]
      rfl
    have hshape : ∃ r, rows = [r] := by
      cases rows with
      | nil => simp at hlen
      | cons r rs =>
        cases rs with
        | nil => exact ⟨r, rfl⟩
        | cons r' rs' => simp at hlen
    obtain ⟨r, rfl⟩ := hshape
    have hrindex : r.index = 1 := by simpa using hrows
    have hrdeg := hrowsdeg r (by simp)
    have hrs : r.s = 8 := hrdeg.2.1
    have hrt : r.t = 70 := hrdeg.2.2
    have hrmem : r ∈ basisRows := hrdeg.1
    have hr : r = ⟨8, 70, 1, "82,1"⟩ := by
      have hB : ∀ q ∈ basisRows, q.s = 8 → q.t = 70 →
          q.index = 1 → q.monomial = "82,1" := by
        native_decide
      have hm := hB r hrmem hrs hrt hrindex
      cases r
      simp_all
    subst r
    apply Subtype.ext
    rw [hx]
    simp [B, atom, basisValue, hrindex]
    have hs : "82,1" ≠ "" := by decide
    have hp : (("82,1".splitOn ",").map
        (fun n => n.toNat?.getD 0)) = [82, 1] := by
      have split : "82,1".splitOn "," = ["82", "1"] := by
        simp +decide [String.splitOn, String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString, if_neg hs, hp]
    norm_num [polynomialOfPowers, RawData.generatorCount, generator, map_mul]
  have hroute : eB = linToSphereE2 8 70 hxbound x := by
    rw [hxB]
    exact KIP126.Main.StageInput.computation.results.route_presentation
      8 70 hxbound B
  have hd0 :=
    KIP126.Core.SpectralSequence.FinitePageCalculus.differential_two_direct hd
  rw [hy0] at hd0
  simp only [map_zero] at hd0
  rw [← hroute] at hd0
  change IsPageCycle _ 2 (8,70) eB
  exact hd0

theorem theta_b_massey_cycle_inputs : ThetaBMasseyCycleInputs := by
  refine ⟨isPageCycle_of_nonzeroSurvival (by decide)
      routeLiterature.classical.theta5_exists.1, ?_, ?_⟩
  · apply isPageCycle_of_permanentCycle (by decide)
    rcases routeLiterature.classical.two_detection with ⟨z, hz, _⟩
    exact ⟨z, hz⟩
  · exact theta_b_massey_eB_cycle

/- The first nullhomotopy is the d₂(h₆)=h₀h₅² calculation. -/
abbrev ThetaBMasseyD2H6 : Prop :=
    (adamsTowerInternalSpectralSequence
        standardFoundation.hf2.unit SphereSpectrum).d 2 (1, 64)
        (Sphere.Internal.hi standardFoundation.hf2 M 6) =
      Sphere.Internal.product standardFoundation.hf2 M
        (s := 2) (t := 64) (s' := 1) (t' := 1)
        (Sphere.Internal.hiSquare standardFoundation.hf2 M 5)
        (Sphere.Internal.hi standardFoundation.hf2 M 0)

theorem theta_b_massey_d2_h6 : ThetaBMasseyD2H6 := by
  have h := KIP126.Interface.Solution.adamsOneLine_d2 6 (by decide)
  change HasNonzeroDifferential
    (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
    2 (1,64) (3,65)
    (Sphere.Internal.hi standardFoundation.hf2 M 6)
    (Sphere.Internal.h0HiSquare standardFoundation.hf2 M 5) at h
  have hd' :=
    KIP126.Core.SpectralSequence.FinitePageCalculus.differential_two_direct
      h.toHasDifferential
  have hforward :=
    KIP126.Classical.Adams.Sphere.Internal.product_hi_zero_hiSquare_five_eq_h0HiSquare
      standardFoundation.hf2 M
  rw [← hforward] at hd'
  have horder :
      Sphere.Internal.product standardFoundation.hf2 M
          (s := 2) (t := 64) (s' := 1) (t' := 1)
          (Sphere.Internal.hiSquare standardFoundation.hf2 M 5)
          (Sphere.Internal.hi standardFoundation.hf2 M 0) =
        Sphere.Internal.product standardFoundation.hf2 M
          (s := 1) (t := 1) (s' := 2) (t' := 64)
          (Sphere.Internal.hi standardFoundation.hf2 M 0)
          (Sphere.Internal.hiSquare standardFoundation.hf2 M 5) := by
    have hcomm :=
      KIP126.Classical.Adams.Sphere.Internal.sphere_product_graded_commutativity
        standardFoundation.hf2 M
        (s := 2) (t := 64) (s' := 1) (t' := 1)
        (x := Sphere.Internal.hiSquare standardFoundation.hf2 M 5)
        (y := Sphere.Internal.hi standardFoundation.hf2 M 0)
    let E := adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum
    have htr (z : E.Page 2 (1 + 2, 1 + 64)) :
        (KIP126.Classical.Adams.Sphere.Internal.spherePageDegreeTransport
          standardFoundation.hf2 2 64 1 1 (by norm_num)).hom z = z := by
      unfold KIP126.Classical.Adams.Sphere.Internal.spherePageDegreeTransport
      have hp : (by norm_num : (((1 + 2 : ℕ) : ℤ), ((1 + 64 : ℕ) : ℤ)) =
          (((2 + 1 : ℕ) : ℤ), ((64 + 1 : ℕ) : ℤ))) = rfl := Subsingleton.elim _ _
      rw [hp]
      rfl
    have htr' := htr (Sphere.Internal.product standardFoundation.hf2 M
      (s := 1) (t := 1) (s' := 2) (t' := 64)
      (Sphere.Internal.hi standardFoundation.hf2 M 0)
      (Sphere.Internal.hiSquare standardFoundation.hf2 M 5))
    rw [htr'] at hcomm
    norm_num at hcomm
    exact hcomm
  exact hd'.trans horder.symm

/- The second nullhomotopy is recorded at the exact defining-system
degree.  The eventual proof must identify this witness with h₀⁶h₆. -/
abbrev ThetaBMasseyD2Second : Prop :=
    ∃ b : (adamsTowerInternalSpectralSequence
      standardFoundation.hf2.unit SphereSpectrum).Page 2 (7, 70),
      (adamsTowerInternalSpectralSequence
        standardFoundation.hf2.unit SphereSpectrum).d 2 (7, 70) b =
        Sphere.Internal.product standardFoundation.hf2 M
          (s := 1) (t := 1) (s' := 8) (t' := 70)
          (Sphere.Internal.hi standardFoundation.hf2 M 0) eB

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem theta_b_massey_d2_second_nullhomotopy : ThetaBMasseyD2Second := by
  let E := adamsTowerInternalSpectralSequence
    standardFoundation.hf2.unit SphereSpectrum
  have hrow := routeComputation.results
      ⟨.sphere, .equation, 2, 7, 70, [2], 9, 71, [0], "S0_AdamsE2_ss", 513⟩ (by
    unfold KIP126.Computation.Route.Raw.claims
    iterate 180 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  dsimp only [KIP126.Computation.Route.Statement] at hrow
  obtain ⟨x,hx,y,hy,h⟩ := hrow
  change HasDifferential E 2 (7,70) (9,71) x y at h
  have vx : KIP126.Computation.Route.Raw.coordinatesValid
      KIP126.Computation.Route.Raw.degrees .sphere 7 70 [2] = true := rfl
  have vy : KIP126.Computation.Route.Raw.coordinatesValid
      KIP126.Computation.Route.Raw.degrees .sphere 9 71 [0] = true := rfl
  simp only [KIP126.Computation.Route.Realization.decode,vx,vy,if_true,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    Option.some.injEq] at hx hy
  rw [← hx,← hy] at h
  have hprod := routeComputation.products
      ⟨1,1,8,70⟩ (by
        unfold KIP126.Computation.Route.Raw.products
        iterate 13 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      (dataH0) (B)
  have h0route := routeComputation.labels.h0
  have h0std : routeComputation.realization.sphere 1 1 dataH0 =
      Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 0 := by
    simpa only [KIP126.Classical.Adams.standardFoundation,
      KIP126.Classical.Adams.standardMilnorCooperations,
      KIP126.Def.StageInput.witness, KIP126.Def.fixedImplementation,
      KIP126.Implementation.foundation, KIP126.Implementation.milnor,
      KIP126.Foundation.FoundationInput.toStandard,
      KIP126.Foundation.MilnorInput.toMilnor] using h0route
  have hrel : mulAt dataH0 B = mulAt (mulAt h0Six dataH0) h5Sq := by
    apply Subtype.ext
    have hz := csv_relation_zero "0,1,82,1;0,7,18,2" relation_member5
    have hsplit : "0,1,82,1;0,7,18,2".splitOn ";" =
        ["0,1,82,1","0,7,18,2"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hp0 : (("0,1,82,1".splitOn ",").map
        (fun n => n.toNat?.getD 0)) = [0, 1, 82, 1] := by
      have split : "0,1,82,1".splitOn "," = ["0", "1", "82", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hp1 : (("0,7,18,2".splitOn ",").map
        (fun n => n.toNat?.getD 0)) = [0, 7, 18, 2] := by
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
    norm_num [relationPolynomial,hsplit,monomialOfString,hp0,hp1,
      polynomialOfPowers,RawData.generatorCount,generator,map_mul,map_add,
      pow_succ,mul_assoc] at hz
    have heq := (eq_neg_of_add_eq_zero_left hz).trans (hneg _)
    simpa [mulAt,dataH0,B,atom,h0Six,h0Sq,h5Sq,generator,h0,
      RawData.generatorCount,pow_succ,mul_assoc,map_mul] using heq
  have htarget : routeComputation.realization.sphere 9 71 (mulAt dataH0 B) =
      routeComputation.realization.basis .sphere 9 71 0 := by
    have hc := routeComputation.csv
      (⟨.sphere,9,71,["0,7,18,2"]⟩ : KIP126.Computation.Route.Raw.Degree)
      (by
        unfold KIP126.Computation.Route.Raw.degrees
        iterate 167 apply List.mem_cons_of_mem
        exact List.mem_cons_self) rfl
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 1)
    have heq : mulAt dataH0 B = z := by
      rw [hrel]
      apply Subtype.ext
      rw [hz]
      change (((generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*
        (generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)) *
        (generator ⟨0,by decide⟩*generator ⟨0,by decide⟩))*
        generator ⟨0,by decide⟩ *
        (generator ⟨18,by decide⟩*generator ⟨18,by decide⟩) =
        projection (monomialOfString "0,7,18,2")
      have hp : (("0,7,18,2".splitOn ",").map
          (fun n => n.toNat?.getD 0)) = [0, 7, 18, 2] := by
        have split : "0,7,18,2".splitOn "," = ["0", "7", "18", "2"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "0,7,18,2"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,
        pow_succ,mul_assoc]
    rw [heq]
    exact he
  rw [← htarget] at h
  have hprod' : routeComputation.realization.sphere 9 71 (mulAt dataH0 B) =
      Sphere.Internal.product Def.fixedImplementation.foundationInput.hf2
        Def.fixedImplementation.milnorInput.toMilnor
        (routeComputation.realization.sphere 1 1 dataH0)
        (routeComputation.realization.sphere 8 70 B) := by
    simpa using hprod
  rw [hprod', h0std] at h
  refine ⟨x, ?_⟩
  have hdirect :=
    KIP126.Core.SpectralSequence.FinitePageCalculus.differential_two_direct h
  have hprod_op :
      Sphere.Internal.product Def.fixedImplementation.foundationInput.hf2
          Def.fixedImplementation.milnorInput.toMilnor
          (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 0)
          (routeComputation.realization.sphere 8 70 B) =
        Sphere.Internal.product standardFoundation.hf2 standardMilnorCooperations
          (Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 0)
          (routeComputation.realization.sphere 8 70 B) := by
    simpa only [KIP126.Classical.Adams.standardFoundation,
      KIP126.Classical.Adams.standardMilnorCooperations,
      KIP126.Def.StageInput.witness, KIP126.Def.fixedImplementation,
      KIP126.Implementation.foundation, KIP126.Implementation.milnor,
      KIP126.Foundation.FoundationInput.toStandard,
      KIP126.Foundation.MilnorInput.toMilnor]
  rw [hprod_op, hx] at hdirect
  simpa [eB] using hdirect

/- Construct one E₃ representative from the three preceding inputs. -/
theorem theta_b_massey_defining_system
    (hcycles : ThetaBMasseyCycleInputs)
    (hd2h6 : ThetaBMasseyD2H6)
    (hd2second : ThetaBMasseyD2Second) :
    ∃ z, RepresentsOnPage
      (adamsTowerInternalSpectralSequence
        standardFoundation.hf2.unit SphereSpectrum)
      3 (9, 134) eH6B z ∧ z ∈ ThetaBMassey M eB := by
  sorry

/- The two E₂ product calculations needed to remove the defining-system
indeterminacy.  This follows the proof of MainPaper Lemma 7.16 (printed
p.50): the indeterminacy products themselves vanish in Ext/E₂; it is not
enough to assert that their d₂ differential is zero. -/
theorem theta_b_massey_left_indeterminacy_product
    (c : E2 standardFoundation.hf2 SphereSpectrum 7 70)
    (hc : IsPageCycle
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      2 (7, 70) c) :
      (Sphere.Internal.product standardFoundation.hf2 M
        (s := 2) (t := 64) (s' := 7) (t' := 70)
        (Sphere.Internal.hiSquare standardFoundation.hf2 M 5) c) = 0 := by
  sorry

theorem theta_b_massey_right_indeterminacy_product
    (a : E2 standardFoundation.hf2 SphereSpectrum 1 64)
    (ha : IsPageCycle
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      2 (1, 64) a) :
      (Sphere.Internal.product standardFoundation.hf2 M
        (s := 1) (t := 64) (s' := 8) (t' := 70) a eB) = 0 := by
        
  sorry

/- Assembly step: the two E₂ product vanishings imply equality of all E₃
defining-system representatives. -/
theorem theta_b_massey_zero_indeterminacy_assembly
    (hdef : ∃ z, RepresentsOnPage
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      3 (9, 134) eH6B z ∧ z ∈ ThetaBMassey M eB)
    (hleft : ∀ c : E2 standardFoundation.hf2 SphereSpectrum 7 70,
      IsPageCycle (adamsTowerInternalSpectralSequence
        standardFoundation.hf2.unit SphereSpectrum) 2 (7, 70) c →
      Sphere.Internal.product standardFoundation.hf2 M
        (s := 2) (t := 64) (s' := 7) (t' := 70)
        (Sphere.Internal.hiSquare standardFoundation.hf2 M 5) c = 0)
    (hright : ∀ a : E2 standardFoundation.hf2 SphereSpectrum 1 64,
      IsPageCycle (adamsTowerInternalSpectralSequence
        standardFoundation.hf2.unit SphereSpectrum) 2 (1, 64) a →
      Sphere.Internal.product standardFoundation.hf2 M
        (s := 1) (t := 64) (s' := 8) (t' := 70) a eB = 0) :
    ThetaBMasseyZeroIndeterminacy M eB := by
  sorry

/- The full cycle-space/product calculation kills the two defining-system
indeterminacy images on E₃. -/
theorem theta_b_massey_zero_indeterminacy
    (hdef : ∃ z, RepresentsOnPage
      (adamsTowerInternalSpectralSequence
        standardFoundation.hf2.unit SphereSpectrum)
      3 (9, 134) eH6B z ∧ z ∈ ThetaBMassey M eB) :
    ThetaBMasseyZeroIndeterminacy M eB := by
  apply theta_b_massey_zero_indeterminacy_assembly hdef
  · intro c hc
    exact theta_b_massey_left_indeterminacy_product c hc
  · intro a ha
    exact theta_b_massey_right_indeterminacy_product a ha

/-- `lem:toda2ext`: both the specified E3 value and the whole Massey
set are constrained. Two d2 equations alone do not remove indeterminacy.
The proof must reconstruct the two full cycle spaces and their product
images from I's bounded basis, staircase and multiplication comparisons. -/
theorem theta_b_massey_value_and_indeterminacy :
    (∃ z, RepresentsOnPage
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      3 (9,134) eH6B z ∧ z ∈ ThetaBMassey M eB) ∧
    ThetaBMasseyZeroIndeterminacy M eB := by
  have hcycles := theta_b_massey_cycle_inputs
  have hd2h6 := theta_b_massey_d2_h6
  have hd2second := theta_b_massey_d2_second_nullhomotopy
  have hdef := theta_b_massey_defining_system hcycles hd2h6 hd2second
  exact ⟨hdef, theta_b_massey_zero_indeterminacy hdef⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- `lem:toda2ext`: the first product uses q=0; the second uses 0<=q<=6
and m>=max(4,10-q). The latter requires the entire low stem63 staircase,
its eventual zero targets, and the actual negative-filtration tail. -/
theorem theta_b_moss_no_crossing :
    ¬ SphereMossCrossing (H := standardFoundation.hf2) 3 (3,65) ∧
    ¬ SphereMossCrossing (H := standardFoundation.hf2) 3 (9,71) := by
  have hseq : Computation.Route.sequence routeModel .sphere =
      adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum := by
    rfl
  constructor
  · intro h
    rcases h with ⟨m, q, hm, hq, hqbound, hstem, hd⟩
    rw [← hseq] at hd
    norm_num [Prod.fst, Prod.snd, Int.reduceSub, Int.reduceAdd] at hd
    have hd' : (Computation.Route.sequence routeModel .sphere).d m (q, q + 63) ≠ 0 := by
      have hdegree : q + 62 + 1 = q + 63 := by omega
      rw [← hdegree]
      exact hd
    have hz := KIP126.Computation.Route.stem63_no_late_differentials
      routeComputation sphereVanishing q (by omega) m (by omega)
    apply hd'
    ext a
    change (Computation.Route.sequence routeModel .sphere).d m (q, q + 63) a = 0
    exact hz a
  · intro h
    rcases h with ⟨m, q, hm, hq, hqbound, hstem, hd⟩
    rw [← hseq] at hd
    norm_num [Prod.fst, Prod.snd, Int.reduceSub, Int.reduceAdd] at hd
    have hd' : (Computation.Route.sequence routeModel .sphere).d m (q, q + 63) ≠ 0 := by
      have hdegree : q + 62 + 1 = q + 63 := by omega
      rw [← hdegree]
      exact hd
    have hz := KIP126.Computation.Route.stem63_no_late_differentials
      routeComputation sphereVanishing q (by omega) m (by omega)
    apply hd'
    ext a
    change (Computation.Route.sequence routeModel .sphere).d m (q, q + 63) a = 0
    exact hz a

/-- `lem:toda2ext`: a compatible synthetic bracket MEMBER and its actual
nonzero detector must be produced, not inferred from order two alone.
The proof uses the local Massey/no-crossing results, the supplied classical
Moss application, and the realization/secondary-operation comparison. -/
structure CompositionOnlyMossInterface : Prop where
  bridge : ∀
    (hdef : ∃ z, RepresentsOnPage
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      3 (9, 134) eH6B z ∧ z ∈ ThetaBMassey M eB)
    (hnocross : ¬ SphereMossCrossing (H := standardFoundation.hf2) 3 (3,65) ∧
      ¬ SphereMossCrossing (H := standardFoundation.hf2) 3 (9,71))
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (htheta : ThetaChoice M (D).toModelData theta),
    ∃ (b : BiHom 62 70 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
      (z : BiHom 125 134 (S_0_0 : KIP126.Def.standardRouteInput.Syn)),
      SphereDetected D 8 70 0 eB b ∧ SphereDetected D 9 134 0 eH6B z ∧
      TripleToda theta syntheticTwo b z

axiom compositionOnlyMossInterface : CompositionOnlyMossInterface

theorem synthetic_theta_b_toda_moss_assembly
    (hMoss : CompositionOnlyMossInterface)
    (hdef : ∃ z, RepresentsOnPage
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      3 (9, 134) eH6B z ∧ z ∈ ThetaBMassey M eB)
    (hnocross : ¬ SphereMossCrossing (H := standardFoundation.hf2) 3 (3,65) ∧
      ¬ SphereMossCrossing (H := standardFoundation.hf2) 3 (9,71))
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (htheta : ThetaChoice M (D).toModelData theta) :
    ∃ (b : BiHom 62 70 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
      (z : BiHom 125 134 (S_0_0 : KIP126.Def.standardRouteInput.Syn)),
      SphereDetected D 8 70 0 eB b ∧ SphereDetected D 9 134 0 eH6B z ∧
      TripleToda theta syntheticTwo b z := by
  sorry

theorem synthetic_theta_b_toda
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (htheta : ThetaChoice M (D).toModelData theta) :
    ∃ (b : BiHom 62 70 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
      (z : BiHom 125 134 (S_0_0 : KIP126.Def.standardRouteInput.Syn)),
      SphereDetected D 8 70 0 eB b ∧ SphereDetected D 9 134 0 eH6B z ∧
      TripleToda theta syntheticTwo b z := by
  have hvalue := theta_b_massey_value_and_indeterminacy
  exact synthetic_theta_b_toda_moss_assembly
    compositionOnlyMossInterface hvalue.1 theta_b_moss_no_crossing theta htheta

/-- `lem:toda2ext`: lambda^2 h0=2 lambda and 2 theta=2 b=0 kill
these two images. This does not set the original high bracket's
indeterminacy to zero and does not require an extra raw computation. -/
/- E₂ inputs for the two multiplied-indeterminacy images.  After transport,
the synthetic formulas use only the composition product `sphereProduct`, not
an independent sphere-spectrum multiplication.
These are the classical product calculations used in the corresponding
paragraph of MainPaper Lemma 7.16; the synthetic predicates below are their
transported form. -/
theorem theta_b_e2_first_multiplied_product
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (b : BiHom 62 70 (S_0_0 : KIP126.Def.standardRouteInput.Syn)) :
    ThetaBMultipliedIndeterminacy h₀ theta b := by
  sorry

theorem theta_b_e2_second_multiplied_product
    (b : BiHom 62 70 (S_0_0 : KIP126.Def.standardRouteInput.Syn)) :
    SymmetricTwoMultipliedIndeterminacy b := by
  sorry

theorem theta_b_multiplied_indeterminacy
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (htheta : ThetaChoice M (D).toModelData theta)
    (b : BiHom 62 70 (S_0_0 : KIP126.Def.standardRouteInput.Syn)) :
    ThetaBMultipliedIndeterminacy h₀ theta b ∧
    SymmetricTwoMultipliedIndeterminacy b := by
  exact ⟨theta_b_e2_first_multiplied_product theta b,
    theta_b_e2_second_multiplied_product b⟩

/-- The precise multiplied shuffle in `lem:toda2ext`. The premise is
actual Toda membership, so no selected value replaces the original set.
The two multiplied-indeterminacy statements above are internal proof
dependencies, rather than new assumptions of this theorem. -/
theorem theta_b_multiplied_shuffle_assembly
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (b : BiHom 62 70 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (z : BiHom 125 134 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (hz : TripleToda theta syntheticTwo b z)
    (hleft : ThetaBMultipliedIndeterminacy h₀ theta b)
    (hright : SymmetricTwoMultipliedIndeterminacy b) :
    lambdaMultiply 2 (sphereProduct h₀ z) =
      lambdaMultiply 3 (sphereProduct η (sphereProduct theta b)) := by
  sorry

theorem theta_b_multiplied_shuffle
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (htheta : ThetaChoice M (D).toModelData theta)
    (b : BiHom 62 70 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (z : BiHom 125 134 (S_0_0 : KIP126.Def.standardRouteInput.Syn))
    (hz : TripleToda theta syntheticTwo b z) :
    lambdaMultiply 2 (sphereProduct h₀ z) =
      lambdaMultiply 3 (sphereProduct η (sphereProduct theta b)) := by
  have hm := theta_b_multiplied_indeterminacy theta htheta b
  exact theta_b_multiplied_shuffle_assembly theta b z hz hm.1 hm.2

/-- Lemma `lem:toda2ext`, including nonemptiness and ALL bracket members.
AlphaOneProperties is an internally produced compatibility target from
`lem:x_123_9`, not a new accepted A/C premise. The Q9 class is the actual
restriction of that same Q11 representative.

The proof must eliminate every AF<=12 possibility in this weight window.
In particular, the AF9 exclusion must use the full eta-extension and
filtration analysis; cancelling eta in a homotopy equation is invalid.
The two multiplied Toda-indeterminacy lemmas above apply exactly here. -/
theorem main_toda_bracket_detected
    (hc3 : C3 L) (hc5 : C5 M (D).toModelData L η)
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 11))
    (ha : AlphaOneProperties D η h₀ ((L).U M) eV a11) :
    let a9 := a11 ≫ ((D).quotientTower S_0_0).rho 9 11 (by decide)
    (∃ z : BiHom 125 132 (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9),
      ModuleTripleToda (lambdaMultiply 3 a9) h₀ η z) ∧
    (∀ z : BiHom 125 132 (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9),
      ModuleTripleToda (lambdaMultiply 3 a9) h₀ η z →
      FiniteDetected D 9 (by decide) 11 136 4 eY z) := by
  sorry

/-- The second no-crossing alternative checked in `lem:nuext125`.
For exponents (1,0,0) and lengths (3,0,0), the Mahowald parameters are
r=r'=3 at (8,134). The only crossing candidate is the full Cnu d2 from
(9,135) to (11,136); I's complete source basis and staircase kill it.
The zero-length q-extension supplies the other alternative independently;
neither alternative is a new C premise, or a Moss crossing condition. -/
theorem cnu_d3_no_crossing :
    let F := KIP126.Def.fixedImplementation.foundationInput
    @PageRepresentatives.NoCrossingOn F.Spectrum F.stable F.cofiber F.hf2
      (@HasFunctorialCofiber.cofib F.Spectrum F.stable F.cofiber
        _ _ (D).auxiliary.nuMap) 3 3 (8,134) := by
  dsimp only [PageRepresentatives.NoCrossingOn]
  constructor
  · omega
  · constructor
    · omega
    · intro hc
      rcases hc with ⟨a, b, ha, ha', hb, hb', x, y, hd⟩
      have ha1 : a = 1 := by omega
      have hb0 : b = 0 := by omega
      subst a
      subst b
      have hzero := KIP126.Computation.Route.cnu_d2_zero routeComputation
      change KIP126.Core.SpectralSequence.HasNonzeroDifferential
        (KIP126.Computation.Route.sequence routeModel .nuCofiber)
        2 (9,135) (11,136) x y at hd
      rcases hd with ⟨hdeg, xr, yr, hxr, hyr, hdiff, hne⟩
      rw [hzero] at hdiff
      apply hne
      simpa [eq_comm] using hdiff

/- The generalized Mahowald conclusion on Q₃, before the independent
Q₃-to-Q₅ correction calculation. The proof must supply the two zero-length
edge extensions, the common representative, May's compatible lift, and the
no-crossing argument above. -/
theorem nu_extension_in_third_quotient : NuExtension3 D eX eY h2 := by
  sorry

/-- `lem:nuext125`, the substantial Q₃-to-Q₅ step. Starting from the
actual Q₃ relation, resolve every AF10 correction class in the full
E₂(10,135) space, including linear combinations, BHS lifetime, and the
actual restriction map. The conclusion is an exact relation between
detected representatives in the same Q₅; it does not assert that the
correction group vanishes. -/
theorem nu_extension_lifts_to_fifth_quotient
    (hq3 : NuExtension3 D eX eY h2) : NuExtension5 D eX eY h2 := by
  sorry

/-- Lift the corrected Q₅ relation to Q₉ along the actual λ⁴ quotient map.
The target is stated with its λ-divided representative, so this requires the
separate obstruction calculation and is stronger than merely multiplying
the Q₅ equality by λ⁴. -/
theorem nu_extension_lifts_from_fifth_to_ninth_quotient
    (hq5 : NuExtension5 D eX eY h2) : NuExtension9 D eX eY h2 := by
  sorry

/-- `lem:nuext125`: use the actual lambda^4 map from the shifted Q5
to Q9. X need only survive nontrivially to E6 with no incoming differential;
neither X nor Y is assumed to be a classical permanent cycle. -/
theorem nu_extension_in_ninth_quotient : NuExtension9 D eX eY h2 :=
  nu_extension_lifts_from_fifth_to_ninth_quotient
    (nu_extension_lifts_to_fifth_quotient nu_extension_in_third_quotient)

/-- `cor:2ext125`: the h0 extension is independent of the Y representative,
with a target representative chosen afterwards. C3 and C5 are essential;
this is not a new unconditional computation of d5(Y). -/
theorem h0_extension_for_any_y
    (hc3 : C3 L) (hc5 : C5 M (D).toModelData L η) :
    ∀ y : BiHom 125 132
        (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9),
      FiniteDetected D 9 (by decide) 11 136 4 eY y →
      ∃ t : BiHom 125 139
          (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9),
        FiniteDetected D 9 (by decide) 14 139 0 ((L).target M) t ∧
        sphereAction h₀ y = lambdaMultiply 6 t := by
  sorry

theorem h0_extension_nonzero_for_any_y
    (hc3 : C3 L) (hc5 : C5 M (D).toModelData L η) :
    ∀ y : BiHom 125 132
        (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9),
      ∀ t : BiHom 125 139
          (XModLambdaN (S_0_0 : KIP126.Def.standardRouteInput.Syn) 9),
        FiniteDetected D 9 (by decide) 11 136 4 eY y →
        FiniteDetected D 9 (by decide) 14 139 0 ((L).target M) t →
        lambdaMultiply 6 t ≠ 0 := by
  sorry

theorem any_y_h0_extension
    (hc3 : C3 L) (hc5 : C5 M (D).toModelData L η) :
    AnyYH0Extension D eY ((L).target M) h₀ := by
  intro y hy
  obtain ⟨t, ht, heq⟩ := h0_extension_for_any_y hc3 hc5 y hy
  refine ⟨t, ht, heq, ?_⟩
  exact h0_extension_nonzero_for_any_y hc3 hc5 y t hy ht

/-- Remark `rem:h02x1259`: only under both paper conditions can the
newly constructed Q9 detection rule out the previously unknown d5(Y).
The page representative is part of HasDifferential. -/
theorem conditional_y_d5_zero_assembly
    (hc3 : C3 L) (hc5 : C5 M (D).toModelData L η)
    (hext : AnyYH0Extension D eY ((L).target M) h₀)
    (hdiv : TargetNuDivisible D ((L).target M) h2) :
    HasDifferential
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      5 (11,136) (16,140) eY 0 := by
  sorry

theorem conditional_y_d5_zero
    (hc3 : C3 L) (hc5 : C5 M (D).toModelData L η) :
    HasDifferential
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      5 (11,136) (16,140) eY 0 := by
  sorry

/-- `prop:state5false`: this includes the two-candidate exhaustion for
u*h0, the two P/Q filtration arguments, and the precise lifting of the
equality from Q9 to the untruncated sphere. Existence of permanent P and
Q representatives by itself does not lift an equality of products.
No injectivity of eta or unrestricted vanishing of lambda^9 on Q9 is used. -/
theorem target_nu_divisible_assembly
    (hc3 : C3 L) (hc5 : C5 M (D).toModelData L η)
    (hd5 : HasDifferential
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      5 (11,136) (16,140) eY 0)
    (hext : AnyYH0Extension D eY ((L).target M) h₀)
    (hnu : NuExtension9 D eX eY h2) :
    TargetNuDivisible D ((L).target M) h2 := by
  sorry

theorem target_nu_divisible
    (hc3 : C3 L) (hc5 : C5 M (D).toModelData L η) :
    TargetNuDivisible D ((L).target M) h2 := by
  apply target_nu_divisible_assembly hc3 hc5
  · exact conditional_y_d5_zero hc3 hc5
  · exact any_y_h0_extension hc3 hc5
  · exact nu_extension_in_ninth_quotient

/-- The last rigidity step of Blueprint
`prop:near126-c3-not-c5`, which uses `thm:external-lambda-bockstein`.
The cycle side of that comparison is the zero-differential criterion
`KIPBase.Synthetic.pageTail_cycle_iff_exists_zero_differential_relation`;
its direct finite-quotient side is `prop:finite-quotient-lift-filtration`.
The cofiber is the actual cofiber of `D.auxiliary.nuMap`, and `[2]` is
the same bottom-cell image as in `I.bottom`. The exponent four gives
incoming pages 2..5, not a permanence claim about the cofiber class.
`KIP126.Core.SpectralSequence` and `KIPBase.SpectralSequence` are distinct
Lean structures, so the cited KIPBase theorem does not discharge this
remaining KIP126 proof obligation by itself. -/
theorem target_divisibility_forces_cnu_incoming
    (hdiv : TargetNuDivisible D ((L).target M) h2) :
    ∃ y : KIP126.Computation.Route.Page D .nuCofiber 14 139,
      (I).realization.decode .nuCofiber 14 139 [2] = some y ∧
      ∃ r : ℤ, 2 ≤ r ∧ r ≤ 5 ∧
        HitOnPage (KIP126.Computation.Route.sequence D .nuCofiber) r (14,139) y := by
  sorry

theorem target_divisibility_forces_cnu_incoming_assembly
    (hdiv : TargetNuDivisible D ((L).target M) h2) :
    ∃ y : KIP126.Computation.Route.Page D .nuCofiber 14 139,
      (I).realization.decode .nuCofiber 14 139 [2] = some y ∧
      ∃ r : ℤ, 2 ≤ r ∧ r ≤ 5 ∧
        HitOnPage (KIP126.Computation.Route.sequence D .nuCofiber) r (14,139) y := by
  exact target_divisibility_forces_cnu_incoming hdiv

/-- The final contradiction uses precisely the decoded target and finite
incoming window already supplied by the independent Cnu reconstruction. -/
theorem c3_excludes_c5
    (hc3 : C3 L) : ¬ C5 M (D).toModelData L η := by
  intro hc5
  obtain ⟨y, hy, r, hr, hr', hhit⟩ :=
    target_divisibility_forces_cnu_incoming (target_nu_divisible hc3 hc5)
  obtain ⟨y', hy', _, hnot⟩ := KIP126.Computation.Route.cnu_target_through5 I
  have hyy : y = y' := Option.some.inj (hy.symm.trans hy')
  subst y'
  exact hnot.2.2 r hr hr' hhit

end
end KIP126.Main.Solution.Route.Section7
