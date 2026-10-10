import KIP126.Main.Solution.Computation.Route
import KIP126.Def.Kervaire.Route.Tmf.Predicates
import KIP126.Def.ClassicalAdams.TowerNaturality.Isomorphism.Proofs

/-! The high125 tmf consequences are Main deductions. The source supplies
one actual product with nonzero tmf image. Its nonzero associated grade at
filtration 25 additionally uses C(M), the vanishing line, and separation.
No theorem here consumes the assembled route literature or a stage axiom. -/
namespace KIP126.Main.Solution.Computation
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Core.SpectralSequence KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.Kervaire.Route KIP126.Literature.Route

universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn) {L : Labels H} {G : TmfLabels H}

set_option backward.isDefEq.respectTransparency false in
private theorem source_high125_detected (source : TmfSourceData H) (hsource : TmfSourceResults source)
    (binding : TmfBinding D G source)
    (multiplicative : ClassicalProductDetection D) :
    TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (G.high125 M) source.high125 := by
  have hg : G.g = source.labels.g := binding.g
  have hw : G.delta_h_1_mul_g = source.labels.delta_h_1_mul_g := binding.delta_h_1_mul_g
  have hk : TowerDetection.Detects (D.classicalConvergence .sphere) (4,24)
      G.g source.kappaBar := by
    rw [binding.sphereConvergence, hg]
    exact hsource.kappaBar_detection
  have hw' : TowerDetection.Detects (D.classicalConvergence .sphere) (9,54)
      G.delta_h_1_mul_g source.wClass := by
    rw [binding.sphereConvergence, hw]
    exact hsource.w_detection
  have hk2 := multiplicative 4 24 4 24 G.g G.g source.kappaBar source.kappaBar hk hk
  norm_num [ClassicalProductDetection] at hk2
  have hk4 := multiplicative 8 48 8 48 _ _ _ _ hk2 hk2
  norm_num [ClassicalProductDetection] at hk4
  have hprod := multiplicative 16 96 9 54 _ _ _ _ hk4 hw'
  norm_num [ClassicalProductDetection] at hprod
  exact hprod

/-- Multiplicative detection puts the source product kappaBar^4*w in F25
with leading label G.high125. Its tmf image is nonzero by the source result.
The finite E5 exhaustion, vanishing line and separated filtration give F26=0
via `classical_stem125_filtration26_zero`; hence that leading grade is nonzero.
This argument does not assume the already assembled `TmfInputs` conclusion. -/
theorem high125_nonzero_survival_of_computation
    (I : KIP126.Computation.Route.Inputs D L G)
    (V : SphereVanishingLine H) (separated : ClassicalSphereSeparated H)
    (source : TmfSourceData H) (hsource : TmfSourceResults source)
    (binding : TmfBinding D G source)
    (multiplicative : ClassicalProductDetection D) :
    NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      (25,150) (G.high125 M) := by
  set_option backward.isDefEq.respectTransparency false in
    have hdet := source_high125_detected D source hsource binding multiplicative
    dsimp only [TowerDetection.Detects, ClassicalObject.obj] at hdet
    obtain ⟨z, hz, a, ha, hgrade⟩ := hdet
    refine ⟨z, hz, ?_⟩
    intro hzero
    have hg : (TowerDetection.filtration H.unit SphereSpectrum).toAssociatedGraded 25 (150 - 25) a = 0 := by
      rw [← hgrade, hzero, map_zero]
    have hmem := (subobject_cokernel_π_eq_zero_iff
      ((TowerDetection.filtration H.unit SphereSpectrum).F 26 (150 - 25))
      ((TowerDetection.filtration H.unit SphereSpectrum).F 25 (150 - 25))
      ((TowerDetection.filtration H.unit SphereSpectrum).mono 25 (150 - 25)) a).mp hg
    rw [ha] at hmem
    have htail : source.high125 ∈
        TowerDetection.filtrationSubmodule H.unit SphereSpectrum 26 125 := by
      simpa only [TowerDetection.filtration, TowerDetection.homotopy,
        Int.reduceSub, OrderIso.apply_symm_apply] using hmem
    have hvan := KIP126.Computation.Route.classical_stem125_filtration26_zero
      I V separated source.high125 htail
    exact hsource.high125_nonzero (by rw [hvan, CategoryTheory.Limits.zero_comp])

/-- Exact source-to-model tmf comparison using the actual product and canonical
detection. It supplies one detected high class, and retains its leading-term
survival as an explicit premise. Representative independence is a further
Main deduction using the higher-filtration tail. -/
theorem tmf_of_source (G : TmfLabels H) (source : TmfSourceData H)
    (hsource : TmfSourceResults source) (binding : TmfBinding D G source)
    (multiplicative : ClassicalProductDetection D)
    (hhigh : NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      (25,150) (G.high125 M)) : TmfInputs D G := by
  set_option backward.isDefEq.respectTransparency false in
    refine ⟨?_, ?_, ?_⟩
    · intro theta _
      apply (cancel_mono binding.detectorIso.hom).1
      rw [Category.assoc, binding.unit, CategoryTheory.Limits.zero_comp]
      exact hsource.vanishing62 (theta ≫ source.unit)
    · refine ⟨hhigh, source.high125,
        source_high125_detected D source hsource binding multiplicative, ?_⟩
      intro hz
      apply hsource.high125_nonzero
      rw [← binding.unit, ← Category.assoc, hz, CategoryTheory.Limits.zero_comp]
    · intro s hs
      let f := binding.detectorIso.hom
      let e := LinearEquiv.ofBijective (adamsCycleInduced H.unit f 2 (by decide) s (63+s))
        (adamsCycleInduced_bijective H.unit f 2 (by decide) s (63+s))
      have hb : (adamsCycleBoundaries H.unit D.auxiliary.detector 2 (by decide) s (63+s)).map
          e.toLinearMap = adamsCycleBoundaries H.unit source.spectrum 2 (by decide) s (63+s) := by
        ext b
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact (adamsE1Induced_mem_boundaries_iff H.unit f 2 (by decide) s (63+s) a.val).2 ha
        · intro hb
          refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
          apply (adamsE1Induced_mem_boundaries_iff H.unit f 2 (by decide) s (63+s) (e.symm b).val).1
          change e (e.symm b) ∈ adamsCycleBoundaries H.unit source.spectrum 2 (Nat.le_succ 1) s (63+s)
          simpa only [e.apply_symm_apply] using hb
      let eqv := (adamsTowerSSDataPageIso H.unit D.auxiliary.detector s (63+s) 0).toLinearEquiv.trans
        ((Submodule.Quotient.equiv _ _ e hb).trans
          (adamsTowerSSDataPageIso H.unit source.spectrum s (63+s) 0).toLinearEquiv.symm)
      letI : Subsingleton ((adamsTowerSSData H.unit source.spectrum s (63+s)).page 0) :=
        hsource.low_filtration63 s hs
      exact ⟨fun a b => eqv.injective (Subsingleton.elim (eqv a) (eqv b))⟩

/-- Produce the tmf consumer package after the finite computation and the
independent infinite-range premises have been supplied on the same model. -/
theorem tmf_inputs_of_computation
    (I : KIP126.Computation.Route.Inputs D L G)
    (V : SphereVanishingLine H) (separated : ClassicalSphereSeparated H)
    (source : TmfSourceData H) (hsource : TmfSourceResults source)
    (binding : TmfBinding D G source)
    (multiplicative : ClassicalProductDetection D) : TmfInputs D G :=
  tmf_of_source D G source hsource binding multiplicative
    (high125_nonzero_survival_of_computation D I V separated source hsource
      binding multiplicative)

end
end KIP126.Main.Solution.Computation
