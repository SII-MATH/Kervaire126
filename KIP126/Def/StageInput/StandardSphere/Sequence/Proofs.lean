import KIP126.Def.StableHomotopy.Implementation.Fixed
import KIP126.Def.StageInput.Foundation
import KIP126.Def.ClassicalAdams.Convergence.BHS.Predicates
import KIP126.Def.ClassicalAdams.SphereVanishing.Predicates

/-! Applicability of BHS to the standard sphere in Def's fixed implementation.
The statement is independent of the selected route, literature package, and
program data. Its construction proof remains an explicit obligation. -/
namespace KIP126.Def

theorem standardSphereApplicability : Classical.Adams.BHSObjectApplicability
    fixedImplementation.foundationInput.countableProducts
    fixedImplementation.foundationInput.hf2.unit
    (StableHomotopy.SphereSpectrum
      (C := fixedImplementation.foundationInput.Spectrum)) := by
  sorry

/-- Separation of the Adams filtration on the fixed 2-completed sphere.
The applicability theorem above identifies the fixed object, while the
convergence-to-separation argument remains a visible proof obligation. -/
theorem standardSphereSeparated : Classical.Adams.ClassicalSphereSeparated
    Classical.Adams.standardFoundation.hf2 := by
  have h := standardSphereApplicability
  exact (open CategoryTheory KIP126.StableHomotopy KIP126.Classical.Adams in by
    set_option backward.isDefEq.respectTransparency false in
      intro n a ha
      let V := towerAbutment (SphereSpectrum (C := fixedImplementation.foundationInput.Spectrum)) n
      let S : Submodule ℤ V := Submodule.span ℤ {a}
      have hs : (ModuleCat.subobjectModule V).symm S = ⊥ := by
        apply h.strongly_convergent.separated n
        intro s
        apply (ModuleCat.subobjectModule V).symm.monotone
        apply Submodule.span_le.mpr
        intro x hx
        have hxa := Set.mem_singleton_iff.mp hx
        rw [hxa]
        change a ∈ TowerDetection.filtrationSubmodule standardFoundation.hf2.unit SphereSpectrum s n
        have hh := ha s.toNat
        simpa only [TowerDetection.filtrationSubmodule, Int.toNat_natCast] using hh
      have hz : S = ⊥ := by
        have hh := congrArg (ModuleCat.subobjectModule V) hs
        simpa using hh
      have ham : a ∈ S := Submodule.subset_span (Set.mem_singleton a)
      rw [hz] at ham
      exact (Submodule.mem_bot ℤ).mp ham)

end KIP126.Def
