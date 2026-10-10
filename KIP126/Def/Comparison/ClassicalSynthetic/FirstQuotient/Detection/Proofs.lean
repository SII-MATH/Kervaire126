import KIP126.Def.Comparison.ClassicalSynthetic.FirstQuotient.Detection.Predicates
import KIP126.Def.Synthetic.Detection.Proofs
import KIP126.Def.Synthetic.Detection.Vanishing.Proofs

/-! Detection determines a homotopy representative only when the next
actual Adams filtration vanishes. For the first lambda quotient, BHS
`cor:synth-ctau-ASS` at p=1 supplies the single-filtration range; applying
that range and separated convergence is a separate internal obligation.
Neither the range nor BHS's theorem is silently added to Model.
-/
namespace KIP126.Comparison.ClassicalSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {HS : Syn} {unit : S_0_0 ⟶ HS} {family : SyntheticAdamsFamily Syn} {Y : Syn}

/-- Associated-graded detection gives equality only after its possible
higher-filtration error is eliminated. Zero labels are allowed. -/
theorem detects_unique_of_next_filtration_zero
    (c : TowerConvergence unit family Y) (i : Tridegree)
    (hzero : towerFiltrationSubmodule unit Y (i.1+1) (i.2.1-i.1,i.2.2) = ⊥)
    (x : (family.obj Y).E₂ i)
    (α β : BiHom (i.2.1-i.1) i.2.2 Y)
    (hα : Detects c i x α) (hβ : Detects c i x β) : α = β := by
  have h := detects_sub_filtration c i hα hβ
  change α - β ∈ towerFiltrationSubmodule unit Y (i.1+1) (i.2.1-i.1,i.2.2) at h
  rw [hzero, Submodule.mem_bot] at h
  exact sub_eq_zero.mp h

variable {C : Type w} [StableHomotopyCategory.{w, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

/-- Vanishing of all higher associated grades plus D's separated ACTUAL
tower filtration eliminates the entire tail. No finite snapshot is used. -/
theorem firstQuotient_next_filtration_zero_of_range
    (X : ClassicalObject) (a s t : ℤ)
    (h : FirstQuotientSingleFiltration D X a) :
    FirstQuotientNextFiltrationZero D X a s t := by
  apply eq_bot_iff.mpr
  intro α hα
  apply D.homotopySeparated (.quotient 1 (.shift (0,a) (.nu X))) (t-s) (t+a) α
  intro j
  by_cases hj : s+1 ≤ (j : ℤ)
  · apply ((D.convergence (.quotient 1 (.shift (0,a) (.nu X)))).filtrationAtLeast_iff_of_eInfty_isZero
      (s+1) j (t-s) (t+a) hj (fun q hq _ => ?_) α).mp hα
    letI := h (t-s) (t+a) q (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  · exact towerFiltrationSubmodule_antitone _ _ _ (by omega) hα

/-- Once the BHS single-filtration range is transported to this same
quotient/tower, the already fixed comparisonCompatible detection condition
uniquely determines the first-quotient label. This is the required internal
uniqueness lemma, not an extra external theorem for arbitrary choices. -/
theorem firstQuotient_inverse_eq_of_detection
    (X : ClassicalObject) (a s t : ℤ)
    (hzero : FirstQuotientNextFiltrationZero D X a s t)
    (x : E2 H (X.obj D.auxiliary) s t)
    (α : BiHom (t-s) (t+a)
      ((SyntheticObject.quotient 1 (.shift (0,a) (.nu X))).obj D.nu D.auxiliary))
    (hα : Detects (D.convergence (.quotient 1 (.shift (0,a) (.nu X)))) (s,t,t+a)
      (familyPageMap D.family (XModLambdaN.incl _ 1) 2 (s,t,t+a)
        (by simpa [SyntheticObject.obj, SyntheticAdamsSS.E₂] using D.nuE2 X a s t 0 x)) α) :
    α = (D.firstQuotient (X.obj D.auxiliary) a s t).symm x := by
  exact detects_unique_of_next_filtration_zero
    (D.convergence (.quotient 1 (.shift (0,a) (.nu X)))) (s,t,t+a)
    hzero _ _ _ hα (D.comparisonCompatible.nu_first_quotient X a s t x)

end
end KIP126.Comparison.ClassicalSynthetic
