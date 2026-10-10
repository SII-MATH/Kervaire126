import KIP126.Interface.Challenge.Challenge2
import KIP126.LinProgram.Certificates.BasisTable.LowDegrees

/-! Low-degree mathematical consequences of one Challenge2 computation delivery.
The selected basis already supplies the eta degree. The remaining degrees use
the same delivered sphere coordinates and reusable fixed-table certificates. -/

namespace KIP126.Main.Solution.Computation

open KIP126.Core.Algebra KIP126.LinE2
open KIP126.StableHomotopy KIP126.Classical.Adams
open KIP126.Kervaire.Route

noncomputable section

/-- The delivered selected basis in bidegree `(1, 2)` has one vector over F₂.
No full-table query or second interpretation is needed. -/
theorem sphere_eta_nonzero_unique (input : KIP126.Challenge2) :
    ∀ x y : E2 standardFoundation.hf2 SphereSpectrum 1 2,
      x ≠ 0 → y ≠ 0 → x = y := by
  classical
  obtain ⟨e, _⟩ := input.computation.results.route.basis
    ⟨.sphere, 1, 2, ["1,1"]⟩ (by
      unfold KIP126.Computation.Route.Raw.degrees
      iterate 80 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
  change E2 standardFoundation.hf2 SphereSpectrum 1 2 ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  have hc (x : E2 standardFoundation.hf2 SphereSpectrum 1 2) (hx : x ≠ 0) :
      e x 0 = 1 := by
    generalize h : e x 0 = c
    fin_cases c
    · exfalso
      apply hx
      apply e.injective
      rw [map_zero]
      apply Finsupp.ext
      intro i
      fin_cases i
      exact h
    · rfl
  intro x y hx hy
  apply e.injective
  apply Finsupp.ext
  intro i
  fin_cases i
  exact (hc x hx).trans (hc y hy).symm

/-- The existing empty-table certificate and the delivered coordinates force
the actual sphere Adams component in bidegree `(2, 3)` to vanish. -/
theorem sphere_e2_two_three_subsingleton (input : KIP126.Challenge2) :
    Subsingleton (E2 standardFoundation.hf2 SphereSpectrum 2 3) := by
  let coord : E2 standardFoundation.hf2 SphereSpectrum 2 3 ≃ₗ[ℤ]
      (BasisIndex 2 3 →₀ F2) :=
    input.computation.results.sphereBasis.coordinates 2 3 (by decide)
  haveI : IsEmpty (BasisIndex 2 3) := ⟨by
    intro i
    have hm : basisRowAt 2 3 i ∈ basisRows.filter (fun r => r.s == 2 && r.t == 3) := by
      exact List.getElem_mem i.isLt
    obtain ⟨hm, hd⟩ := List.mem_filter.mp hm
    have hd' : (basisRowAt 2 3 i).s = 2 ∧ (basisRowAt 2 3 i).t = 3 := by
      simpa using hd
    exact BasisCertificates.NuLow.nu_low.2 _ hm hd'.1 hd'.2⟩
  exact Function.Injective.subsingleton coord.injective

/-- The delivered coordinates and their values in the same presentation make
all nonzero classes of the sphere Adams component `(0, 0)` equal. -/
theorem sphere_zero_nonzero_unique (input : KIP126.Challenge2) :
    ∀ x y : E2 standardFoundation.hf2 SphereSpectrum 0 0,
      x ≠ 0 → y ≠ 0 → x = y := by
  classical
  let e : E2 standardFoundation.hf2 SphereSpectrum 0 0 ≃ₗ[ℤ] E2At 0 0 :=
    (input.computation.bindings.presentation.comparison 0 0 (by decide)).symm
  let coord : E2 standardFoundation.hf2 SphereSpectrum 0 0 ≃ₗ[ℤ]
      (BasisIndex 0 0 →₀ F2) :=
    input.computation.results.sphereBasis.coordinates 0 0 (by decide)
  have values : ∀ i : BasisIndex 0 0,
      (e (coord.symm (Finsupp.single i 1))).val = basisValue (basisRowAt 0 0 i) :=
    input.computation.results.sphereBasis.csv_values 0 0 (by decide)
  have hi (i : BasisIndex 0 0) : (basisRowAt 0 0 i).monomial = "" := by
    have hm : basisRowAt 0 0 i ∈ basisRows.filter (fun r => r.s == 0 && r.t == 0) := by
      exact List.getElem_mem i.isLt
    obtain ⟨hm, hd⟩ := List.mem_filter.mp hm
    have hd' : (basisRowAt 0 0 i).s = 0 ∧ (basisRowAt 0 0 i).t = 0 := by
      simpa using hd
    exact BasisCertificates.zero_unique _ hm hd'.1 hd'.2
  haveI : Subsingleton (BasisIndex 0 0) := ⟨by
    intro i j
    have hv : e (coord.symm (Finsupp.single i 1)) =
        e (coord.symm (Finsupp.single j 1)) := by
      apply Subtype.ext
      rw [values, values]
      simp only [basisValue, hi i, hi j]
    have hs : Finsupp.single i (1 : F2) = Finsupp.single j 1 :=
      coord.symm.injective (e.injective hv)
    by_contra hij
    have hh := congrArg (fun f : BasisIndex 0 0 →₀ F2 => f i) hs
    simp [hij] at hh⟩
  intro x y hx hy
  have hxn : coord x ≠ 0 := by
    intro h
    exact hx (coord.injective (h.trans (map_zero coord).symm))
  obtain ⟨i, hi⟩ : ∃ i, coord x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hxn (Finsupp.ext h)
  have hc (a : E2 standardFoundation.hf2 SphereSpectrum 0 0) (ha : a ≠ 0) :
      coord a i = 1 := by
    generalize h : coord a i = c
    fin_cases c
    · exfalso
      apply ha
      apply coord.injective
      rw [map_zero]
      apply Finsupp.ext
      intro j
      have hj : j = i := Subsingleton.elim _ _
      subst j
      exact h
    · rfl
  apply coord.injective
  apply Finsupp.ext
  intro j
  have hj : j = i := Subsingleton.elim _ _
  subst j
  rw [hc x hx, hc y hy]

end
end KIP126.Main.Solution.Computation
