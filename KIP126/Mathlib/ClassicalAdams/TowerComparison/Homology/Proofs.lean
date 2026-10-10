import KIP126.Def.ClassicalAdams.TowerSequence.Data
import Mathlib.Algebra.Homology.ConcreteCategory

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
universe u v

/-- The concrete homology comparison retains the actual cycle element. -/
theorem moduleCatCyclesIso_cyclesMk {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (x : S.X₂) (hx : S.g x = 0) :
    S.moduleCatCyclesIso.hom (S.cyclesMk x hx) = ⟨x, hx⟩ := by
  apply Subtype.ext
  have h := congrArg (fun f => f.hom (S.cyclesMk x hx)) S.moduleCatCyclesIso_hom_i
  change (S.moduleCatCyclesIso.hom (S.cyclesMk x hx)).val = _ at h
  exact h.trans (S.i_cyclesMk x hx)

/-- Homology projection is the ordinary quotient of the specified cycle. -/
theorem moduleCatHomologyIso_cyclesMk {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (x : S.X₂) (hx : S.g x = 0) :
    S.moduleCatHomologyIso.hom (S.homologyπ (S.cyclesMk x hx)) =
      (LinearMap.range S.moduleCatToCycles).mkQ ⟨x, hx⟩ := by
  have h := congrArg (fun f => f.hom (S.cyclesMk x hx)) S.π_moduleCatCyclesIso_hom
  change S.moduleCatHomologyIso.hom (S.homologyπ (S.cyclesMk x hx)) =
    (LinearMap.range S.moduleCatToCycles).mkQ
      (S.moduleCatCyclesIso.hom (S.cyclesMk x hx)) at h
  exact h.trans (congrArg _ (moduleCatCyclesIso_cyclesMk S x hx))

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Tower page passage sends a next-cycle representative to its class on the next page. -/
theorem adamsPageHomologyIso_representative (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (x : adamsCycles unit X (r + 1) (by omega) p.1 p.2) :
    (adamsPageHomologyIso unit X r hr p).hom
      (((adamsPageComplex unit X r hr).sc p).homologyπ
        (((adamsPageComplex unit X r hr).sc p).cyclesMk
          (adamsNextCycleToPage unit X r hr p.1 p.2 x)
          (adamsNextCycle_d_zero unit X r hr p x))) =
      (adamsCycleBoundaries unit X (r + 1) (by omega) p.1 p.2).mkQ x := by
  let e := LinearEquiv.ofBijective (adamsNextPageToHomology unit X r hr p)
    (adamsNextPageToHomology_bijective unit X r hr p)
  change e.symm _ = _
  apply e.symm_apply_eq.mpr
  exact moduleCatHomologyIso_cyclesMk ((adamsPageComplex unit X r hr).sc p)
    (adamsNextCycleToPage unit X r hr p.1 p.2 x) (adamsNextCycle_d_zero unit X r hr p x)

/-- The specified page-passage isomorphism encodes exactly the common
next-cycle representative relation, in both directions. -/
theorem adamsPageHomologyIso_relation (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (x : adamsPage unit X r hr p.1 p.2)
    (y : adamsPage unit X (r + 1) (by omega) p.1 p.2)
    (hx : ((adamsPageComplex unit X r hr).sc p).g x = 0) :
    (∃ w : adamsCycles unit X (r + 1) (by omega) p.1 p.2,
      adamsNextCycleToPage unit X r hr p.1 p.2 w = x ∧
        (adamsCycleBoundaries unit X (r + 1) (by omega) p.1 p.2).mkQ w = y) ↔
    (adamsPageHomologyIso unit X r hr p).hom
      (((adamsPageComplex unit X r hr).sc p).homologyπ
        (((adamsPageComplex unit X r hr).sc p).cyclesMk x hx)) = y := by
  constructor
  · rintro ⟨w, rfl, rfl⟩
    exact adamsPageHomologyIso_representative unit X r hr p w
  · intro h
    obtain ⟨z, hz⟩ := (adamsCycleBoundaries unit X r hr p.1 p.2).mkQ_surjective x
    have hn : (classicalAdamsShape r).next p = (p.1 + r, p.2 + r - 1) := by
      apply ComplexShape.next_eq'
      change p + ((r : ℤ), (r : ℤ) - 1) = _
      apply Prod.ext <;> dsimp
      omega
    have hd := hx
    change (adamsPageD unit X r hr p ((classicalAdamsShape r).next p)).hom x = 0 at hd
    rw [hn, adamsPageD_target, ← hz] at hd
    let w : adamsCycles unit X (r + 1) (by omega) p.1 p.2 :=
      ⟨z.val, (adamsDifferentialValue_eq_zero_iff unit X r hr p.1 p.2 z).mp hd⟩
    have hw : adamsNextCycleToPage unit X r hr p.1 p.2 w = x := hz
    refine ⟨w, hw, ?_⟩
    have hp := adamsPageHomologyIso_representative unit X r hr p w
    have hc : ((adamsPageComplex unit X r hr).sc p).cyclesMk
        (adamsNextCycleToPage unit X r hr p.1 p.2 w)
        (adamsNextCycle_d_zero unit X r hr p w) =
        ((adamsPageComplex unit X r hr).sc p).cyclesMk x hx := by
      apply (ModuleCat.mono_iff_injective ((adamsPageComplex unit X r hr).sc p).iCycles).mp
        inferInstance
      exact (((adamsPageComplex unit X r hr).sc p).i_cyclesMk _ _).trans
        (hw.trans (((adamsPageComplex unit X r hr).sc p).i_cyclesMk x hx).symm)
    exact hp.symm.trans ((congrArg (fun z => (adamsPageHomologyIso unit X r hr p).hom
      (((adamsPageComplex unit X r hr).sc p).homologyπ z)) hc).trans h)

end
end KIP126.Classical.Adams
