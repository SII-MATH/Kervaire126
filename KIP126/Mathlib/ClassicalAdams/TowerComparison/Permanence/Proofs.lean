import KIP126.Def.ClassicalAdams.TowerSSData.Permanence.Proofs
import KIP126.Mathlib.ClassicalAdams.TowerComparison.Homology.Proofs
import KIP126.Mathlib.ClassicalAdams.TowerComparison.Page.Data
import KIP126.Mathlib.SpectralSequence.Permanence.Proofs

namespace KIP126.Classical.Adams

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The standard successor condition, including being a differential cycle,
is exactly the actual next-cycle representative condition. -/
theorem adamsTower_nextPage_iff (n : ℕ) (p : ℤ × ℤ)
    (x : adamsPage unit X (n + 2) (by omega) p.1 p.2)
    (y : adamsPage unit X (n + 2 + 1) (by omega) p.1 p.2) :
    (∃ hx : ((adamsPageComplex unit X (n + 2) (by omega)).sc p).g x = 0,
      (adamsPageHomologyIso unit X (n + 2) (by omega) p).hom
        (((adamsPageComplex unit X (n + 2) (by omega)).sc p).homologyπ
          (((adamsPageComplex unit X (n + 2) (by omega)).sc p).cyclesMk x hx)) = y) ↔
    ∃ w : adamsCycles unit X (n + 2 + 1) (by omega) p.1 p.2,
      adamsNextCycleToPage unit X (n + 2) (by omega) p.1 p.2 w = x ∧
        (adamsCycleBoundaries unit X (n + 2 + 1) (by omega) p.1 p.2).mkQ w = y := by
  constructor
  · rintro ⟨hx, hy⟩
    exact (adamsPageHomologyIso_relation unit X (n + 2) (by omega) p x y hx).mpr
      hy
  · rintro ⟨w, rfl, rfl⟩
    exact ⟨adamsNextCycle_d_zero unit X (n + 2) (by omega) p w,
      adamsPageHomologyIso_representative unit X (n + 2) (by omega) p w⟩

/-- Express standard pagewise permanence using the tower's actual quotient
classes on natural-numbered pages. -/
theorem adamsTower_isPermanent_iff_compatible (s t : ℤ)
    (x : adamsPage unit X 2 (by omega) s t) :
    IsPermanent (adamsTowerSpectralSequence unit X) 2 (by decide) (s, t) x ↔
      ∃ y : ∀ n : ℕ, adamsPage unit X (n + 2) (by omega) s t,
        y 0 = x ∧ (∀ n : ℕ, y n ≠ 0) ∧
        (∀ n : ℕ, ∃ w : adamsCycles unit X (n + 2 + 1) (by omega) s t,
          adamsNextCycleToPage unit X (n + 2) (by omega) s t w = y n ∧
          (adamsCycleBoundaries unit X (n + 2 + 1) (by omega) s t).mkQ w = y (n + 1)) := by
  have hidx := isPermanent_iff_indexed (adamsTowerSpectralSequence unit X) 2 (by decide)
    (s, t) x (fun n => Int.ofNat (n + 2))
    (fun n => by change (2 : ℤ) ≤ ((n + 2 : ℕ) : ℤ); omega)
    (funext fun n => (iteratedPage_two_eq n).symm)
  refine hidx.trans ?_
  constructor
  · rintro ⟨y, h0, hn, hs⟩
    dsimp only [adamsTowerSpectralSequence, adamsPageComplex] at y h0 hn hs
    refine ⟨y, eq_of_heq h0, hn, ?_⟩
    intro n
    obtain ⟨hx, hy⟩ := hs n
    exact (adamsTower_nextPage_iff unit X n (s, t) (y n) (y (n + 1))).mp
      ⟨hx, eq_of_heq hy⟩
  · rintro ⟨y, h0, hn, hs⟩
    refine ⟨y, heq_of_eq h0, hn, ?_⟩
    intro n
    obtain ⟨hx, hy⟩ := (adamsTower_nextPage_iff unit X n (s, t) (y n) (y (n + 1))).mpr (hs n)
    exact ⟨hx, heq_of_eq hy⟩

/-- The common-representative condition and standard nonzero pagewise
permanence agree for every E₂ class of the same actual tower. -/
theorem adamsTower_survival_comparison (p : ℤ × ℤ)
    (x : (adamsTowerInternalSpectralSequence unit X).Page 2 p) :
    NonzeroSurvival (adamsTowerInternalSpectralSequence unit X) p x ↔
      IsPermanent (adamsTowerSpectralSequence unit X) 2 (by decide) p
        ((adamsTowerPageComparison unit X 2 (by decide) p).hom x) := by
  rcases p with ⟨s, t⟩
  have h := (adamsTower_nonzeroSurvival_iff_compatible unit X s t x).trans
    (adamsTower_isPermanent_iff_compatible unit X s t
      ((adamsTowerSSDataPageIso unit X s t 0).hom x)).symm
  have hp : (adamsTowerPageComparison unit X 2 (by decide) (s, t)).hom =
      (adamsTowerSSDataPageIso unit X s t 0).hom := by
    change ((adamsTowerSSDataPageIso unit X s t 0) ≪≫ eqToIso _).hom = _
    simp only [Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  have hpred := congrArg (fun f :
      (adamsTowerPreSS unit X).Page 2 (s, t) ⟶
        ((adamsTowerSpectralSequence unit X).page 2 (by decide)).X (s, t) =>
      IsPermanent (adamsTowerSpectralSequence unit X) 2 (by decide) (s, t) (f x)) hp
  exact h.trans (Iff.of_eq hpred).symm

end
end KIP126.Classical.Adams
