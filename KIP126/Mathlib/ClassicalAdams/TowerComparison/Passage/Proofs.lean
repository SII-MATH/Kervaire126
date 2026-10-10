import KIP126.Mathlib.ClassicalAdams.TowerComparison.Page.Data
import KIP126.Mathlib.ClassicalAdams.TowerComparison.Homology.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.PagePassage.Proofs
import KIP126.Def.SpectralSequence.Permanence.Predicates
import KIP126.Mathlib.SpectralSequence.Permanence.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Compare successor relations before specializing the page-number equalities. -/
theorem adamsTowerPageComparison_passage_reindex
    (n m k : ℕ) (hk : 1 ≤ k) (hn : n + 2 = k) (hm : n + 1 = m)
    (s t : ℤ)
    (x : (adamsTowerSSData unit X s t).page (n : WithTop ℕ))
    (y : (adamsTowerSSData unit X s t).page (m : WithTop ℕ))
    (hx : ((adamsPageComplex unit X k hk).sc (s, t)).g
      (((adamsTowerSSDataPageIso unit X s t n).hom ≫ eqToHom (show
        ModuleCat.of ℤ (adamsPage unit X (n + 2) (by omega) s t) =
          adamsPageObject unit X k hk (s, t) by subst k; rfl)) x) = 0) :
    (∃ z : (Subobject.underlying.obj
        ((adamsTowerSSData unit X s t).Z (m : WithTop ℕ)) : ModuleCat ℤ),
      (Subobject.ofLE ((adamsTowerSSData unit X s t).Z (m : WithTop ℕ))
        ((adamsTowerSSData unit X s t).Z (n : WithTop ℕ))
        ((adamsTowerSSData unit X s t).Z_anti (by exact_mod_cast (show n ≤ m by omega))) ≫
        (adamsTowerSSData unit X s t).pageπ (n : WithTop ℕ)) z = x ∧
      (adamsTowerSSData unit X s t).pageπ (m : WithTop ℕ) z = y) ↔
    (adamsPageHomologyIso unit X k hk (s, t)).hom
      (((adamsPageComplex unit X k hk).sc (s, t)).homologyπ
        (((adamsPageComplex unit X k hk).sc (s, t)).cyclesMk _ hx)) =
      ((adamsTowerSSDataPageIso unit X s t m).hom ≫ eqToHom (show
        ModuleCat.of ℤ (adamsPage unit X (m + 2) (by omega) s t) =
          adamsPageObject unit X (k + 1) (by omega) (s, t) by subst m; subst k; rfl)) y := by
  subst m
  subst k
  exact (adamsTowerSSData_next_relation unit X s t n x y).trans
    (adamsPageHomologyIso_relation unit X (n + 2) hk (s, t)
      ((adamsTowerSSDataPageIso unit X s t n).hom x)
      ((adamsTowerSSDataPageIso unit X s t (n + 1)).hom y) hx)

/-- The constructed all-page comparison respects the specified successor class. -/
theorem adamsTowerPageComparison_passage (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    (x : (adamsTowerInternalSpectralSequence unit X).Page r p)
    (y : (adamsTowerInternalSpectralSequence unit X).Page (r + 1) p)
    (hx : ((adamsTowerSpectralSequence unit X).page r hr).d p
      ((classicalAdamsShape r).next p) ((adamsTowerPageComparison unit X r hr p).hom x) = 0) :
    NextPageRelation (adamsTowerInternalSpectralSequence unit X) r p x y ↔
      nextPageClass (adamsTowerSpectralSequence unit X) r hr p
        ((adamsTowerPageComparison unit X r hr p).hom x) hx =
          (adamsTowerPageComparison unit X (r + 1) (by omega) p).hom y := by
  cases r with
  | negSucc k => omega
  | ofNat k =>
    have hk : (2 : ℤ) ≤ (k : ℤ) := hr
    have hn : (Int.ofNat k - 2).toNat + 2 = k := by
      change ((k : ℤ) - 2).toNat + 2 = k
      omega
    have hm : (Int.ofNat k - 2).toNat + 1 = (Int.ofNat k + 1 - 2).toNat := by
      change ((k : ℤ) - 2).toNat + 1 = ((k : ℤ) + 1 - 2).toNat
      omega
    rcases p with ⟨s, t⟩
    exact adamsTowerPageComparison_passage_reindex unit X
      (Int.ofNat k - 2).toNat (Int.ofNat k + 1 - 2).toNat k (by omega)
      hn hm s t x y hx

end
end KIP126.Classical.Adams
