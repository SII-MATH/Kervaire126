import KIP126.Mathlib.ClassicalAdams.TowerComparison.Page.Data

namespace KIP126.Classical.Adams

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The differential comparison survives the two purely notational reindexings. -/
theorem adamsTowerPageComparison_d_reindex (n k : ℕ) (hk : 1 ≤ k) (hn : n + 2 = k)
    (s t a b : ℤ) (ha : s + (n + 2 : ℕ) = a) (hb : t + (n + 2 : ℕ) - 1 = b) :
    (adamsTowerInternalD unit X n s t ≫ eqToHom (show
      (adamsTowerSSData unit X (s + (n + 2 : ℕ)) (t + (n + 2 : ℕ) - 1)).page ↑n =
        (adamsTowerSSData unit X a b).page ↑n by rw [ha, hb])) ≫
      ((adamsTowerSSDataPageIso unit X a b n).hom ≫ eqToHom (show
        ModuleCat.of ℤ (adamsPage unit X (n + 2) (by omega) a b) =
          adamsPageObject unit X k hk (a, b) by subst k; rfl)) =
    ((adamsTowerSSDataPageIso unit X s t n).hom ≫ eqToHom (show
      ModuleCat.of ℤ (adamsPage unit X (n + 2) (by omega) s t) =
        adamsPageObject unit X k hk (s, t) by subst k; rfl)) ≫
      adamsPageD unit X k hk (s, t) (a, b) := by
  subst k
  subst a
  subst b
  simp only [eqToHom_refl, Category.comp_id, adamsPageD_target]
  exact adamsTowerInternalD_comparison unit X n s t

/-- The all-page quotient comparison intertwines the actual tower differentials. -/
theorem adamsTowerPageComparison_differential (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    (adamsTowerPreSS unit X).d r p ≫
      (adamsTowerPageComparison unit X r hr
        (p + (r, r - 1))).hom =
    (adamsTowerPageComparison unit X r hr p).hom ≫
      ((adamsTowerSpectralSequence unit X).page r hr).d p
        (p + (r, r - 1)) := by
  cases r with
  | negSucc k => omega
  | ofNat k =>
    have hk : (2 : ℤ) ≤ (k : ℤ) := hr
    rcases p with ⟨s, t⟩
    have hn : (Int.ofNat k - 2).toNat + 2 = k := by
      change ((k : ℤ) - 2).toNat + 2 = k
      omega
    refine (congrArg (fun f => f ≫ (adamsTowerPageComparison unit X (Int.ofNat k) hr
      ((s, t) + (Int.ofNat k, Int.ofNat k - 1))).hom)
      (adamsTowerPreSS_d_eq unit X (Int.ofNat k) (s, t) hr)).trans ?_
    have h := adamsTowerPageComparison_d_reindex unit X (Int.ofNat k - 2).toNat k
      (by omega) hn s t (s + (k : ℤ)) (t + ((k : ℤ) - 1))
      (by rw [hn]) (by rw [hn]; omega)
    dsimp only [adamsTowerPageComparison,
      adamsTowerSpectralSequence, adamsPageComplex]
    simp only [Iso.trans_hom, eqToIso.hom, Prod.mk_add_mk, Int.ofNat_eq_natCast] at h ⊢
    exact h

end
end KIP126.Classical.Adams
