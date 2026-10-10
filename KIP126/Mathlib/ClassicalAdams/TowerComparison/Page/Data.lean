import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
import KIP126.Def.ClassicalAdams.TowerSequence.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The all-page comparison is the actual representative-preserving quotient
isomorphism, followed only by the equality between the two page-number conventions. -/
def adamsTowerPageComparison (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    (adamsTowerPreSS unit X).Page r p ≅
      ((adamsTowerSpectralSequence unit X).page r hr).X p :=
  adamsTowerSSDataPageIso unit X p.1 p.2 (r - 2).toNat ≪≫ eqToIso (by
    cases r with
    | ofNat k =>
      change (2 : ℤ) ≤ (k : ℤ) at hr
      have hk : ((k : ℤ) - 2).toNat + 2 = k := by omega
      have hpage (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a = b) :
          adamsPageObject unit X a ha p = adamsPageObject unit X b hb p := by
        subst b
        rfl
      exact hpage (((k : ℤ) - 2).toNat + 2) k (by omega) (by omega) hk
    | negSucc k => omega)

end
end KIP126.Classical.Adams
