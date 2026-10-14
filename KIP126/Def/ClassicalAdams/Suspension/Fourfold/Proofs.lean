module

public import KIP126.Def.ClassicalAdams.Suspension.Fourfold.Data
public import KIP126.Def.ClassicalAdams.Suspension.Internal.Proofs

@[expose] public section


namespace KIP126.Classical.Adams.Suspension.Fourfold

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Core.SpectralSequence

universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

theorem quadShiftIso_hom (X : C) :
    (quadShiftIso X).hom =
      (((shiftFunctorAdd C (1 : ℤ) (1 : ℤ)).inv.app X)⟦(1 : ℤ)⟧')⟦(1 : ℤ)⟧' ≫
        ((shiftFunctorAdd C (2 : ℤ) (1 : ℤ)).inv.app X)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd C (3 : ℤ) (1 : ℤ)).inv.app X := rfl

theorem quadShiftIso_inv (X : C) :
    (quadShiftIso X).inv =
      ((shiftFunctorAdd C (3 : ℤ) (1 : ℤ)).hom.app X ≫
        ((shiftFunctorAdd C (2 : ℤ) (1 : ℤ)).hom.app X)⟦(1 : ℤ)⟧') ≫
        (((shiftFunctorAdd C (1 : ℤ) (1 : ℤ)).hom.app X)⟦(1 : ℤ)⟧')⟦(1 : ℤ)⟧' := rfl

variable [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {X : C}
  (S₀ : TowerComparison H X)
  (S₁ : TowerComparison H (X⟦(1 : ℤ)⟧))
  (S₂ : TowerComparison H ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧))
  (S₃ : TowerComparison H (((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧))

/-- Four actual desuspensions preserve the complete differential relation.
No additional compatibility law or page-range hypothesis is introduced. -/
theorem desuspendFourInternalPage_hasDifferential
    {r : ℤ} {p q : ℤ × ℤ}
    {x : (adamsTowerInternalSpectralSequence H.unit (quadShift X)).Page 2 p}
    {y : (adamsTowerInternalSpectralSequence H.unit (quadShift X)).Page 2 q}
    (h : HasDifferential (adamsTowerInternalSpectralSequence H.unit (quadShift X))
      r p q x y) :
    HasDifferential (adamsTowerInternalSpectralSequence H.unit X) r
      (p.1, p.2 - 1 - 1 - 1 - 1) (q.1, q.2 - 1 - 1 - 1 - 1)
      (desuspendFourInternalPage S₀ S₁ S₂ S₃ 2 p x)
      (desuspendFourInternalPage S₀ S₁ S₂ S₃ 2 q y) := by
  have h₂ := S₂.desuspendTwiceInternalPage_hasDifferential S₃ h
  have h₄ := S₀.desuspendTwiceInternalPage_hasDifferential S₁ h₂
  simpa only [desuspendFourInternalPage, ModuleCat.comp_apply] using h₄

/-- Eight actual representative comparisons, one per endpoint at each
suspension, transfer the differential without an independent page map. -/
theorem hasDifferential_desuspendFour
    {r s t u v : ℤ}
    {x₄ : PageRepresentatives.Ambient H (quadShift X) (s, t)}
    {y₄ : PageRepresentatives.Ambient H (quadShift X) (u, v)}
    {x₃ : PageRepresentatives.Ambient H
      (((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧) (s, t - 1)}
    {y₃ : PageRepresentatives.Ambient H
      (((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧) (u, v - 1)}
    {x₂ : PageRepresentatives.Ambient H
      ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧) (s, t - 1 - 1)}
    {y₂ : PageRepresentatives.Ambient H
      ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧) (u, v - 1 - 1)}
    {x₁ : PageRepresentatives.Ambient H (X⟦(1 : ℤ)⟧) (s, t - 1 - 1 - 1)}
    {y₁ : PageRepresentatives.Ambient H (X⟦(1 : ℤ)⟧) (u, v - 1 - 1 - 1)}
    {x₀ : PageRepresentatives.Ambient H X (s, t - 1 - 1 - 1 - 1)}
    {y₀ : PageRepresentatives.Ambient H X (u, v - 1 - 1 - 1 - 1)}
    (hx₃ : S₃.DesuspendsClass s t x₄ x₃)
    (hy₃ : S₃.DesuspendsClass u v y₄ y₃)
    (hx₂ : S₂.DesuspendsClass s (t - 1) x₃ x₂)
    (hy₂ : S₂.DesuspendsClass u (v - 1) y₃ y₂)
    (hx₁ : S₁.DesuspendsClass s (t - 1 - 1) x₂ x₁)
    (hy₁ : S₁.DesuspendsClass u (v - 1 - 1) y₂ y₁)
    (hx₀ : S₀.DesuspendsClass s (t - 1 - 1 - 1) x₁ x₀)
    (hy₀ : S₀.DesuspendsClass u (v - 1 - 1 - 1) y₁ y₀)
    (h : HasDifferential
      (adamsTowerInternalSpectralSequence H.unit (quadShift X))
      r (s, t) (u, v) x₄ y₄) :
    HasDifferential (adamsTowerInternalSpectralSequence H.unit X)
      r (s, t - 1 - 1 - 1 - 1) (u, v - 1 - 1 - 1 - 1) x₀ y₀ := by
  have h₂ := S₂.hasDifferential_desuspendTwice S₃ hx₃ hy₃ hx₂ hy₂ h
  exact S₀.hasDifferential_desuspendTwice S₁ hx₁ hy₁ hx₀ hy₀ h₂

end
end KIP126.Classical.Adams.Suspension.Fourfold
