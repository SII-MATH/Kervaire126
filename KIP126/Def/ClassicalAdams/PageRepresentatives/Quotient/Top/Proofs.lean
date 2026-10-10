import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Top.Data

namespace KIP126.Classical.Adams.PageRepresentatives

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Algebra

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

/-- After the λ quotient, exactly the indicated classical boundaries vanish. -/
theorem quotientMap_finiteTopClass_eq_zero (q k : ℕ) (hkq : k < q) (p : ℤ × ℤ)
    (z : cycles H X (q - k : ℕ) p) :
    quotientMap H X (c' := q - p.2 + (p.2 - k))
      (b' := 1 + p.2 - (p.2 - k)) (by omega) (by omega) p
      (finiteTopClass H X (q - k) p z) = 0 ↔
        z.val ∈ boundaries H X (1 + k) p := by
  have h : 1 + p.2 - (p.2 - (k : ℤ)) = 1 + k := by omega
  have he := NestedQuotient.map_projection_eq_zero
    (cycles_antitone H X p (show (q : ℤ) - p.2 + (p.2 - k) ≤
      (q - k : ℕ) - p.2 + p.2 by omega))
    (boundaries_monotone H X p (show 1 + p.2 - p.2 ≤ 1 + p.2 - (p.2 - (k : ℤ)) by omega))
    (Submodule.inclusion (show cycles H X (q - k : ℕ) p ≤
      cycles H X ((q - k : ℕ) - p.2 + p.2) p by rw [sub_add_cancel]) z)
  change quotientMap H X (by omega) (by omega) p (finiteTopClass H X (q - k) p z) = 0 ↔
    z.val ∈ boundaries H X (1 + p.2 - (p.2 - (k : ℤ))) p at he
  exact he.trans (by rw [h])

theorem permanentQuotientMap_topClass_eq_zero (k : ℕ) (p : ℤ × ℤ)
    (z : permanentCycles H X p) :
    permanentQuotientMap H X (b' := 1 + p.2 - (p.2 - k)) (by omega) p
      (permanentTopClass H X p z) = 0 ↔
        z.val ∈ boundaries H X (1 + k) p := by
  have h : 1 + p.2 - (p.2 - (k : ℤ)) = 1 + k := by omega
  have he := NestedQuotient.map_projection_eq_zero
    (le_refl (permanentCycles H X p))
    (boundaries_monotone H X p (show 1 + p.2 - p.2 ≤ 1 + p.2 - (p.2 - (k : ℤ)) by omega)) z
  change permanentQuotientMap H X (by omega) p (permanentTopClass H X p z) = 0 ↔
    z.val ∈ boundaries H X (1 + p.2 - (p.2 - (k : ℤ))) p at he
  exact he.trans (by rw [h])

end KIP126.Classical.Adams.PageRepresentatives
