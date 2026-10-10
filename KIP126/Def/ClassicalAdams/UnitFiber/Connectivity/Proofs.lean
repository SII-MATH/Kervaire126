import KIP126.Def.ClassicalAdams.UnitFiber.Homotopy.Proofs
import KIP126.Def.ClassicalAdams.TowerSmash.Pairing.Right.Connectivity.Proofs

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))

/-- If negative homotopy vanishing detects the connective half of the
t-structure, the unit fiber's connectivity follows from sphere connectivity.
The detection property is explicit: it is not in the current fixed foundation. -/
theorem mod2UnitFiber_isLE_of_homotopy (t : Triangulated.TStructure C)
    (hdetect : ∀ X : C, (∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n X)) →
      t.IsLE X 0)
    (hsphere : ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n (SphereSpectrum : C))) :
    t.IsLE (fiber H.unit) 0 := by
  apply hdetect
  intro n hn
  exact mod2UnitFiber_homotopy_subsingleton H n (hsphere n hn)

omit [HasFunctorialCofiber (C := C)] in
/-- Positive homotopy vanishing of the supplied HF2 object places it in the
coconnective half when the t-structure detects that vanishing. -/
theorem mod2EilenbergMacLane_isGE_of_homotopy (t : Triangulated.TStructure C)
    (hdetect : ∀ X : C, (∀ n : ℤ, 0 < n → Subsingleton (HomotopyGroup n X)) →
      t.IsGE X 0) : t.IsGE H.HF2 0 := by
  apply hdetect
  intro n hn
  exact H.homotopy_vanishes n (by omega)

/-- Derive the two-factor inclusion condition from sphere connectivity,
homotopy detection of the t-structure bounds, and connective tensor closure.
No connectivity hypothesis is imposed separately on the unit fiber or HF2. -/
theorem mod2UnitFiber_inclusionCommutes_of_homotopy (t : Triangulated.TStructure C)
    (hle : ∀ X : C, (∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n X)) → t.IsLE X 0)
    (hge : ∀ X : C, (∀ n : ℤ, 0 < n → Subsingleton (HomotopyGroup n X)) → t.IsGE X 0)
    (htensor : ∀ X Y : C, t.IsLE X 0 → t.IsLE Y 0 → t.IsLE (X ⊗ Y) 0)
    (hsphere : ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n (SphereSpectrum : C))) :
    UnitFiberInclusionCommutes H.unit := by
  letI := mod2UnitFiber_isLE_of_homotopy H t hle hsphere
  letI := mod2EilenbergMacLane_isGE_of_homotopy H t hge
  exact unitFiberInclusionCommutes_of_tStructure H.unit t htensor

variable [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated] [MonoidalPreadditive C]

/-- Apply the preceding lower hypotheses to the pairing on the actual
HF2-based sphere tower. This still does not assert Leibniz or coherence. -/
theorem mod2SpherePairing_step_right_of_homotopy (t : Triangulated.TStructure C)
    (hle : ∀ X : C, (∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n X)) → t.IsLE X 0)
    (hge : ∀ X : C, (∀ n : ℤ, 0 < n → Subsingleton (HomotopyGroup n X)) → t.IsGE X 0)
    (htensor : ∀ X Y : C, t.IsLE X 0 → t.IsLE Y 0 → t.IsLE (X ⊗ Y) 0)
    (hsphere : ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n (SphereSpectrum : C)))
    (s q : ℕ) :
    adamsTowerSpherePairingNextRight H.unit s q ≫
        adamsTowerStep H.unit (𝟙_ C) (q + s) =
      (adamsTower H.unit (𝟙_ C) s ◁ adamsTowerStep H.unit (𝟙_ C) q) ≫
        (adamsTowerSpherePairingIso H.unit s q).hom :=
  adamsTowerSpherePairingIso_step_right H.unit
    (mod2UnitFiber_inclusionCommutes_of_homotopy H t hle hge htensor hsphere) s q

end KIP126.Classical.Adams
