module

public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Proofs
public import KIP126.Def.StableHomotopy.RepresentedHom.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasProductsOfShape ℕ C]

/-- Orthogonality to two consecutive shifts at every stage passes to the
actual Milnor homotopy limit. The second degree also kills the derived limit. -/
theorem SequentialHomotopyLimit.shiftedHom_subsingleton
    {D : InverseSequence C} {L : C} (H : SequentialHomotopyLimit D L)
    (U : C) (d : ℤ)
    (hD : ∀ k, Subsingleton (ShiftedHom U d (D.obj k)))
    (hD₁ : ∀ k, Subsingleton (ShiftedHom U (d + 1) (D.obj k))) :
    Subsingleton (ShiftedHom U d L) := by
  let T : HoCofiberSequence (C := C) :=
    ⟨L, ∏ᶜ D.obj, ∏ᶜ D.obj, H.toProduct, D.oneSubShift, H.boundary, H.distinguished⟩
  have hz (a : ShiftedHom U ((d + 1) - 1) L) : a = 0 := by
    have ha : postcomposeLinearMap U ((d + 1) - 1) T.f a = 0 := by
      apply Pi.hom_ext
      intro k
      letI : Subsingleton (ShiftedHom U ((d + 1) - 1) (D.obj k)) := by
        simpa only [add_sub_cancel_right] using hD k
      exact Subsingleton.elim _ _
    obtain ⟨z, hza⟩ := (RepresentedHom.exact_h U T (d + 1) a).mp ha
    have hz : z = 0 := by
      apply Pi.hom_ext
      intro k
      letI := hD₁ k
      exact Subsingleton.elim _ _
    rw [hz, map_zero] at hza
    exact hza.symm
  have h : Subsingleton (ShiftedHom U ((d + 1) - 1) L) :=
    ⟨fun a b => (hz a).trans (hz b).symm⟩
  simpa only [add_sub_cancel_right] using h

end KIP126.StableHomotopy
