module

public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Proofs
public import KIP126.Def.StableHomotopy.RepresentedHom.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasProductsOfShape ℕ C]

/-- A surjective next-degree difference map removes precisely the
ambiguity of represented maps with fixed Milnor projections. -/
theorem SequentialHomotopyLimit.shiftedHom_ext_of_surjective
    {D : InverseSequence C} {L : C} (H : SequentialHomotopyLimit D L)
    (U : C) (d : ℤ)
    (hsurj : Function.Surjective
      (fun z : ShiftedHom U (d + 1) (∏ᶜ D.obj) => z ≫ D.oneSubShift))
    {a b : ShiftedHom U d L} (hab : ∀ k, a ≫ H.π k = b ≫ H.π k) : a = b := by
  let T : HoCofiberSequence (C := C) :=
    ⟨L, ∏ᶜ D.obj, ∏ᶜ D.obj, H.toProduct, D.oneSubShift, H.boundary, H.distinguished⟩
  have hinj : Function.Injective (postcomposeLinearMap U ((d + 1) - 1) T.f) := by
    intro x y hxy
    have hz : postcomposeLinearMap U ((d + 1) - 1) T.f (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := (RepresentedHom.exact_h U T (d + 1) (x - y)).mp hz
    have hz₀ : connectingLinearMap U T (d + 1) z = 0 := by
      apply (RepresentedHom.exact_g U T (d + 1) z).mpr
      exact hsurj z
    exact sub_eq_zero.mp (hz.symm.trans hz₀)
  have hinj' : Function.Injective (postcomposeLinearMap U d H.toProduct) := by
    have hd : d + 1 - 1 = d := by omega
    rw [hd] at hinj
    exact hinj
  apply hinj'
  apply Pi.hom_ext
  intro k
  change (a ≫ H.toProduct) ≫ Pi.π D.obj k = (b ≫ H.toProduct) ≫ Pi.π D.obj k
  simpa only [Category.assoc, SequentialHomotopyLimit.π] using hab k

end KIP126.StableHomotopy
