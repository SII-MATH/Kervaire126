import KIP126.Interface.Challenge.Challenge2
import KIP126.LinProgram.Model.Product.Data

/-! Coordinates for the existing internal tower differential. No differential
is inferred from the table or supplied as new data. -/

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory

/-- The actual internal second differential, reindexed by natural bidegrees. -/
def sphereE2SecondDifferential (s t : ℕ) :
    sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) →ₗ[ℤ]
      sphereAdamsData.Page 2 (((s + 2 : ℕ) : ℤ), ((t + 1 : ℕ) : ℤ)) :=
  (sphereAdamsData.d 2 ((s : ℤ), (t : ℤ)) ≫ eqToHom (by
    change sphereAdamsData.Page 2 ((s : ℤ) + 2, (t : ℤ) + 1) =
      sphereAdamsData.Page 2 (((s + 2 : ℕ) : ℤ), ((t + 1 : ℕ) : ℤ))
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one])).hom

/-- Pull the existing d₂ back to Lin coordinates, only when both pages are
inside the certified range. This is not a differential on the entire
truncated quotient, and asserts no Leibniz law. -/
def LinE2Presentation.secondDifferential (P : LinE2Presentation)
    (s t : ℕ) (ht : t + 1 ≤ 261) :
    KIP126.LinE2.E2At s t →ₗ[ℤ] KIP126.LinE2.E2At (s + 2) (t + 1) :=
  (P.comparison (s + 2) (t + 1) ht).symm.toLinearMap.comp
    ((sphereE2SecondDifferential s t).comp
      (P.comparison s t (by omega)).toLinearMap)

end
end KIP126.Classical.Adams
