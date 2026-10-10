import KIP126.Def.ClassicalAdams.Moss.Crossing.Predicates

namespace KIP126.Classical.Adams.Moss

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  {H : C} (unit : 𝟙_ C ⟶ H) (X Y : C)

/-- There is no possible nonnegative crossing source below this bound. -/
theorem noMossCrossing_of_filtration_le {r : ℤ} {k : ℤ × ℤ}
    (hk : k.1 ≤ r - 1) : NoMossCrossing unit X Y r k := by
  rintro ⟨m, q, _, hq, hbelow, _, _⟩
  omega

/-- The differential target has the product's stem, with filtration q+m. -/
theorem crossing_target_stem (m q : ℤ) (k : ℤ × ℤ) :
    (crossingSourceDegree k q + (mappingSequence unit X Y).diffDeg m).2 -
      (crossingSourceDegree k q + (mappingSequence unit X Y).diffDeg m).1 =
        k.2 - k.1 := by
  change (q + (k.2 - k.1) + 1 + (m - 1)) - (q + m) = k.2 - k.1
  omega

end KIP126.Classical.Adams.Moss
