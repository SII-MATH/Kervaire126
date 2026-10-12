module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- A strict map with a specified strict nullhomotopy of its composite
lifts to the actual homotopy fiber, retaining that entire nullhomotopy. -/
def fiberLift {A X Y : Prespectrum.{u}} (f : X ⟶ Y) (a : A ⟶ X)
    (H : A ⟶ pathPrespectrum Y) (h₀ : H ≫ pathEvaluation Y 0 = a ≫ f)
    (h₁ : H ≫ pathEvaluation Y 1 = zeroMap A Y) : A ⟶ fiber f where
  level n :=
    { toFun := fun x => ⟨(a.level n x, H.level n x),
        ⟨congrArg (fun k : A ⟶ Y => k.level n x) h₀,
          congrArg (fun k : A ⟶ Y => k.level n x) h₁⟩⟩
      continuous_toFun := ((a.level n).continuous.prodMk (H.level n).continuous).subtype_mk _ }
  point n := Subtype.ext (Prod.ext (a.point n) (H.point n))
  bond n x t := Subtype.ext (Prod.ext (a.bond n x t) (H.bond n x t))

end KIP126.StableHomotopy.Implementation.Prespectrum
