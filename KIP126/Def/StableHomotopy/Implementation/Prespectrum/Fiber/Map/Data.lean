module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

/-- The actual map of path homotopy fibers induced by a strictly commuting
square: apply the source map to the point and the target map to its path. -/
def fiberMap {X Y X' Y' : Prespectrum.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) : fiber f ⟶ fiber g where
  level n :=
    { toFun z := ⟨(a.level n z.val.1,(b.level n).comp z.val.2),⟨by
        change b.level n (z.val.2 0) = g.level n (a.level n z.val.1)
        rw [z.property.1]
        exact congrArg (fun k : X ⟶ Y' => k.level n z.val.1) h, by
        change b.level n (z.val.2 1) = (Y'.level n).point
        rw [z.property.2,b.point]⟩⟩
      continuous_toFun := ((a.level n).continuous.comp continuous_subtype_val.fst).prodMk
        ((ContinuousMap.continuous_postcomp (b.level n)).comp continuous_subtype_val.snd)
        |>.subtype_mk _ }
  point n := by
    apply Subtype.ext
    apply Prod.ext
    · exact a.point n
    · apply ContinuousMap.ext; intro s; exact b.point n
  bond n z t := by
    apply Subtype.ext
    apply Prod.ext
    · exact a.bond n z.val.1 t
    · apply ContinuousMap.ext; intro s; exact b.bond n (z.val.2 s) t

end KIP126.StableHomotopy.Implementation.Prespectrum
