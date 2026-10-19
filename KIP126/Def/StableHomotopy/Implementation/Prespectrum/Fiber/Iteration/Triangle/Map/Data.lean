module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Triangle.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Pretriangulated
universe u

/-- A proved map of actual source fiber sequences gives a genuine triangle
morphism, with all three displayed component maps retained. -/
noncomputable def sourceFiberTriangleMap {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : sourceLocalization.obj X ⟶ sourceLocalization.obj X')
    (b : sourceLocalization.obj Y ⟶ sourceLocalization.obj Y')
    (c : sourceLocalization.obj (fiber f) ⟶ sourceLocalization.obj (fiber g))
    (hp : sourceLocalization.map (fiberProjection f) ≫ a =
      c ≫ sourceLocalization.map (fiberProjection g))
    (hf : sourceLocalization.map f ≫ b = a ≫ sourceLocalization.map g)
    (hc : sourceLocalization.map (fiberConnecting f) ≫ c =
      sourceLoopFunctor.map b ≫ sourceLocalization.map (fiberConnecting g)) :
    sourceFiberTriangle f ⟶ sourceFiberTriangle g :=
  Triangle.homMk _ _ c a b hp hf (sourceFiberBoundary_natural f g b c hc)

end KIP126.StableHomotopy.Implementation.Prespectrum
