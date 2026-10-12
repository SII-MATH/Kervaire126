module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

@[reassoc] theorem coneBoundary_map {X Y X' Y' : Prespectrum.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    coneMap a b h ≫ coneBoundary g = coneBoundary f ≫ suspensionMap a := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro z
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,s⟩)
  · exact ((suspensionMap a).point n).symm
  · rfl

/-- The Puppe comparison commutes with the actual maps of double cones
induced by any strict square. -/
@[reassoc] theorem coneIterationComparison_natural {X Y X' Y' : Prespectrum.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    coneMap b (coneMap a b h) (coneInclusion_map a b h) ≫ coneIterationComparison g =
      coneIterationComparison f ≫ suspensionMap a := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro z
  refine Quot.inductionOn z ?_
  rintro (w | ⟨y,s⟩)
  · exact congrArg (fun k : cone f ⟶ X'.suspension => k.level n w) (coneBoundary_map a b h)
  · exact ((suspensionMap a).point n).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
