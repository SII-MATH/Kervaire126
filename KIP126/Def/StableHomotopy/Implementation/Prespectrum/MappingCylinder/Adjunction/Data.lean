module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Adjunction.Hom.Proofs
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual reduced mapping cylinder and original compact-open path
prespectrum form a strict adjunction, before any localization. -/
noncomputable def cylinderPathAdjunction : cylinderFunctor.{u} ⊣ pathFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun _ _ => {
      toFun := cylinderPathCurry
      invFun := cylinderPathUncurry
      left_inv := cylinderPathUncurry_curry
      right_inv := cylinderPathCurry_uncurry }
    homEquiv_naturality_left_symm := cylinderPathUncurry_natural_left
    homEquiv_naturality_right := cylinderPathCurry_natural_right }

end KIP126.StableHomotopy.Implementation.Prespectrum
