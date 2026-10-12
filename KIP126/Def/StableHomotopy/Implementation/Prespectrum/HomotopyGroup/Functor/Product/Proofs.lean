module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Product.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Preadditive

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

instance sourceStableHomotopyAddFunctor_preservesProduct {J : Type} [Finite J]
    (X : J → Prespectrum.{u}) (d : ℤ) :
    PreservesLimit (Discrete.functor (fun j => sourceLocalization.obj (X j)))
      (sourceStableHomotopyAddFunctor d) :=
  preservesLimit_of_preserves_limit_cone (Prespectrum.sourceProductIsLimit X)
    (sourceStableHomotopyAddFunctor_productIsLimit X d)

instance sourceStableHomotopyAddFunctor_preservesProductsOfShape (J : Type) [Finite J] (d : ℤ) :
    PreservesLimitsOfShape (Discrete J) (sourceStableHomotopyAddFunctor.{u} d) where
  preservesLimit {K} := by
    letI : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk))
        (sourceStableHomotopyAddFunctor d) :=
      sourceStableHomotopyAddFunctor_preservesProduct (fun j => (K.obj (Discrete.mk j)).as.obj) d
    exact preservesLimit_of_iso_diagram (sourceStableHomotopyAddFunctor d)
      Discrete.natIsoFunctor.symm

instance sourceStableHomotopyAddFunctor_preservesFiniteProducts (d : ℤ) :
    PreservesFiniteProducts (sourceStableHomotopyAddFunctor.{u} d) :=
  ⟨fun _ => inferInstance⟩

/-- The original abelian stable homotopy functor is additive for the actual
constructed source hom groups. -/
instance sourceStableHomotopyAddFunctor_additive (d : ℤ) :
    (sourceStableHomotopyAddFunctor.{u} d).Additive :=
  Functor.additive_of_preserves_binary_products _

end KIP126.StableHomotopy.Implementation
