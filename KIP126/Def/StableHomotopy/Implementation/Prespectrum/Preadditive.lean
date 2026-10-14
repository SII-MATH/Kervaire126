module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Preadditive.Hom
public import KIP126.Def.CategoryTheory.Preadditive.Bilinear.Data
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- The original ordinary stable localization is preadditive, with addition
constructed from actual path concatenation and the proved loop equivalence. -/
noncomputable instance sourcePreadditive : Preadditive SourceCategory.{u} := by
  letI := sourceHomGroup
  exact KIP126.Foundation.preadditiveOfBilinearHomGroups
    sourceHomGroup_add_comp sourceHomGroup_comp_add

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The constructed additive zero is the original source zero morphism. -/
theorem sourcePreadditive_zero (A B : SourceCategory.{u}) :
    (sourcePreadditive.homGroup A B).zero =
      @Zero.zero (A ⟶ B) (sourceHasZeroMorphisms.zero A B) := rfl

instance sourceHasFiniteBiproducts : HasFiniteBiproducts SourceCategory.{u} :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Looping preserves the actual additive structure. -/
instance sourceLoopFunctor_additive : sourceLoopFunctor.{u}.Additive := by
  letI := sourceSuspensionLoopAdjunction.isRightAdjoint
  exact Functor.additive_of_preserves_binary_products sourceLoopFunctor

instance sourceSuspensionFunctor_additive : sourceSuspensionFunctor.{u}.Additive := by
  letI : sourceSuspensionFunctor.{u}.IsEquivalence :=
    inferInstanceAs (sourceSuspensionEquivalence.functor.IsEquivalence)
  exact Functor.additive_of_preserves_binary_products sourceSuspensionFunctor

instance sourceDesuspensionFunctor_additive : sourceDesuspensionFunctor.{u}.Additive := by
  letI : sourceDesuspensionFunctor.{u}.IsEquivalence :=
    inferInstanceAs (sourceSuspensionEquivalence.inverse.IsEquivalence)
  exact Functor.additive_of_preserves_binary_products sourceDesuspensionFunctor

end KIP126.StableHomotopy.Implementation.Prespectrum

end
