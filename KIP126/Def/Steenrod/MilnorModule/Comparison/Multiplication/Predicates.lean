import KIP126.Def.Steenrod.MilnorModule.Comparison.Predicates
import KIP126.Def.Steenrod.MilnorModule.Multiplication.Data
import KIP126.Def.Steenrod.MilnorExt.Multiplication.Data

/-!
# Multiplicativity of the fixed-degree right-to-left Ext comparison

Both Yoneda operations are actual derived compositions using their specified
internal shifts.  The property below concerns the same supplied comparison
family in every bidegree; it chooses neither that family nor a product.
-/

namespace KIP126.Steenrod.Milnor.Module

open KIP126.Core.Algebra

/-- The same-degree comparison carries the actual right-comodule Yoneda
product to the actual left-module Yoneda product.  Contravariance reverses
the composition arrows, already reflected by the two product definitions;
the named factors and their integer internal degrees remain unchanged. -/
def PreservesYoneda
    (e : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t) : Prop :=
  ∀ (s s' : ℕ) (t t' : ℤ) (x : Ext.SphereExt s t) (y : Ext.SphereExt s' t'),
    e (s + s') (t + t') (Ext.yoneda x y) = yoneda (e s t x) (e s' t' y)

/-- The actual identity class is preserved in cohomological and internal
degree zero.  No separately selected unit appears in this condition. -/
def PreservesUnit
    (e : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t) : Prop :=
  e 0 0 Ext.unit = unit

end KIP126.Steenrod.Milnor.Module
