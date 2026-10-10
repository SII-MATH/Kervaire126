import KIP126.Def.HigherAlgebra.Operad.Topological.Data

/-!
Algebras over the actual topological operad in Cartesian topological spaces.
The action is a jointly continuous map on the operation space and every
finite tuple of inputs, and all operadic laws are actual equalities of these
actions. This is the space-valued algebra model, not yet an algebra in a
synthetic symmetric monoidal model category; the latter needs its enriched
tensor operations rather than replacing spectra by their underlying spaces.

Reference: May, *The Geometry of Iterated Loop Spaces*, Definition 1.2 and
the equivalent direct action formulation in Lemma 1.4.
-/

namespace KIP126.HigherAlgebra.Operad.TopologicalOperad

universe v w w'

/-- An action of one fixed operad on one fixed topological space. The unit
acts as identity, substitution acts by iterated evaluation, and relabelling
is precisely permutation of the corresponding input variables. Nullary
actions are included. -/
structure Algebra (O : TopologicalOperad.{v}) (X : TopCat.{w}) where
  act : (I : FintypeCat.{0}) → C(O.Op I × (I → X), X)
  unit : ∀ x : X, act Arity.one (O.unit, fun _ => x) = x
  substitution : ∀ (I : FintypeCat.{0}) (J : I → FintypeCat.{0})
    (x : O.Op I) (y : (i : I) → O.Op (J i)) (a : Arity.sum I J → X),
    act (Arity.sum I J) (O.compose I J (x, y), a) =
      act I (x, fun i => act (J i) (y i, fun j => a ⟨i, j⟩))
  equivariance : ∀ {I J : FintypeCat.{0}} (e : I ≃ J)
    (x : O.Op I) (a : J → X),
    act J (O.relabel e x, a) = act I (x, fun i => a (e i))

namespace Algebra

/-- A jointly continuous operad action is preserved on all labelled tuples,
including the empty tuple; no separate freedom in the nullary unit is allowed. -/
structure Hom {O : TopologicalOperad.{v}} {X : TopCat.{w}} {Y : TopCat.{w'}}
    (A : Algebra O X) (B : Algebra O Y) where
  map : C(X, Y)
  map_act : ∀ (I : FintypeCat.{0}) (x : O.Op I) (a : I → X),
    map (A.act I (x, a)) = B.act I (x, fun i => map (a i))

end Algebra

/-- Bundling the carrier with its actual operadic action allows later
construction of the algebra category and its weak-equivalence subcategory. -/
structure BundledAlgebra (O : TopologicalOperad.{v}) where
  carrier : TopCat.{w}
  algebra : Algebra O carrier

end KIP126.HigherAlgebra.Operad.TopologicalOperad
