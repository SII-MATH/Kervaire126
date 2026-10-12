module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory Simplicial
universe u

/-- A specified order-realization model of an actual space. -/
structure OrderRealizationModel (X : TopCat.{u}) where
  order : PartOrd.{u}
  equivalence : ContinuousMap.HomotopyEquiv |nerve order| X

/-- A model of the next space, retaining both comparisons with the old
space through the same order embedding. -/
structure OrderRealizationExtension {X Y : TopCat.{u}} (f : X ⟶ Y)
    (M : OrderRealizationModel X) where
  model : OrderRealizationModel Y
  embedding : M.order ↪o model.order
  forward : ∀ x : |nerve M.order|,
    model.equivalence (SSet.toTop.map (nerveMap embedding.monotone.functor) x) =
      f (M.equivalence x)
  backward : ∀ x : X,
    model.equivalence.invFun (f x) =
      SSet.toTop.map (nerveMap embedding.monotone.functor) (M.equivalence.invFun x)

end KIP126.Topology.SimplicialRealization
