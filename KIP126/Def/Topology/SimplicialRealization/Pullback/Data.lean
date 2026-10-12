module

public import KIP126.Def.Topology.SimplicialRealization.Equalizer.Data
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual pullback, as a subcomplex of the simplicial product. -/
def pullbackSubcomplex {X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : (X ⊗ Y).Subcomplex :=
  equalitySubcomplex (CartesianMonoidalCategory.fst X Y ≫ f)
    (CartesianMonoidalCategory.snd X Y ≫ g)


end KIP126.Topology.SimplicialRealization
