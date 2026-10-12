module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Functor.Map

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The actual scalar Moore completion on the original source category.
Its object assignment is the previously constructed Milnor limit. -/
noncomputable def sourceMooreCompletionFunctor (p : ℕ) : SourceCategory.{u} ⥤ SourceCategory.{u} where
  obj := sourceMooreCompletion p
  map := sourceMooreCompletionMap p
  map_id := sourceMooreCompletionMap_id p
  map_comp := sourceMooreCompletionMap_comp p

/-- The existing compatible-stage Moore units form a natural transformation. -/
noncomputable def sourceMooreCompletionNatUnit (p : ℕ) :
    𝟭 SourceCategory.{u} ⟶ sourceMooreCompletionFunctor p where
  app := sourceMooreCompletionUnit p
  naturality := fun _ _ f => (sourceMooreCompletionMap_unit p f).symm

end KIP126.StableHomotopy.Implementation

end

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

instance sourceMooreCompletionFunctor_additive (p : ℕ) :
    (sourceMooreCompletionFunctor.{u} p).Additive where
  map_add := fun {X Y f g} => sourceMooreCompletionMap_add p f g

end KIP126.StableHomotopy.Implementation

end
