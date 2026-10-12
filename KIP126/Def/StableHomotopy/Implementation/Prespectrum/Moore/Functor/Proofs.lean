module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Functor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

instance sourceMooreCompletionFunctor_additive (p : ℕ) :
    (sourceMooreCompletionFunctor.{u} p).Additive where
  map_add := fun {X Y f g} => sourceMooreCompletionMap_add p f g

end KIP126.StableHomotopy.Implementation
