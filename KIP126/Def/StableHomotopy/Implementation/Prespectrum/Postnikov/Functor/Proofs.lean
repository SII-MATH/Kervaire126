module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Functor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- This constructed truncation functor is additive. -/
instance sourcePostnikovFunctor_additive (n : ℤ) : (sourcePostnikovFunctor n).Additive where
  map_add {X Y} f g := sourcePostnikovMap_add n f g

end KIP126.StableHomotopy.Implementation
