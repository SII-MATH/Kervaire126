module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- The actual Postnikov truncation functor on the original source category,
with the previously constructed objects and universal-property maps. -/
noncomputable def sourcePostnikovFunctor (n : ℤ) : SourceCategory.{0} ⥤ SourceCategory.{0} where
  obj X := sourcePostnikovTruncation X n
  map f := sourcePostnikovMap n f
  map_id X := sourcePostnikovMap_id n X
  map_comp f g := sourcePostnikovMap_comp n f g

/-- The original stage-zero units form the truncation natural transformation. -/
noncomputable def sourcePostnikovUnitNat (n : ℤ) : 𝟭 SourceCategory.{0} ⟶ sourcePostnikovFunctor n where
  app X := sourcePostnikovUnit X n
  naturality _ _ f := (sourcePostnikovUnit_naturality n f).symm

end KIP126.StableHomotopy.Implementation
