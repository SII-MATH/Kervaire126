module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Limit.Instances
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Derived.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory CategoryTheory.Limits

/-- The actual HF₂-local category has arbitrary small products, obtained
from the constructed source products and proved closure under limits. -/
instance (priority := 100) hasSmallProductsOfShape (J : Type) :
    HasProductsOfShape J CompletedSpectrum :=
  hasLimitsOfShape_of_source (Discrete J)

/-- Inclusion preserves these actual products. -/
instance toSource_preservesSmallProducts (J : Type) :
    PreservesLimitsOfShape (Discrete J) toSource := inferInstance

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
