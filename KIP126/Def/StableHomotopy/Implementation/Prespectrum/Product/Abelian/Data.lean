module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Colimit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

universe u

/-- Finite pointwise products commute with the original stable homotopy
groups as abelian groups, by their actual projection maps. -/
noncomputable def stablePiAddEquiv {J : Type} [Finite J]
    (X : J → Prespectrum.{u}) (d : ℤ) :
    StableHomotopy (piPrespectrum X) d ≃+ ∀ j, StableHomotopy (X j) d where
  toEquiv := Equiv.ofBijective (stablePiComparison X d) (stablePiComparison_bijective X d)
  map_add' := stablePiComparison_add X d

end KIP126.StableHomotopy.Implementation.Prespectrum
