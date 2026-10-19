module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Cylinder.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial MonoidalCategory

universe u

/-- The actual realization product with a simplex, expressed in its
ordinary barycentric coordinates. -/
noncomputable def realizationSimplexPrismHomeomorph (K : SSet.{u}) (n : ℕ) :
    |K ⊗ Δ[n]| ≃ₜ (|K| × stdSimplex ℝ (Fin (n+1))) :=
  (KIP126.Topology.SimplicialRealization.realizationStandardSimplexProductHomeomorph K n).trans
    ((Homeomorph.refl _).prodCongr (SimplexCategory.toTopHomeo ⦋n⦌))

/-- The actual singular adjoint of a continuously parameterized simplex. -/
noncomputable def singularPrismAdjoint (K : SSet.{u}) (B : TopCat.{u}) (n : ℕ)
    (f : C(|K| × stdSimplex ℝ (Fin (n+1)),B)) : K ⊗ Δ[n] ⟶ TopCat.toSSet.obj B :=
  sSetTopAdj.homEquiv _ _ (TopCat.ofHom (Y := B)
    (f.comp ⟨realizationSimplexPrismHomeomorph K n,
      (realizationSimplexPrismHomeomorph K n).continuous⟩))

/-- The actual singular lift of a continuously parameterized simplex,
using the same ordinary simplex domain. -/
noncomputable def singularPrism (K : SSet.{u}) (B : TopCat.{u}) (n : ℕ)
    (f : C(|K| × stdSimplex ℝ (Fin (n+1)),B)) :
    C(|K| × stdSimplex ℝ (Fin (n+1)),|TopCat.toSSet.obj B|) :=
  (SSet.toTop.map (singularPrismAdjoint K B n f)).hom.comp
    ⟨(realizationSimplexPrismHomeomorph K n).symm,
      (realizationSimplexPrismHomeomorph K n).symm.continuous⟩

end KIP126.StableHomotopy.Implementation
