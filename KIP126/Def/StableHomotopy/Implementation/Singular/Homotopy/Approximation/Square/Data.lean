module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Cylinder.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial MonoidalCategory
open scoped unitInterval

universe u

/-- The actual two-parameter singular lift, using the realized product
with a standard one-simplex twice. -/
noncomputable def singularSquare (K : SSet.{u}) (B : TopCat.{u})
    (F : C((|K| × I) × I,B)) : C((|K| × I) × I,|TopCat.toSSet.obj B|) :=
  (singularCylinder (K ⊗ Δ[1]) B
    (F.comp ((⟨realizationCylinderHomeomorph K,
      (realizationCylinderHomeomorph K).continuous⟩ : C(|K ⊗ Δ[1]|,|K| × I)).prodMap
        (ContinuousMap.id I)))).comp
      ((⟨(realizationCylinderHomeomorph K).symm,
        (realizationCylinderHomeomorph K).symm.continuous⟩ : C(|K| × I,|K ⊗ Δ[1]|)).prodMap
          (ContinuousMap.id I))

end KIP126.StableHomotopy.Implementation
