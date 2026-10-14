module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Prism.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Singular.Cylinder.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial MonoidalCategory
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The one-simplex prism lift is exactly the already defined singular
cylinder after the actual interval coordinate homeomorphism. -/
theorem singularPrism_one (K : SSet.{u}) (B : TopCat.{u})
    (f : C(|K| × stdSimplex ℝ (Fin 2),B)) (x : |K|) (t : I) :
    singularPrism K B 1 f (x,stdSimplexHomeomorphUnitInterval.symm t) =
      singularCylinder K B (f.comp ((ContinuousMap.id _).prodMap
        ⟨stdSimplexHomeomorphUnitInterval.symm,
          stdSimplexHomeomorphUnitInterval.symm.continuous⟩)) (x,t) := by
  have h : singularPrismAdjoint K B 1 f = singularCylinderAdjoint K B
      (f.comp ((ContinuousMap.id _).prodMap
        ⟨stdSimplexHomeomorphUnitInterval.symm,
          stdSimplexHomeomorphUnitInterval.symm.continuous⟩)) := by
    apply congrArg (sSetTopAdj.homEquiv _ _)
    apply ConcreteCategory.hom_ext
    intro y
    change f (realizationSimplexPrismHomeomorph K 1 y) =
      f ((realizationCylinderHomeomorph K y).1,
        stdSimplexHomeomorphUnitInterval.symm (realizationCylinderHomeomorph K y).2)
    change f (realizationSimplexPrismHomeomorph K 1 y) =
      f ((realizationSimplexPrismHomeomorph K 1 y).1,
        stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval
          (realizationSimplexPrismHomeomorph K 1 y).2))
    rw [Homeomorph.symm_apply_apply]
  have he : (realizationSimplexPrismHomeomorph K 1).symm
      (x,stdSimplexHomeomorphUnitInterval.symm t) =
      (realizationCylinderHomeomorph K).symm (x,t) := by
    apply (realizationCylinderHomeomorph K).injective
    rw [Homeomorph.apply_symm_apply]
    change ((realizationSimplexPrismHomeomorph K 1
      ((realizationSimplexPrismHomeomorph K 1).symm
        (x,stdSimplexHomeomorphUnitInterval.symm t))).1,
      stdSimplexHomeomorphUnitInterval (realizationSimplexPrismHomeomorph K 1
        ((realizationSimplexPrismHomeomorph K 1).symm
          (x,stdSimplexHomeomorphUnitInterval.symm t))).2) = (x,t)
    rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply]
  change SSet.toTop.map (singularPrismAdjoint K B 1 f)
    ((realizationSimplexPrismHomeomorph K 1).symm
      (x,stdSimplexHomeomorphUnitInterval.symm t)) = _
  rw [h,he]
  rfl

end KIP126.StableHomotopy.Implementation
