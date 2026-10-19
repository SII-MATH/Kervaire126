module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Cylinder.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual cylinder lift, bundled as a homotopy between the realized
adjoints of its two endpoint maps. -/
noncomputable def singularHomotopyLift (K : SSet.{u}) (B : TopCat.{u})
    {a b : C(|K|,B)} (H : a.Homotopy b) :
    (SSet.toTop.map (sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B) a))).hom.Homotopy
      (SSet.toTop.map (sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B) b))).hom where
  toFun z := singularCylinder K B
    (H.toContinuousMap.comp ContinuousMap.prodSwap) (z.2,z.1)
  continuous_toFun := (singularCylinder K B _).continuous.comp
    (continuous_snd.prodMk continuous_fst)
  map_zero_left x := by
    change singularCylinder K B _
      (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex (0 : Fin 2))) = _
    rw [singularCylinder_endpoint]
    apply congrArg (fun f : C(|K|,B) =>
      SSet.toTop.map (sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B) f)) x)
    apply ContinuousMap.ext
    exact H.apply_zero
  map_one_left x := by
    change singularCylinder K B _
      (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex (1 : Fin 2))) = _
    rw [singularCylinder_endpoint]
    apply congrArg (fun f : C(|K|,B) =>
      SSet.toTop.map (sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B) f)) x)
    apply ContinuousMap.ext
    exact H.apply_one

end KIP126.StableHomotopy.Implementation
