module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Map.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory Opposite Simplicial
universe u
set_option backward.isDefEq.respectTransparency false

theorem singularRealizationMap_point {A B : BasedSpace.{u}} (f : A ⟶ B) :
    singularRealizationMap f (singularRealization A).point = (singularRealization B).point := by
  let φ := TopCat.toSSet.map (TopCat.ofHom (X := A.space) (Y := B.space) f.map)
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sSetTopAdj.unit.naturality φ) (op ⦋0⦌))
    (TopCat.toSSetObj₀Equiv.symm A.point)
  have he := congrArg TopCat.toSSetObj₀Equiv h.symm
  have hp : φ.app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm A.point) =
      TopCat.toSSetObj₀Equiv.symm B.point := by
    apply TopCat.toSSetObj₀Equiv.injective
    exact f.point
  change singularRealizationMap f (singularRealization A).point =
    TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app (TopCat.toSSet.obj B.space)).app
      (op ⦋0⦌) (φ.app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm A.point))) at he
  rw [hp] at he
  exact he

theorem singularEvaluation_natural {A B : BasedSpace.{u}} (f : A ⟶ B)
    (x : singularRealization A) :
    singularEvaluation B (singularRealizationMap f x) = f.map (singularEvaluation A x) :=
  ConcreteCategory.congr_hom
    (sSetTopAdj.counit.naturality (TopCat.ofHom (X := A.space) (Y := B.space) f.map)) x

theorem singularRealizationMap_id (A : BasedSpace.{u}) :
    singularRealizationMap (𝟙 A) = ContinuousMap.id _ := by
  change (SSet.toTop.map (TopCat.toSSet.map (𝟙 A.space))).hom = _
  rw [CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_id]
  rfl

theorem singularRealizationMap_comp {A B D : BasedSpace.{u}} (f : A ⟶ B) (g : B ⟶ D) :
    singularRealizationMap (f ≫ g) = (singularRealizationMap g).comp (singularRealizationMap f) := by
  change (SSet.toTop.map (TopCat.toSSet.map
    ((TopCat.ofHom (X := A.space) (Y := B.space) f.map) ≫
      (TopCat.ofHom (X := B.space) (Y := D.space) g.map)))).hom = _
  rw [Functor.map_comp,Functor.map_comp]
  rfl

end KIP126.StableHomotopy.Implementation
