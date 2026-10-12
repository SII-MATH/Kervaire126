module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Square.Data
public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Comparison.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial MonoidalCategory
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- A cylinder lift of a time-independent evaluated map is exactly its
realized adjoint at every parameter value. -/
theorem singularCylinder_timeIndependent (K : SSet.{u}) (B : TopCat.{u})
    (f : C(|K|,B)) (x : |K|) (t : I) :
    singularCylinder K B (f.comp ContinuousMap.fst) (x,t) =
      SSet.toTop.map (sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B) f)) x := by
  have h : singularCylinderAdjoint K B (f.comp ContinuousMap.fst) =
      CartesianMonoidalCategory.fst K Δ[1] ≫
        sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B) f) := by
    rw [← sSetTopAdj.homEquiv_naturality_left]
    rfl
  change SSet.toTop.map (singularCylinderAdjoint K B (f.comp ContinuousMap.fst))
    ((realizationCylinderHomeomorph K).symm (x,t)) = _
  rw [h,Functor.map_comp,TopCat.comp_app]
  apply congrArg (SSet.toTop.map _)
  exact congrArg Prod.fst ((realizationCylinderHomeomorph K).apply_symm_apply (x,t))

/-- The actual two-parameter lift evaluates to the original square at
every point, not just on its boundary or up to homotopy. -/
theorem singularSquare_evaluation (K : SSet.{u}) (B : TopCat.{u})
    (F : C((|K| × I) × I,B)) (z : (|K| × I) × I) :
    sSetTopAdj.counit.app B (singularSquare K B F z) = F z := by
  change sSetTopAdj.counit.app B (singularCylinder (K ⊗ Δ[1]) B _
    ((realizationCylinderHomeomorph K).symm z.1,z.2)) = _
  rw [singularCylinder_evaluation]
  change F (realizationCylinderHomeomorph K
    ((realizationCylinderHomeomorph K).symm z.1),z.2) = _
  rw [Homeomorph.apply_symm_apply]

/-- Both outer edges are exactly the one-parameter lifts of the original
edge maps. This retains all parameters along both edges simultaneously. -/
theorem singularSquare_outerEndpoint (K : SSet.{u}) (B : TopCat.{u})
    (F : C((|K| × I) × I,B)) (i : Fin 2) (z : |K| × I) :
    singularSquare K B F (z,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) =
      singularCylinder K B
        (F.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _
          (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i))))) z := by
  change singularCylinder (K ⊗ Δ[1]) B _
    ((realizationCylinderHomeomorph K).symm z,
      stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) = _
  rw [singularCylinder_endpoint]
  rfl

/-- Both inner edges are also exactly the original one-parameter lifts;
thus the square has four strictly compatible boundary maps. -/
theorem singularSquare_innerEndpoint (K : SSet.{u}) (B : TopCat.{u})
    (F : C((|K| × I) × I,B)) (i : Fin 2) (x : |K|) (t : I) :
    singularSquare K B F
      ((x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)),t) =
      singularCylinder K B
        (F.comp (((ContinuousMap.id _).prodMk (ContinuousMap.const _
          (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)))).prodMap
            (ContinuousMap.id I))) (x,t) := by
  have he : (realizationCylinderHomeomorph K).symm
      (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) =
      SSet.toTop.map (realizationCylinderEnd K i) x := by
    apply (realizationCylinderHomeomorph K).injective
    rw [Homeomorph.apply_symm_apply,realizationCylinderHomeomorph_end]
  change singularCylinder (K ⊗ Δ[1]) B _
    ((realizationCylinderHomeomorph K).symm
      (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)),t) = _
  rw [he,singularCylinder_precomp]
  apply congrArg (fun h : C(|K| × I,B) => singularCylinder K B h (x,t))
  apply ContinuousMap.ext
  intro z
  change F (realizationCylinderHomeomorph K
    (SSet.toTop.map (realizationCylinderEnd K i) z.1),z.2) = _
  rw [realizationCylinderHomeomorph_end]
  rfl

/-- A homotopy of evaluated cylinder maps relative to both endpoints
lifts to a homotopy relative to both whole endpoint slices, and every
value of the prescribed evaluated two-parameter homotopy is retained. -/
theorem singularCylinder_lift_homotopyRel_endpoints
    (K : SSet.{u}) (B : TopCat.{u}) (f g : C(|K| × I,B))
    (H : f.HomotopyRel g {z | z.2 = 0 ∨ z.2 = 1}) :
    ∃ H' : (singularCylinder K B f).HomotopyRel (singularCylinder K B g)
      {z | z.2 = 0 ∨ z.2 = 1},
      ∀ z, sSetTopAdj.counit.app B (H' z) = H z := by
  let F : C((|K| × I) × I,B) :=
    H.toHomotopy.toContinuousMap.comp ContinuousMap.prodSwap
  have hside (i : Fin 2)
      (hi : stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i) = 0 ∨
        stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i) = 1)
      (x : |K|) (t : I) :
      singularSquare K B F
        ((x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)),t) =
      singularCylinder K B f
        (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) := by
    rw [singularSquare_innerEndpoint]
    have he : F.comp
        (((ContinuousMap.id _).prodMk (ContinuousMap.const _
          (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)))).prodMap
            (ContinuousMap.id I)) =
        (f.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _
          (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i))))).comp
            ContinuousMap.fst := by
      apply ContinuousMap.ext
      intro z
      exact H.eq_fst z.2 hi
    rw [he,singularCylinder_timeIndependent,singularCylinder_endpoint]
  let H' : (singularCylinder K B f).HomotopyRel (singularCylinder K B g)
      {z | z.2 = 0 ∨ z.2 = 1} := {
    toFun := fun z => singularSquare K B F (z.2,z.1)
    continuous_toFun := (singularSquare K B F).continuous.comp
      (continuous_snd.prodMk continuous_fst)
    map_zero_left := by
      intro z
      change singularSquare K B F
        (z,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex (0 : Fin 2))) = _
      rw [singularSquare_outerEndpoint]
      apply congrArg (fun h : C(|K| × I,B) => singularCylinder K B h z)
      apply ContinuousMap.ext
      exact H.apply_zero
    map_one_left := by
      intro z
      change singularSquare K B F
        (z,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex (1 : Fin 2))) = _
      rw [singularSquare_outerEndpoint]
      apply congrArg (fun h : C(|K| × I,B) => singularCylinder K B h z)
      apply ContinuousMap.ext
      exact H.apply_one
    prop' := by
      rintro t ⟨x,s⟩ (hs | hs)
      · change s = 0 at hs
        subst s
        exact hside 0 (Or.inl rfl) x t
      · change s = 1 at hs
        subst s
        exact hside 1 (Or.inr rfl) x t }
  refine ⟨H',?_⟩
  intro z
  exact singularSquare_evaluation K B F (z.2,z.1)

end KIP126.StableHomotopy.Implementation
