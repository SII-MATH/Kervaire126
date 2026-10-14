module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Zero.Data
public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Singular.Cylinder.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Topology Simplicial Opposite
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem singularEvaluation_vertex (A : BasedSpace.{u}) (a : A) :
    singularEvaluation A (singularVertex A a) = a :=
  singularEvaluation_point { A with point := a }

/-- A path in the original space gives a path between its actual singular
vertices. -/
theorem singularVertex_joined {A : BasedSpace.{u}} {a b : A} (h : Joined a b) :
    Joined (singularVertex A a) (singularVertex A b) := by
  obtain ⟨p⟩ := h
  let H := singularCylinder (Δ[0] : SSet.{u}) A.space
    (p.toContinuousMap.comp ContinuousMap.snd)
  have he (i : Fin 2) :
      H (default,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) =
        singularVertex A (p (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i))) := by
    rw [singularCylinder_endpoint]
    have hc : TopCat.ofHom (X := SSet.toTop.obj (Δ[0] : SSet.{u})) (Y := A.space)
        ((p.toContinuousMap.comp ContinuousMap.snd).comp
          ((ContinuousMap.id _).prodMk (ContinuousMap.const _
            (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i))))) =
        TopCat.const (p (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i))) := rfl
    rw [hc]
    simp only [Adjunction.homEquiv_unit, TopCat.toSSet_map_const, SSet.comp_const]
    exact realization_const_apply _ _
  refine ⟨{
    toFun := fun t => H (default,t)
    continuous_toFun := H.continuous.comp (continuous_const.prodMk continuous_id)
    source' := ?_
    target' := ?_ }⟩
  · exact (he 0).trans (congrArg (singularVertex A) p.source)
  · exact (he 1).trans (congrArg (singularVertex A) p.target)

/-- Every point in singular realization can be joined to an actual
singular vertex, using a simplex containing that point. -/
theorem exists_joined_singularVertex (A : BasedSpace.{u}) (z : singularRealization A) :
    ∃ a : A, Joined z (singularVertex A a) := by
  obtain ⟨s,t,ht⟩ := KIP126.Topology.SimplicialRealization.exists_nondegenerate_simplex
    (TopCat.toSSet.obj A.space) z
  let f : (Δ[s.dim] : SSet.{u}) ⟶ TopCat.toSSet.obj A.space := SSet.yonedaEquiv.symm s.simplex
  let v := SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (s.dim+1))
  let i : (Δ[0] : SSet.{u}) ⟶ Δ[s.dim] := SSet.const v
  let a := TopCat.toSSetObj₀Equiv (f.app (op ⦋0⦌) v)
  have hi : SSet.toTop.map f (SSet.toTop.map i default) = singularVertex A a := by
    rw [← TopCat.comp_app, ← Functor.map_comp, SSet.const_comp]
    rw [realization_const_apply]
    dsimp only [singularVertex,a]
    rw [Equiv.symm_apply_apply]
  letI : PathConnectedSpace |(Δ[s.dim] : SSet.{u})| :=
    (SimplexCategory.toTopHomeo ⦋s.dim⦌).symm.surjective.pathConnectedSpace
      (SimplexCategory.toTopHomeo ⦋s.dim⦌).symm.continuous
  have hp : Joined (SSet.toTop.map f t) (SSet.toTop.map f (SSet.toTop.map i default)) :=
    ⟨(PathConnectedSpace.joined t (SSet.toTop.map i default)).somePath.map
      (SSet.toTop.map f).hom.continuous⟩
  exact ⟨a, by simpa only [f,ht,hi] using hp⟩

/-- The actual singular counit reflects path components, with no
local-connectivity or separation assumption on the original space. -/
theorem singularEvaluation_joined_iff (A : BasedSpace.{u})
    (x y : singularRealization A) :
    Joined (singularEvaluation A x) (singularEvaluation A y) ↔ Joined x y := by
  constructor
  · intro h
    obtain ⟨a,ha⟩ := exists_joined_singularVertex A x
    obtain ⟨b,hb⟩ := exists_joined_singularVertex A y
    have hxa : Joined (singularEvaluation A x) a := by
      simpa only [singularEvaluation_vertex] using
        (show Joined (singularEvaluation A x) (singularEvaluation A (singularVertex A a)) from
          ⟨ha.somePath.map (singularEvaluation A).continuous⟩)
    have hyb : Joined (singularEvaluation A y) b := by
      simpa only [singularEvaluation_vertex] using
        (show Joined (singularEvaluation A y) (singularEvaluation A (singularVertex A b)) from
          ⟨hb.somePath.map (singularEvaluation A).continuous⟩)
    exact ha.trans ((singularVertex_joined (hxa.symm.trans (h.trans hyb))).trans hb.symm)
  · intro h
    exact ⟨h.somePath.map (singularEvaluation A).continuous⟩

/-- Singular evaluation is injective on the original zeroth cubical
homotopy quotient. -/
theorem singularEvaluationHomotopy_zero_injective (A : BasedSpace.{u}) :
    Function.Injective (singularEvaluationHomotopy A 0) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      obtain ⟨H⟩ := Quotient.exact h
      have hj : Joined (singularEvaluation A (p 0)) (singularEvaluation A (q 0)) :=
        ⟨{
          toFun := fun t => H (t,0)
          continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
          source' := H.apply_zero 0
          target' := H.apply_one 0 }⟩
      obtain ⟨P⟩ := (singularEvaluation_joined_iff A (p 0) (q 0)).mp hj
      apply Quotient.sound
      refine ⟨{
        toFun := fun z => P z.1
        continuous_toFun := P.continuous.comp continuous_fst
        map_zero_left := ?_
        map_one_left := ?_
        prop' := ?_ }⟩
      · intro z
        exact P.source.trans (congrArg p (Subsingleton.elim _ _))
      · intro z
        exact P.target.trans (congrArg q (Subsingleton.elim _ _))
      · rintro t z ⟨i,_⟩
        exact Fin.elim0 i

/-- Singular evaluation induces a bijection on actual path components. -/
theorem singularEvaluationHomotopy_zero_bijective (A : BasedSpace.{u}) :
    Function.Bijective (singularEvaluationHomotopy A 0) :=
  ⟨singularEvaluationHomotopy_zero_injective A, singularEvaluationHomotopy_surjective A 0⟩

end KIP126.StableHomotopy.Implementation
