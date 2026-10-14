module

public import KIP126.Def.Topology.Simplex.Homotopy.Proofs
public import Mathlib.Topology.UnitInterval

@[expose] public section

namespace KIP126.Topology.Simplex

open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- The actual affine homotopy of simplex-valued maps fixes every point
where the two maps already agree. -/
theorem homotopicRel_of_eqOn {X V : Type*} [TopologicalSpace X] [Fintype V]
    (f g : C(X,stdSimplex ℝ V)) (S : Set X) (h : Set.EqOn f g S) :
    f.HomotopicRel g S := by
  obtain ⟨H,hH⟩ := exists_affine_homotopy f g
  refine ⟨⟨H,?_⟩⟩
  intro t x hx
  apply stdSimplex.ext
  funext j
  change H (t,x) j = f x j
  rw [hH,← h hx]
  ring

/-- The simplex cylinder has an actual relative affine homotopy
between any two maps agreeing on the prescribed region. -/
theorem cylinder_homotopicRel_of_eqOn {X V : Type*} [TopologicalSpace X] [Fintype V]
    (f g : C(X,stdSimplex ℝ V × I)) (S : Set X) (h : Set.EqOn f g S) :
    f.HomotopicRel g S := by
  obtain ⟨H,hH⟩ := exists_affine_homotopy (ContinuousMap.fst.comp f) (ContinuousMap.fst.comp g)
  let e := stdSimplexHomeomorphUnitInterval
  let fi : C(X,stdSimplex ℝ (Fin 2)) :=
    (⟨e.symm,e.symm.continuous⟩ : C(I,_)).comp (ContinuousMap.snd.comp f)
  let gi : C(X,stdSimplex ℝ (Fin 2)) :=
    (⟨e.symm,e.symm.continuous⟩ : C(I,_)).comp (ContinuousMap.snd.comp g)
  obtain ⟨J,hJ⟩ := exists_affine_homotopy fi gi
  refine ⟨{
    toFun := fun z => (H z,e (J z))
    continuous_toFun := H.continuous.prodMk (e.continuous.comp J.continuous)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    rw [H.apply_zero,J.apply_zero]
    exact Prod.ext rfl (e.apply_symm_apply _)
  · intro x
    rw [H.apply_one,J.apply_one]
    exact Prod.ext rfl (e.apply_symm_apply _)
  · intro t x hx
    change (H (t,x),e (J (t,x))) = f x
    have h₁ := congrArg Prod.fst (h hx)
    have h₂ := congrArg Prod.snd (h hx)
    apply Prod.ext
    · apply stdSimplex.ext
      funext j
      rw [hH]
      change (1 - (t : ℝ)) * (f x).1 j + (t : ℝ) * (g x).1 j = (f x).1 j
      rw [← h₁]
      ring
    · have he : J (t,x) = e.symm (f x).2 := by
        apply stdSimplex.ext
        funext j
        rw [hJ]
        change (1 - (t : ℝ)) * e.symm (f x).2 j +
          (t : ℝ) * e.symm (g x).2 j = e.symm (f x).2 j
        rw [← h₂]
        ring
      rw [he,e.apply_symm_apply]

end KIP126.Topology.Simplex
