module

public import KIP126.Def.Topology.FiberBundle.Fiberwise.Data
public import KIP126.Def.Topology.Ball.Collar.Proofs

@[expose] public section

namespace KIP126.Topology

universe u v w z

variable {A : Type u} {B : Type v} {F : Type w} {G : Type z}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace G]

@[simp] theorem fiberwiseHomeomorphPullback_fst
    (e : (B × F) ≃ₜ (B × G)) (he : ∀ x, (e x).1 = x.1) (f : C(A,B)) (x : A × F) :
    (fiberwiseHomeomorphPullback e he f x).1 = x.1 := rfl

@[simp] theorem fiberwiseHomeomorphPullback_symm_fst
    (e : (B × F) ≃ₜ (B × G)) (he : ∀ x, (e x).1 = x.1) (f : C(A,B)) (x : A × G) :
    ((fiberwiseHomeomorphPullback e he f).symm x).1 = x.1 := rfl

/-- A genuine continuous family of boundary transition homeomorphisms
extends over the open radial collar, agreeing exactly on the boundary. -/
theorem exists_collar_transition_extension
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : (Metric.sphere (0 : E) 1 × F) ≃ₜ (Metric.sphere (0 : E) 1 × G))
    (he : ∀ x, (e x).1 = x.1) :
    ∃ e' : (Ball.unitDiskCollar E × F) ≃ₜ (Ball.unitDiskCollar E × G),
      (∀ x, (e' x).1 = x.1) ∧
      (∀ (s : Metric.sphere (0 : E) 1) (v : F),
        (e' (⟨Ball.unitDiskBoundary E s,Ball.unitDiskBoundary_mem_collar s⟩,v)).2 = (e (s,v)).2) ∧
      (∀ (s : Metric.sphere (0 : E) 1) (v : G),
        (e'.symm (⟨Ball.unitDiskBoundary E s,Ball.unitDiskBoundary_mem_collar s⟩,v)).2 = (e.symm (s,v)).2) := by
  refine ⟨fiberwiseHomeomorphPullback e he (Ball.unitDiskCollarProjection E),
    fun _ => rfl,?_,?_⟩
  · intro s v
    change (e (Ball.unitDiskCollarProjection E _,v)).2 = _
    rw [Ball.unitDiskCollarProjection_boundary]
  · intro s v
    change (e.symm (Ball.unitDiskCollarProjection E _,v)).2 = _
    rw [Ball.unitDiskCollarProjection_boundary]

end KIP126.Topology
