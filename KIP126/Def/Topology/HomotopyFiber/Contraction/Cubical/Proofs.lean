module

public import KIP126.Def.Topology.HomotopyFiber.Contraction.Cubical.Data

@[expose] public section

namespace KIP126.Topology

open HomotopyLifting
universe u v
variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- A cubical fibration with a strongly contractible total space has the
actual fiber homotopy groups of the based loop space. The map is the
projection of the specified contraction, in every dimension including zero. -/
theorem contractionFiberHomotopyMap_bijective (f : C(E,B)) (e : E)
    (c : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (hc : ∀ t, c (t,e) = e) (hf : HasCubicalLifting f) (n : ℕ) :
    Function.Bijective (contractionFiberHomotopyMap f e c hc n) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with
    | h p =>
      induction q using Quotient.inductionOn with
      | h q =>
        intro hpq
        apply Quotient.sound
        exact contractionFiberLoop_homotopy_injective f e c hc _ (hf.cylinder n)
          p.val q.val p.property q.property (Quotient.exact hpq)
  · intro q
    induction q using Quotient.inductionOn with
    | h q =>
      obtain ⟨α,hα,hH⟩ := contractionFiberLoop_homotopy_surjective f e c hc _ (hf n)
        q.val q.property
      refine ⟨Quotient.mk'' ⟨α,hα⟩,Quotient.sound ?_⟩
      exact hH.symm

end KIP126.Topology
