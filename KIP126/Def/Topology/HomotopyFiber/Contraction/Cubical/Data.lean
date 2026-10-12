module

public import KIP126.Def.Topology.HomotopyFiber.Contraction.Proofs

@[expose] public section

namespace KIP126.Topology

universe u v
variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- The cubical based map induced by the actual fiber-to-loop comparison. -/
def contractionFiberGenLoop (f : C(E,B)) (e : E)
    (c : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (hc : ∀ t, c (t,e) = e) (n : ℕ)
    (p : GenLoop (Fin n) {x : E // f x = f e} ⟨e,rfl⟩) :
    GenLoop (Fin n) (Path (f e) (f e)) (Path.refl (f e)) :=
  ⟨(contractionFiberLoop f e c).comp p.val,fun z hz =>
    (congrArg (contractionFiberLoop f e c) (p.property z hz)).trans
      (contractionFiberLoop_point f e c hc)⟩

/-- The induced map on the actual cubical homotopy quotient. -/
def contractionFiberHomotopyMap (f : C(E,B)) (e : E)
    (c : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (hc : ∀ t, c (t,e) = e) (n : ℕ) :
    HomotopyGroup.Pi n {x : E // f x = f e} ⟨e,rfl⟩ →
      HomotopyGroup.Pi n (Path (f e) (f e)) (Path.refl (f e)) :=
  Quotient.map (contractionFiberGenLoop f e c hc n) fun _ _ h =>
    h.comp_continuousMap (contractionFiberLoop f e c)

end KIP126.Topology
