module

public import KIP126.Def.Topology.HomotopyGroup.Relative.Transport.Proofs

@[expose] public section

namespace KIP126.Topology
open HomotopyLifting
open scoped unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false

/-- The actual path of boundary maps traced by a cube homotopy. -/
def cubeBoundaryPath {Y : Type u} [TopologicalSpace Y] {n : ℕ}
    {p q : C(Fin n → I,Y)} (H : p.Homotopy q) :
    Path (p.restrict (_root_.Cube.boundary (Fin n)))
      (q.restrict (_root_.Cube.boundary (Fin n))) := by
  let K : C(I × ↥(_root_.Cube.boundary (Fin n)),Y) :=
    ⟨fun z => H (z.1,z.2.val),H.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  exact {
    toContinuousMap := K.curry
    source' := by ext x; exact H.apply_zero x.val
    target' := by ext x; exact H.apply_one x.val }

/-- A cube map contracts to its value at the zero corner by actual
coordinatewise multiplication in the unit interval. -/
def cubeMapContraction {Y : Type u} [TopologicalSpace Y] {n : ℕ}
    (p : C(Fin n → I,Y)) : p.Homotopy (ContinuousMap.const _ (p (fun _ => 0))) where
  toFun z := p (fun i => unitInterval.symm z.1 * z.2 i)
  continuous_toFun := p.continuous.comp (continuous_pi (fun i =>
    (unitInterval.continuous_symm.comp continuous_fst).mul
      ((continuous_apply i).comp continuous_snd)))
  map_zero_left x := by simp
  map_one_left x := by simp

/-- Postcomposition acts continuously on the actual boundary-map space. -/
def cubeBoundaryPostcompose {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X,Y)) (n : ℕ) :
    C(C(↥(_root_.Cube.boundary (Fin n)),X),C(↥(_root_.Cube.boundary (Fin n)),Y)) :=
  ⟨fun a => f.comp a,ContinuousMap.continuous_postcomp f⟩

end KIP126.Topology
