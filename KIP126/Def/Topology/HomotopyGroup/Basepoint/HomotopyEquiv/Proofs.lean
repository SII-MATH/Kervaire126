module

public import KIP126.Def.Topology.HomotopyGroup.Basepoint.Equivalence.Proofs
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

namespace KIP126.Topology
open scoped unitInterval
universe u v w
set_option backward.isDefEq.respectTransparency false

theorem continuousHomotopyMap_comp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X,Y)) (g : C(Y,Z)) (x : X) (n : ℕ) (z : HomotopyGroup.Pi n X x) :
    continuousHomotopyMap (g.comp f) x (g (f x)) rfl n z =
      continuousHomotopyMap g (f x) (g (f x)) rfl n
        (continuousHomotopyMap f x (f x) rfl n z) := by
  induction z using Quotient.inductionOn with
  | h p => rfl

@[simp] theorem continuousHomotopyMap_id {X : Type u} [TopologicalSpace X]
    (x : X) (n : ℕ) (z : HomotopyGroup.Pi n X x) :
    continuousHomotopyMap (ContinuousMap.id X) x x rfl n z = z := by
  induction z using Quotient.inductionOn with
  | h p => rfl

/-- A genuine homotopy equivalence induces a bijection on every cubical
homotopy group at every chosen point. Its inverse homotopies need not fix
that point: their actual point paths supply the required transport. -/
theorem homotopyEquiv_continuousHomotopyMap_bijective
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) (n : ℕ) :
    Function.Bijective (continuousHomotopyMap e.toFun x (e x) rfl n) := by
  obtain ⟨L⟩ := e.left_inv
  obtain ⟨R⟩ := e.right_inv
  let γ : Path (e.invFun (e x)) x := homotopyPointPath L x
  let δ : Path (e (e.invFun (e x))) (e x) := homotopyPointPath R (e x)
  have hl (z : HomotopyGroup.Pi n X x) :
      homotopyBasepointEquiv γ n
        (continuousHomotopyMap e.invFun (e x) (e.invFun (e x)) rfl n
          (continuousHomotopyMap e.toFun x (e x) rfl n z)) = z := by
    have hh := continuousHomotopyMap_homotopy L x n z
    change homotopyBasepointEquiv γ n
      (continuousHomotopyMap (e.invFun.comp e.toFun) x (e.invFun (e x)) rfl n z) =
        continuousHomotopyMap (ContinuousMap.id X) x x rfl n z at hh
    rw [continuousHomotopyMap_comp,continuousHomotopyMap_id] at hh
    exact hh
  have hr (z : HomotopyGroup.Pi n Y (e x)) :
      homotopyBasepointEquiv δ n
        (continuousHomotopyMap e.toFun (e.invFun (e x)) (e (e.invFun (e x))) rfl n
          (continuousHomotopyMap e.invFun (e x) (e.invFun (e x)) rfl n z)) = z := by
    have hh := continuousHomotopyMap_homotopy R (e x) n z
    change homotopyBasepointEquiv δ n
      (continuousHomotopyMap (e.toFun.comp e.invFun) (e x) (e (e.invFun (e x))) rfl n z) =
        continuousHomotopyMap (ContinuousMap.id Y) (e x) (e x) rfl n z at hh
    rw [continuousHomotopyMap_comp,continuousHomotopyMap_id] at hh
    exact hh
  constructor
  · intro p q hpq
    exact (hl p).symm.trans ((congrArg (fun z => homotopyBasepointEquiv γ n
      (continuousHomotopyMap e.invFun (e x) (e.invFun (e x)) rfl n z)) hpq).trans (hl q))
  · intro z
    let z' := (homotopyBasepointEquiv (γ.map e.continuous) n).symm z
    let w := homotopyBasepointEquiv δ n z'
    let p := continuousHomotopyMap e.invFun (e x) (e.invFun (e x)) rfl n w
    have hp : continuousHomotopyMap e.toFun (e.invFun (e x)) (e (e.invFun (e x))) rfl n p = z' :=
      (homotopyBasepointEquiv δ n).injective (hr w)
    refine ⟨homotopyBasepointEquiv γ n p,?_⟩
    rw [continuousHomotopyMap_basepoint_natural e.toFun γ n p,hp]
    exact (homotopyBasepointEquiv (γ.map e.continuous) n).apply_symm_apply z

/-- Bijectivity propagates along any actual path of source basepoints. -/
theorem continuousHomotopyMap_bijective_of_path
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) {a b : X} (γ : Path a b) (n : ℕ)
    (ha : Function.Bijective (continuousHomotopyMap f a (f a) rfl n)) :
    Function.Bijective (continuousHomotopyMap f b (f b) rfl n) := by
  let ea := homotopyBasepointEquiv γ n
  let eb := homotopyBasepointEquiv (γ.map f.continuous) n
  have h (z : HomotopyGroup.Pi n X b) :
      continuousHomotopyMap f b (f b) rfl n z =
        eb (continuousHomotopyMap f a (f a) rfl n (ea.symm z)) := by
    simpa only [ea,Equiv.apply_symm_apply] using
      continuousHomotopyMap_basepoint_natural f γ n (ea.symm z)
  have he : continuousHomotopyMap f b (f b) rfl n =
      eb ∘ continuousHomotopyMap f a (f a) rfl n ∘ ea.symm := funext h
  rw [he]
  exact eb.bijective.comp (ha.comp ea.symm.bijective)

end KIP126.Topology
