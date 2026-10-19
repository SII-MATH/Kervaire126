module

public import KIP126.Def.Topology.HomotopyGroup.Basepoint.Equivalence.Data
public import KIP126.Def.Topology.HomotopyGroup.ContinuousMap.Data

@[expose] public section

namespace KIP126.Topology
open scoped unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false

theorem homotopyBasepointEquiv_apply_eq {Y : Type u} [TopologicalSpace Y]
    {a b : Y} {γ : Path a b} {n : ℕ}
    {p : GenLoop (Fin n) Y a} {q : GenLoop (Fin n) Y b}
    (h : GenLoopTransport γ p q) : homotopyBasepointEquiv γ n ⟦p⟧ = ⟦q⟧ :=
  Quotient.sound ((exists_genLoopTransport γ p).choose_spec.unique h)

/-- Postcomposition preserves the specified moving-boundary homotopy. -/
theorem GenLoopTransport.map {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) {a b : X} {γ : Path a b} {n : ℕ}
    {p : GenLoop (Fin n) X a} {q : GenLoop (Fin n) X b} (h : GenLoopTransport γ p q) :
    GenLoopTransport (γ.map f.continuous)
      (continuousGenLoopMap f a (f a) rfl n p) (continuousGenLoopMap f b (f b) rfl n q) := by
  obtain ⟨H,hH⟩ := h
  refine ⟨{
    toContinuousMap := f.comp H.toContinuousMap
    map_zero_left := fun x => congrArg f (H.apply_zero x)
    map_one_left := fun x => congrArg f (H.apply_one x) },?_⟩
  intro t x hx
  exact congrArg f (hH t x hx)

/-- Change of basepoint is natural for actual continuous maps. -/
theorem continuousHomotopyMap_basepoint_natural
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) {a b : X} (γ : Path a b) (n : ℕ) (z : HomotopyGroup.Pi n X a) :
    continuousHomotopyMap f b (f b) rfl n (homotopyBasepointEquiv γ n z) =
      homotopyBasepointEquiv (γ.map f.continuous) n (continuousHomotopyMap f a (f a) rfl n z) := by
  induction z using Quotient.inductionOn with
  | h p =>
    exact (homotopyBasepointEquiv_apply_eq ((exists_genLoopTransport γ p).choose_spec.map f)).symm

/-- A genuine homotopy intertwines the two induced maps through the
actual path traced by the chosen basepoint. -/
theorem continuousHomotopyMap_homotopy {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X,Y)}
    (H : f.Homotopy g) (x : X) (n : ℕ) (z : HomotopyGroup.Pi n X x) :
    homotopyBasepointEquiv (homotopyPointPath H x) n (continuousHomotopyMap f x (f x) rfl n z) =
      continuousHomotopyMap g x (g x) rfl n z := by
  induction z using Quotient.inductionOn with
  | h p =>
    apply homotopyBasepointEquiv_apply_eq
    refine ⟨{
      toContinuousMap := H.toContinuousMap.comp
        ⟨fun z => (z.1,p z.2),continuous_fst.prodMk (p.val.continuous.comp continuous_snd)⟩
      map_zero_left := fun z => H.apply_zero (p z)
      map_one_left := fun z => H.apply_one (p z) },?_⟩
    intro t z hz
    exact congrArg (fun w => H (t,w)) (p.property z hz)

end KIP126.Topology
