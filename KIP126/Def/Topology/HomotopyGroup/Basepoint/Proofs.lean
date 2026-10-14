module

public import KIP126.Def.Topology.HomotopyGroup.Basepoint.Predicates
public import KIP126.Def.Topology.HomotopyGroup.Basepoint.Extension.Proofs
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

@[expose] public section

namespace KIP126.Topology
open HomotopyLifting
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

variable {Y : Type u} [TopologicalSpace Y] {a b c : Y} {n : ℕ}

/-- Transport exists because the actual cube boundary has homotopy extension. -/
theorem exists_genLoopTransport (γ : Path a b) (p : GenLoop (Fin n) Y a) :
    ∃ q : GenLoop (Fin n) Y b, GenLoopTransport γ p q := by
  let v : C(↥(_root_.Cube.boundary (Fin n)) × I,Y) :=
    ⟨fun z => γ z.2,γ.continuous.comp continuous_snd⟩
  obtain ⟨H,hH0,hHb⟩ := cubeBoundary_homotopy_extension n p.val v
    (fun x => γ.source.trans (p.property x.val x.property).symm)
  let q : GenLoop (Fin n) Y b := ⟨H.comp ⟨fun x => (x,1),continuous_id.prodMk continuous_const⟩,
    fun x hx => (hHb ⟨x,hx⟩ 1).trans γ.target⟩
  refine ⟨q,⟨{
    toContinuousMap := H.comp ⟨Prod.swap,continuous_swap⟩
    map_zero_left := hH0
    map_one_left := fun _ => rfl },?_⟩⟩
  intro t x hx
  exact hHb ⟨x,hx⟩ t

/-- Reversing an actual transport reverses its specified basepoint path. -/
theorem GenLoopTransport.symm {γ : Path a b}
    {p : GenLoop (Fin n) Y a} {q : GenLoop (Fin n) Y b}
    (h : GenLoopTransport γ p q) : GenLoopTransport γ.symm q p := by
  obtain ⟨H,hH⟩ := h
  exact ⟨H.symm,fun t x hx => hH (unitInterval.symm t) x hx⟩

/-- Actual concatenation retains the concatenated boundary path exactly. -/
theorem GenLoopTransport.trans {γ : Path a b} {δ : Path b c}
    {p : GenLoop (Fin n) Y a} {q : GenLoop (Fin n) Y b} {r : GenLoop (Fin n) Y c}
    (h : GenLoopTransport γ p q) (k : GenLoopTransport δ q r) :
    GenLoopTransport (γ.trans δ) p r := by
  obtain ⟨H,hH⟩ := h
  obtain ⟨K,hK⟩ := k
  refine ⟨H.trans K,?_⟩
  intro t x hx
  rw [ContinuousMap.Homotopy.trans_apply,Path.trans_apply]
  split_ifs
  · exact hH _ x hx
  · exact hK _ x hx

/-- A homotopy of the basepoint path can be realized while keeping both
endpoint cube maps fixed, using extension on the full cylinder boundary. -/
theorem GenLoopTransport.change_path {γ δ : Path a b}
    {p : GenLoop (Fin n) Y a} {q : GenLoop (Fin n) Y b}
    (h : GenLoopTransport γ p q) (K : γ.Homotopy δ) : GenLoopTransport δ p q := by
  obtain ⟨H,hH⟩ := h
  obtain ⟨F,hF0,hF1,hFs⟩ := exists_cylinderBoundary_path_family n p q K
  have hF : ∀ x, F (x,0) = H.toContinuousMap x.val := by
    rintro ⟨⟨s,x⟩,hs | hs | hx⟩
    · change s = 0 at hs
      subst s
      rw [hF0]
      exact (H.apply_zero x).symm
    · change s = 1 at hs
      subst s
      rw [hF1]
      exact (H.apply_one x).symm
    · rw [hFs 0 s x hx]
      exact (K.apply_zero s).trans (hH s x hx).symm
  obtain ⟨G,hG0,hGb⟩ := cylinderBoundary_homotopy_extension n H.toContinuousMap F hF
  refine ⟨{
    toContinuousMap := G.comp ⟨fun z => (z,1),continuous_id.prodMk continuous_const⟩
    map_zero_left := fun x => (hGb ⟨(0,x),Or.inl rfl⟩ 1).trans (hF0 1 x)
    map_one_left := fun x => (hGb ⟨(1,x),Or.inr (Or.inl rfl)⟩ 1).trans (hF1 1 x) },?_⟩
  intro t x hx
  exact (hGb ⟨(t,x),Or.inr (Or.inr hx)⟩ 1).trans ((hFs 1 t x hx).trans (K.apply_one t))

theorem GenLoopTransport.of_homotopic {p q : GenLoop (Fin n) Y a}
    (h : GenLoop.Homotopic p q) : GenLoopTransport (Path.refl a) p q := by
  obtain ⟨H⟩ := h
  exact ⟨H.toHomotopy,fun t x hx => (H.eq_fst t hx).trans (p.property x hx)⟩

theorem GenLoopTransport.homotopic {p q : GenLoop (Fin n) Y a}
    (h : GenLoopTransport (Path.refl a) p q) : GenLoop.Homotopic p q := by
  obtain ⟨H,hH⟩ := h
  exact ⟨{ toHomotopy := H, prop' := fun t x hx => (hH t x hx).trans (p.property x hx).symm }⟩

/-- Any two actual transports along the same specified path have the
same endpoint cubical homotopy class. -/
theorem GenLoopTransport.unique {γ : Path a b} {p : GenLoop (Fin n) Y a}
    {q r : GenLoop (Fin n) Y b} (h : GenLoopTransport γ p q) (k : GenLoopTransport γ p r) :
    GenLoop.Homotopic q r :=
  ((h.symm.trans k).change_path (Path.Homotopy.reflSymmTrans γ).symm).homotopic

/-- A based homotopy of the input does not change transport of its class. -/
theorem GenLoopTransport.pre_homotopic {γ : Path a b}
    {p p' : GenLoop (Fin n) Y a} {q : GenLoop (Fin n) Y b}
    (h : GenLoop.Homotopic p p') (k : GenLoopTransport γ p' q) : GenLoopTransport γ p q :=
  ((GenLoopTransport.of_homotopic h).trans k).change_path (Path.Homotopy.reflTrans γ)

/-- A based homotopy of the output preserves the same transport relation. -/
theorem GenLoopTransport.post_homotopic {γ : Path a b}
    {p : GenLoop (Fin n) Y a} {q q' : GenLoop (Fin n) Y b}
    (h : GenLoopTransport γ p q) (k : GenLoop.Homotopic q q') : GenLoopTransport γ p q' :=
  (h.trans (GenLoopTransport.of_homotopic k)).change_path (Path.Homotopy.transRefl γ)

end KIP126.Topology
