module

public import KIP126.Def.Topology.HomotopyGroup.Relative.Transport.Predicates
public import KIP126.Def.Topology.HomotopyGroup.Relative.Transport.Extension.Proofs
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

@[expose] public section

namespace KIP126.Topology
open HomotopyLifting
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

variable {Y : Type u} [TopologicalSpace Y] {n : ℕ}
variable {a b c : C(↥(_root_.Cube.boundary (Fin n)),Y)}
variable {p q r : C(Fin n → I,Y)}

/-- Every actual path of boundary maps extends to a homotopy of disks. -/
theorem exists_cubeBoundaryTransport (γ : Path a b) (p : C(Fin n → I,Y))
    (hp : ∀ x : ↥(_root_.Cube.boundary (Fin n)), p x.val = a x) :
    ∃ q : C(Fin n → I,Y), CubeBoundaryTransport γ p q := by
  letI : CompactSpace (↥(_root_.Cube.boundary (Fin n))) :=
    isCompact_iff_compactSpace.mp (cubeBoundary_isClosed n).isCompact
  let v : C(↥(_root_.Cube.boundary (Fin n)) × I,Y) :=
    ⟨fun z => γ z.2 z.1,(γ.continuous.comp continuous_snd).eval continuous_fst⟩
  obtain ⟨H,hH0,hHb⟩ := cubeBoundary_homotopy_extension n p v
    (fun x => (congrFun (congrArg DFunLike.coe γ.source) x).trans (hp x).symm)
  refine ⟨H.comp ⟨fun x => (x,1),continuous_id.prodMk continuous_const⟩,⟨{
    toContinuousMap := H.comp ⟨Prod.swap,continuous_swap⟩
    map_zero_left := hH0
    map_one_left := fun _ => rfl },?_⟩⟩
  intro t x
  exact hHb x t

theorem CubeBoundaryTransport.source {γ : Path a b} (h : CubeBoundaryTransport γ p q)
    (x : ↥(_root_.Cube.boundary (Fin n))) : p x.val = a x := by
  obtain ⟨H,hH⟩ := h
  exact (H.apply_zero x.val).symm.trans ((hH 0 x).trans
    (congrArg (fun f => f x) γ.source))

theorem CubeBoundaryTransport.target {γ : Path a b} (h : CubeBoundaryTransport γ p q)
    (x : ↥(_root_.Cube.boundary (Fin n))) : q x.val = b x := by
  obtain ⟨H,hH⟩ := h
  exact (H.apply_one x.val).symm.trans ((hH 1 x).trans
    (congrArg (fun f => f x) γ.target))

theorem CubeBoundaryTransport.symm {γ : Path a b} (h : CubeBoundaryTransport γ p q) :
    CubeBoundaryTransport γ.symm q p := by
  obtain ⟨H,hH⟩ := h
  exact ⟨H.symm,fun t x => hH (unitInterval.symm t) x⟩

theorem CubeBoundaryTransport.trans {γ : Path a b} {δ : Path b c}
    (h : CubeBoundaryTransport γ p q) (k : CubeBoundaryTransport δ q r) :
    CubeBoundaryTransport (γ.trans δ) p r := by
  obtain ⟨H,hH⟩ := h
  obtain ⟨K,hK⟩ := k
  refine ⟨H.trans K,?_⟩
  intro t x
  rw [ContinuousMap.Homotopy.trans_apply,Path.trans_apply]
  split_ifs
  · exact hH _ x
  · exact hK _ x

/-- Homotopic paths of arbitrary boundary maps give the same possible
endpoint disks, without changing either endpoint. -/
theorem CubeBoundaryTransport.change_path {γ δ : Path a b}
    (h : CubeBoundaryTransport γ p q) (K : γ.Homotopy δ) :
    CubeBoundaryTransport δ p q := by
  have hp := h.source
  have hq := h.target
  obtain ⟨H,hH⟩ := h
  obtain ⟨F,hF0,hF1,hFs⟩ := exists_cylinderBoundary_boundaryPath_family n p q K hp hq
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
      exact (congrArg (fun f => f ⟨x,hx⟩) (K.apply_zero s)).trans (hH s ⟨x,hx⟩).symm
  obtain ⟨G,hG0,hGb⟩ := cylinderBoundary_homotopy_extension n H.toContinuousMap F hF
  refine ⟨{
    toContinuousMap := G.comp ⟨fun z => (z,1),continuous_id.prodMk continuous_const⟩
    map_zero_left := fun x => (hGb ⟨(0,x),Or.inl rfl⟩ 1).trans (hF0 1 x)
    map_one_left := fun x => (hGb ⟨(1,x),Or.inr (Or.inl rfl)⟩ 1).trans (hF1 1 x) },?_⟩
  intro t x
  exact (hGb ⟨(t,x.val),Or.inr (Or.inr x.property)⟩ 1).trans
    ((hFs 1 t x.val x.property).trans (congrArg (fun f => f x) (K.apply_one t)))

theorem CubeBoundaryTransport.of_homotopic
    (h : p.HomotopicRel q (_root_.Cube.boundary (Fin n)))
    (hp : ∀ x : ↥(_root_.Cube.boundary (Fin n)), p x.val = a x) :
    CubeBoundaryTransport (Path.refl a) p q := by
  obtain ⟨H⟩ := h
  exact ⟨H.toHomotopy,fun t x => (H.eq_fst t x.property).trans (hp x)⟩

theorem CubeBoundaryTransport.homotopic
    (h : CubeBoundaryTransport (Path.refl a) p q) :
    p.HomotopicRel q (_root_.Cube.boundary (Fin n)) := by
  have hp := h.source
  obtain ⟨H,hH⟩ := h
  exact ⟨{
    toHomotopy := H
    prop' := fun t x hx => (hH t ⟨x,hx⟩).trans (hp ⟨x,hx⟩).symm }⟩

theorem CubeBoundaryTransport.unique {γ : Path a b}
    (h : CubeBoundaryTransport γ p q) (k : CubeBoundaryTransport γ p r) :
    q.HomotopicRel r (_root_.Cube.boundary (Fin n)) :=
  ((h.symm.trans k).change_path (Path.Homotopy.reflSymmTrans γ).symm).homotopic

theorem CubeBoundaryTransport.pre_homotopic {γ : Path a b}
    (h : p.HomotopicRel q (_root_.Cube.boundary (Fin n)))
    (k : CubeBoundaryTransport γ q r) : CubeBoundaryTransport γ p r := by
  have hp (x : ↥(_root_.Cube.boundary (Fin n))) : p x.val = a x :=
    (h.fst_eq_snd x.property).trans (k.source x)
  exact ((CubeBoundaryTransport.of_homotopic h hp).trans k).change_path
    (Path.Homotopy.reflTrans γ)

theorem CubeBoundaryTransport.post_homotopic {γ : Path a b}
    (h : CubeBoundaryTransport γ p q)
    (k : q.HomotopicRel r (_root_.Cube.boundary (Fin n))) : CubeBoundaryTransport γ p r :=
  (h.trans (CubeBoundaryTransport.of_homotopic k h.target)).change_path
    (Path.Homotopy.transRefl γ)

/-- Transport of an arbitrary boundary preserves and reflects the actual
relative homotopy relation on its endpoint disks. -/
theorem CubeBoundaryTransport.homotopic_iff {γ : Path a b}
    {p' q' : C(Fin n → I,Y)}
    (h : CubeBoundaryTransport γ p p') (k : CubeBoundaryTransport γ q q') :
    p.HomotopicRel q (_root_.Cube.boundary (Fin n)) ↔
      p'.HomotopicRel q' (_root_.Cube.boundary (Fin n)) := by
  constructor
  · intro h'
    exact h.unique (k.pre_homotopic h')
  · intro h'
    exact h.symm.unique (k.symm.pre_homotopic h')

end KIP126.Topology
