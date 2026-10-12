module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Topology.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open Set
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Paths prescribed on an entire cube horn extend while retaining
both prescribed endpoint maps. The extra path coordinate turns the
union of these three pieces into the next genuine cube horn. -/
theorem cubeHorn_path_extension {Y : Type u} [TopologicalSpace Y] (n : ℕ)
    (a b : C(I × (Fin n → I),Y))
    (p : C(CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)),C(I,Y)))
    (hp0 : ∀ z, p z 0 = a z.val) (hp1 : ∀ z, p z 1 = b z.val) :
    ∃ F : C((I × (Fin n → I)) × I,Y),
      (∀ z, F (z,0) = a z) ∧ (∀ z, F (z,1) = b z) ∧
      ∀ z t, F (z.val,t) = p z t := by
  classical
  let W := CylinderHorn (Fin (n+1) → I) (_root_.Cube.boundary (Fin (n+1)))
  let x : C(W,I × (Fin n → I)) :=
    ⟨fun z => (z.val.1,fun i => z.val.2 i.succ),
      continuous_subtype_val.fst.prodMk
        (continuous_pi (fun i => (continuous_apply i.succ).comp continuous_subtype_val.snd))⟩
  let v : C(W,I) := ⟨fun z => z.val.2 0,(continuous_apply 0).comp continuous_subtype_val.snd⟩
  let V : Set W := {z | (x z).1 = 0 ∨ (x z).2 ∈ _root_.Cube.boundary (Fin n)}
  let S₀ : Set W := {z | v z = 0}
  let S₁ : Set W := {z | v z = 1}
  have hV : IsClosed V := (isClosed_eq x.continuous.fst continuous_const).union
    ((cubeBoundary_isClosed n).preimage x.continuous.snd)
  have hS₀ : IsClosed S₀ := isClosed_eq v.continuous continuous_const
  have hS₁ : IsClosed S₁ := isClosed_eq v.continuous continuous_const
  have cover : S₀ ∪ (S₁ ∪ V) = univ := by
    apply Set.eq_univ_of_forall
    intro z
    rcases z.property with ht | ⟨i,hi⟩
    · exact Or.inr (Or.inr (Or.inl ht))
    · induction i using Fin.cases with
      | zero => exact hi.elim Or.inl (fun h => Or.inr (Or.inl h))
      | succ i => exact Or.inr (Or.inr (Or.inr ⟨i,hi⟩))
  let raw : W → Y := fun z => if hz : z ∈ V then p ⟨x z,hz⟩ (v z)
    else if v z = 0 then a (x z) else b (x z)
  have raw0 (z : W) (hz : v z = 0) : raw z = a (x z) := by
    dsimp only [raw]
    split_ifs with hv
    · rw [hz]; exact hp0 ⟨x z,hv⟩
    · rfl
  have raw1 (z : W) (hz : v z = 1) : raw z = b (x z) := by
    dsimp only [raw]
    split_ifs with hv h0
    · rw [hz]; exact hp1 ⟨x z,hv⟩
    · exact False.elim (zero_ne_one (h0.symm.trans hz))
    · rfl
  have rawV (z : W) (hz : z ∈ V) : raw z = p ⟨x z,hz⟩ (v z) := dif_pos hz
  have hc0 : ContinuousOn raw S₀ := (a.continuous.comp x.continuous).continuousOn.congr raw0
  have hc1 : ContinuousOn raw S₁ := (b.continuous.comp x.continuous).continuousOn.congr raw1
  have hcV : ContinuousOn raw V := by
    apply continuousOn_iff_continuous_restrict.mpr
    have hu : Continuous (fun z : V => (⟨x z.val,z.property⟩ :
        CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)))) :=
      (x.continuous.comp continuous_subtype_val).subtype_mk _
    exact ((p.continuous.comp hu).eval (v.continuous.comp continuous_subtype_val)).congr
      (fun z => (rawV z.val z.property).symm)
  have hc : Continuous raw := continuousOn_univ.mp
    (cover ▸ hc0.union_of_isClosed (hc1.union_of_isClosed hcV hS₁ hV) hS₀ (hS₁.union hV))
  let F : C((I × (Fin n → I)) × I,Y) :=
    ⟨fun z => raw (cubeHornRetraction (n+1) (z.1.1,Fin.cons z.2 z.1.2)),
      hc.comp ((cubeHornRetraction (n+1)).continuous.comp
        (continuous_fst.fst.prodMk ((cubeCylinderHomeomorph n).continuous.comp
          (continuous_snd.prodMk continuous_fst.snd))))⟩
  refine ⟨F,?_,?_,?_⟩
  · intro z
    have h : (z.1,Fin.cons (0:I) z.2) ∈ {w : I × (Fin (n+1) → I) | w.1 = 0 ∨ w.2 ∈ _root_.Cube.boundary (Fin (n+1))} :=
      Or.inr ⟨0,Or.inl rfl⟩
    change raw (cubeHornRetraction (n+1) (z.1,Fin.cons (0:I) z.2)) = a z
    rw [cubeHornRetraction_restrict (n+1) ⟨_,h⟩]
    exact raw0 ⟨_,h⟩ rfl
  · intro z
    have h : (z.1,Fin.cons (1:I) z.2) ∈ {w : I × (Fin (n+1) → I) | w.1 = 0 ∨ w.2 ∈ _root_.Cube.boundary (Fin (n+1))} :=
      Or.inr ⟨0,Or.inr rfl⟩
    change raw (cubeHornRetraction (n+1) (z.1,Fin.cons (1:I) z.2)) = b z
    rw [cubeHornRetraction_restrict (n+1) ⟨_,h⟩]
    exact raw1 ⟨_,h⟩ rfl
  · intro z t
    have h : z.val.1 = 0 ∨ Fin.cons t z.val.2 ∈ _root_.Cube.boundary (Fin (n+1)) := by
      rcases z.property with ht | ⟨i,hi⟩
      · exact Or.inl ht
      · exact Or.inr ⟨i.succ,hi⟩
    change raw (cubeHornRetraction (n+1) (z.val.1,Fin.cons t z.val.2)) = p z t
    rw [cubeHornRetraction_restrict (n+1) ⟨_,h⟩]
    exact rawV ⟨(z.val.1,Fin.cons t z.val.2),h⟩ z.property

end KIP126.Topology.HomotopyLifting
