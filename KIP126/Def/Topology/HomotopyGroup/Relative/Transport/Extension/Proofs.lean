module

public import KIP126.Def.Topology.HomotopyGroup.Basepoint.Extension.Proofs

@[expose] public section

namespace KIP126.Topology
open Set HomotopyLifting
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- A homotopy of arbitrary boundary paths extends to continuous data
on the full homotopy-cylinder boundary, retaining both endpoint maps. -/
theorem exists_cylinderBoundary_boundaryPath_family {Y : Type u} [TopologicalSpace Y]
    (n : ℕ) (p q : C(Fin n → I,Y))
    {a b : C(↥(_root_.Cube.boundary (Fin n)),Y)}
    {γ δ : Path a b} (K : γ.Homotopy δ)
    (hp : ∀ x : ↥(_root_.Cube.boundary (Fin n)), p x.val = a x)
    (hq : ∀ x : ↥(_root_.Cube.boundary (Fin n)), q x.val = b x) :
    ∃ F : C({z : I × (Fin n → I) // z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))} × I,Y),
      (∀ t x, F (⟨(0,x),Or.inl rfl⟩,t) = p x) ∧
      (∀ t x, F (⟨(1,x),Or.inr (Or.inl rfl)⟩,t) = q x) ∧
      ∀ t s x (hx : x ∈ _root_.Cube.boundary (Fin n)),
        F (⟨(s,x),Or.inr (Or.inr hx)⟩,t) = K (t,s) ⟨x,hx⟩ := by
  classical
  letI : CompactSpace (↥(_root_.Cube.boundary (Fin n))) :=
    isCompact_iff_compactSpace.mp (cubeBoundary_isClosed n).isCompact
  let B := {z : I × (Fin n → I) // z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))}
  let raw : B × I → Y := fun z => if z.1.val.1 = 0 then p z.1.val.2 else
    if z.1.val.1 = 1 then q z.1.val.2 else if hx : z.1.val.2 ∈ _root_.Cube.boundary (Fin n) then K (z.2,z.1.val.1) ⟨z.1.val.2,hx⟩ else p z.1.val.2
  let S₀ : Set (B × I) := {z | z.1.val.1 = 0}
  let S₁ : Set (B × I) := {z | z.1.val.1 = 1}
  let S₂ : Set (B × I) := {z | z.1.val.2 ∈ _root_.Cube.boundary (Fin n)}
  have hS₀ : IsClosed S₀ := isClosed_eq (continuous_subtype_val.comp continuous_fst).fst continuous_const
  have hS₁ : IsClosed S₁ := isClosed_eq (continuous_subtype_val.comp continuous_fst).fst continuous_const
  have hS₂ : IsClosed S₂ := (cubeBoundary_isClosed n).preimage
    (continuous_subtype_val.comp continuous_fst).snd
  have hr₀ : ContinuousOn raw S₀ :=
    (p.continuous.comp (continuous_subtype_val.comp continuous_fst).snd).continuousOn.congr
      (by intro z hz; simp [raw,show z.1.val.1 = 0 from hz])
  have hr₁ : ContinuousOn raw S₁ :=
    (q.continuous.comp (continuous_subtype_val.comp continuous_fst).snd).continuousOn.congr
      (by intro z hz; simp [raw,show z.1.val.1 = 1 from hz])
  have hs (z : B × I) (hz : z.1.val.2 ∈ _root_.Cube.boundary (Fin n)) :
      raw z = K (z.2,z.1.val.1) ⟨z.1.val.2,hz⟩ := by
    dsimp only [raw]
    split_ifs with h h
    · rw [h,Path.Homotopy.source]; exact hp ⟨_,hz⟩
    · rw [h,Path.Homotopy.target]; exact hq ⟨_,hz⟩
    · rfl
  have hr₂ : ContinuousOn raw S₂ := by
    apply continuousOn_iff_continuous_restrict.mpr
    have hc : Continuous (fun z : S₂ => K (z.val.2,z.val.1.val.1)
        ⟨z.val.1.val.2,z.property⟩) :=
      (K.continuous.comp (continuous_subtype_val.snd.prodMk
        ((continuous_subtype_val.comp continuous_subtype_val.fst).fst))).eval
          (((continuous_subtype_val.comp continuous_subtype_val.fst).snd).subtype_mk _)
    exact hc.congr (fun z => (hs z.val z.property).symm)
  have hu : S₀ ∪ (S₁ ∪ S₂) = univ := Set.eq_univ_of_forall (fun z => z.1.property)
  have hc : Continuous raw := continuousOn_univ.mp
    (hu ▸ hr₀.union_of_isClosed (hr₁.union_of_isClosed hr₂ hS₁ hS₂) hS₀ (hS₁.union hS₂))
  refine ⟨⟨raw,hc⟩,?_,?_,?_⟩
  · intro t x; simp [raw]
  · intro t x; simp [raw]
  · intro t s x hx; exact hs (⟨(s,x),Or.inr (Or.inr hx)⟩,t) hx


end KIP126.Topology
