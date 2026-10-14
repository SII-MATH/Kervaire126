module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Extension.Proofs
public import Mathlib.Topology.Homotopy.Path

@[expose] public section

namespace KIP126.Topology
open Set HomotopyLifting
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual cube-boundary homotopy extension theorem, with its
unlifted geometric domain and an arbitrary target universe. -/
theorem cubeBoundary_homotopy_extension {Y : Type u} [TopologicalSpace Y]
    (n : ℕ) (f : C(Fin n → I,Y)) (p : C(↥(_root_.Cube.boundary (Fin n)) × I,Y))
    (hp : ∀ x, p (x,0) = f x.val) :
    ∃ H : C((Fin n → I) × I,Y),
      (∀ x, H (x,0) = f x) ∧ (∀ x t, H (x.val,t) = p (x,t)) := by
  let f' : C(cubeObject.{u} n,Y) := f.comp ⟨ULift.down,continuous_uliftDown⟩
  let p' : C(cubeBoundaryObject.{u} n × I,Y) := p.comp
    ⟨fun z => (z.1.down,z.2), (continuous_uliftDown.comp continuous_fst).prodMk continuous_snd⟩
  obtain ⟨H,hH0,hHb⟩ := cubeBoundaryInclusion_hasHomotopyExtension n
    (TopCat.of Y) f' p' (fun x => hp x.down)
  refine ⟨H.comp ⟨fun z => (ULift.up z.1,z.2),
    (continuous_uliftUp.comp continuous_fst).prodMk continuous_snd⟩,?_,?_⟩
  · intro x; exact hH0 (ULift.up x)
  · intro x t; exact hHb (ULift.up x) t

/-- The full boundary of a cube homotopy cylinder has actual homotopy
extension, by its specified identification with the next cube boundary. -/
theorem cylinderBoundary_homotopy_extension {Y : Type u} [TopologicalSpace Y]
    (n : ℕ) (f : C(I × (Fin n → I),Y))
    (p : C({z : I × (Fin n → I) // z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))} × I,Y))
    (hp : ∀ x, p (x,0) = f x.val) :
    ∃ H : C((I × (Fin n → I)) × I,Y),
      (∀ x, H (x,0) = f x) ∧ (∀ x t, H (x.val,t) = p (x,t)) := by
  let e := cubeCylinderHomeomorph n
  have hb (x : ↥(_root_.Cube.boundary (Fin (n+1)))) :
      e.symm x.val ∈ cylinderBoundary (_root_.Cube.boundary (Fin n)) := by
    apply (cubeCylinderHomeomorph_boundary n _).mpr
    simpa only [e,Homeomorph.apply_symm_apply] using x.property
  let p' : C(↥(_root_.Cube.boundary (Fin (n+1))) × I,Y) := p.comp
    ⟨fun z => (⟨e.symm z.1.val,hb z.1⟩,z.2),
      ((e.symm.continuous.comp (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk
        continuous_snd⟩
  obtain ⟨H,hH0,hHb⟩ := cubeBoundary_homotopy_extension (n+1)
    (f.comp ⟨e.symm,e.symm.continuous⟩) p' (fun x => hp ⟨e.symm x.val,hb x⟩)
  refine ⟨H.comp ⟨fun z => (e z.1,z.2),(e.continuous.comp continuous_fst).prodMk continuous_snd⟩,?_,?_⟩
  · intro x
    exact (hH0 (e x)).trans (congrArg f (e.symm_apply_apply x))
  · intro x t
    have hx := (cubeCylinderHomeomorph_boundary n x.val).mp x.property
    exact (hHb ⟨e x.val,hx⟩ t).trans
      (congrArg (fun w => p (w,t)) (Subtype.ext (e.symm_apply_apply x.val)))

/-- Two based cube maps and a varying path of basepoints give a genuine
continuous map on every face of the intervening homotopy cylinder. -/
theorem exists_cylinderBoundary_path_family {Y : Type u} [TopologicalSpace Y]
    (n : ℕ) {a b : Y} (p : GenLoop (Fin n) Y a) (q : GenLoop (Fin n) Y b)
    {γ δ : Path a b} (K : γ.Homotopy δ) :
    ∃ F : C({z : I × (Fin n → I) // z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))} × I,Y),
      (∀ t x, F (⟨(0,x),Or.inl rfl⟩,t) = p x) ∧
      (∀ t x, F (⟨(1,x),Or.inr (Or.inl rfl)⟩,t) = q x) ∧
      ∀ t s x (hx : x ∈ _root_.Cube.boundary (Fin n)),
        F (⟨(s,x),Or.inr (Or.inr hx)⟩,t) = K (t,s) := by
  classical
  let B := {z : I × (Fin n → I) // z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))}
  let raw : B × I → Y := fun z => if z.1.val.1 = 0 then p z.1.val.2 else
    if z.1.val.1 = 1 then q z.1.val.2 else K (z.2,z.1.val.1)
  let S₀ : Set (B × I) := {z | z.1.val.1 = 0}
  let S₁ : Set (B × I) := {z | z.1.val.1 = 1}
  let S₂ : Set (B × I) := {z | z.1.val.2 ∈ _root_.Cube.boundary (Fin n)}
  have hS₀ : IsClosed S₀ := isClosed_eq (continuous_subtype_val.comp continuous_fst).fst continuous_const
  have hS₁ : IsClosed S₁ := isClosed_eq (continuous_subtype_val.comp continuous_fst).fst continuous_const
  have hS₂ : IsClosed S₂ := (cubeBoundary_isClosed n).preimage
    (continuous_subtype_val.comp continuous_fst).snd
  have hr₀ : ContinuousOn raw S₀ :=
    (p.val.continuous.comp (continuous_subtype_val.comp continuous_fst).snd).continuousOn.congr
      (by intro z hz; simp [raw,show z.1.val.1 = 0 from hz])
  have hr₁ : ContinuousOn raw S₁ :=
    (q.val.continuous.comp (continuous_subtype_val.comp continuous_fst).snd).continuousOn.congr
      (by intro z hz; simp [raw,show z.1.val.1 = 1 from hz])
  have hs (z : B × I) (hz : z.1.val.2 ∈ _root_.Cube.boundary (Fin n)) :
      raw z = K (z.2,z.1.val.1) := by
    dsimp only [raw]
    split_ifs with h h
    · rw [h,Path.Homotopy.source]; exact p.property _ hz
    · rw [h,Path.Homotopy.target]; exact q.property _ hz
    · rfl
  have hr₂ : ContinuousOn raw S₂ := (K.continuous.comp
    (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst).fst)).continuousOn.congr hs
  have hu : S₀ ∪ (S₁ ∪ S₂) = univ := Set.eq_univ_of_forall (fun z => z.1.property)
  have hc : Continuous raw := continuousOn_univ.mp
    (hu ▸ hr₀.union_of_isClosed (hr₁.union_of_isClosed hr₂ hS₁ hS₂) hS₀ (hS₁.union hS₂))
  refine ⟨⟨raw,hc⟩,?_,?_,?_⟩
  · intro t x; simp [raw]
  · intro t x; simp [raw]
  · intro t s x hx; exact hs (⟨(s,x),Or.inr (Or.inr hx)⟩,t) hx

end KIP126.Topology
