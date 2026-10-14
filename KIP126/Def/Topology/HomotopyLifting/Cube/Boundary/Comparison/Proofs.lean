module

public import KIP126.Def.Topology.HomotopyGroup.Relative.Normalization.Proofs
public import KIP126.Def.Topology.HomotopyGroup.Relative.BoundaryAdjustment.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false

/-- Full relative cubical homotopy lifting makes a lift up to relative
homotopy into an exact lift, retaining its entire boundary. -/
theorem HasCubicalLifting.exists_lift_of_homotopicRel
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {f : C(E,B)} (hf : HasCubicalLifting f) (n : ℕ)
    (p : C(Fin n → I,E)) (F : C(Fin n → I,B))
    (h : (f.comp p).HomotopicRel F (_root_.Cube.boundary (Fin n))) :
    ∃ q : C(Fin n → I,E), (∀ x, f (q x) = F x) ∧
      ∀ x : ↥(_root_.Cube.boundary (Fin n)), q x.val = p x.val := by
  obtain ⟨H⟩ := h
  let g : C(CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)),E) :=
    ⟨fun z => p z.val.2,p.continuous.comp continuous_subtype_val.snd⟩
  obtain ⟨L,hL,hLb⟩ := hf n g H.toHomotopy.toContinuousMap (by
    rintro ⟨⟨t,x⟩,ht | hx⟩
    · change t = 0 at ht
      subst t
      exact (H.apply_zero x).symm
    · exact (H.eq_fst t hx).symm)
  refine ⟨L.comp ⟨fun x => (1,x),continuous_const.prodMk continuous_id⟩,?_,?_⟩
  · intro x
    exact (hL (1,x)).trans (H.apply_one x)
  · intro x
    exact hLb ⟨(1,x.val),Or.inr x.property⟩

/-- A fibration surjective on homotopy groups solves every disk lifting
problem whose source boundary already extends to a source disk. -/
theorem HasCubicalLifting.exists_lift_of_extendible_boundary
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {f : C(E,B)} (hf : HasCubicalLifting f) (n : ℕ)
    (hπ : ∀ e, Function.Surjective (continuousHomotopyMap f e (f e) rfl n))
    (p : C(Fin n → I,E)) (F : C(Fin n → I,B))
    (hF : ∀ x : ↥(_root_.Cube.boundary (Fin n)), f (p x.val) = F x.val) :
    ∃ q : C(Fin n → I,E), (∀ x, f (q x) = F x) ∧
      ∀ x : ↥(_root_.Cube.boundary (Fin n)), q x.val = p x.val := by
  obtain ⟨q,hq,H⟩ := exists_homotopicRel_lift_of_continuousHomotopyMap_surjective
    f n hπ p F (fun x => (hF x).symm)
  obtain ⟨r,hr,hrb⟩ := hf.exists_lift_of_homotopicRel n q F H
  exact ⟨r,hr,fun x => (hrb x).trans (hq x)⟩

/-- Injectivity on homotopy groups removes the final obstruction to
extending a lifted full cylinder boundary as an ordinary source map. -/
theorem HasCubicalLifting.exists_cylinderBoundary_extension
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {f : C(E,B)} (hf : HasCubicalLifting f) (n : ℕ)
    (hπ : ∀ e, Function.Injective (continuousHomotopyMap f e (f e) rfl n))
    (g : C({z : I × (Fin n → I) // z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))},E))
    (H : C(I × (Fin n → I),B)) (hcomm : ∀ z, f (g z) = H z.val) :
    ∃ A : C(I × (Fin n → I),E), ∀ z, A z.val = g z := by
  let j : C(CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)),
      {z : I × (Fin n → I) // z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))}) :=
    ⟨fun z => ⟨z.val,z.property.elim Or.inl (fun h => Or.inr (Or.inr h))⟩,
      continuous_subtype_val.subtype_mk _⟩
  obtain ⟨L,hL,hLg⟩ := hf n (g.comp j) H (fun z => hcomm (j z))
  let p := L.comp ⟨fun x => (1,x),continuous_const.prodMk continuous_id⟩
  let q : C(Fin n → I,E) :=
    ⟨fun x => g ⟨(1,x),Or.inr (Or.inl rfl)⟩,
      g.continuous.comp ((continuous_const.prodMk continuous_id).subtype_mk _)⟩
  have hpq (x : ↥(_root_.Cube.boundary (Fin n))) : p x.val = q x.val :=
    hLg ⟨(1,x.val),Or.inr x.property⟩
  have heq : f.comp p = f.comp q := by
    ext x
    exact (hL (1,x)).trans (hcomm ⟨(1,x),Or.inr (Or.inl rfl)⟩).symm
  have hH : (f.comp p).HomotopicRel (f.comp q) (_root_.Cube.boundary (Fin n)) := by
    rw [heq]
    exact ContinuousMap.HomotopicRel.refl _
  obtain ⟨T⟩ := homotopicRel_of_continuousHomotopyMap_injective f n hπ p q hpq hH
  obtain ⟨A,hA1,hAh⟩ := cylinder_top_adjustment n L q T
  refine ⟨A,?_⟩
  rintro ⟨⟨t,x⟩,h0 | h1 | hx⟩
  · exact (hAh ⟨(t,x),Or.inl h0⟩).trans (hLg ⟨(t,x),Or.inl h0⟩)
  · change t = 1 at h1
    subst t
    exact hA1 x
  · exact (hAh ⟨(t,x),Or.inr hx⟩).trans (hLg ⟨(t,x),Or.inr hx⟩)

/-- For a nonempty source, full relative cubical homotopy lifting and
bijections on every actual based homotopy set imply actual lifting
against every full cube boundary. No replacement or model axiom is used. -/
theorem HasCubicalLifting.hasCubeBoundaryLifting_of_homotopy_bijective
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {f : C(E,B)} (hf : HasCubicalLifting f) (e : E)
    (hπ : ∀ x n, Function.Bijective (continuousHomotopyMap f x (f x) rfl n)) :
    HasCubeBoundaryLifting f := by
  intro n g F hcomm
  cases n with
  | zero =>
    obtain ⟨q,hq,hqb⟩ := hf.exists_lift_of_extendible_boundary 0
      (fun x => (hπ x 0).surjective) (ContinuousMap.const _ e) F (by
        intro x
        rcases x.property with ⟨i,hi⟩
        exact Fin.elim0 i)
    refine ⟨q,hq,?_⟩
    intro x
    rcases x.property with ⟨i,hi⟩
    exact Fin.elim0 i
  | succ n =>
    let c := cubeCylinderHomeomorph n
    let g' : C({z : I × (Fin n → I) // z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))},E) :=
      ⟨fun z => g ⟨c z.val,(cubeCylinderHomeomorph_boundary n z.val).mp z.property⟩,
        g.continuous.comp ((c.continuous.comp continuous_subtype_val).subtype_mk _)⟩
    obtain ⟨A,hAb⟩ := hf.exists_cylinderBoundary_extension n
      (fun x => (hπ x n).injective) g' (F.comp ⟨c,c.continuous⟩)
      (fun z => hcomm ⟨c z.val,(cubeCylinderHomeomorph_boundary n z.val).mp z.property⟩)
    let p : C(Fin (n+1) → I,E) := A.comp ⟨c.symm,c.symm.continuous⟩
    have hp (x : ↥(_root_.Cube.boundary (Fin (n+1)))) : p x.val = g x := by
      have hx : c.symm x.val ∈ cylinderBoundary (_root_.Cube.boundary (Fin n)) := by
        apply (cubeCylinderHomeomorph_boundary n _).mpr
        simpa only [c,Homeomorph.apply_symm_apply] using x.property
      exact (hAb ⟨c.symm x.val,hx⟩).trans
        (congrArg g (Subtype.ext (c.apply_symm_apply x.val)))
    obtain ⟨q,hq,hqb⟩ := hf.exists_lift_of_extendible_boundary (n+1)
      (fun x => (hπ x (n+1)).surjective) p F
      (fun x => (congrArg f (hp x)).trans (hcomm x))
    exact ⟨q,hq,fun x => (hqb x).trans (hp x)⟩

end KIP126.Topology.HomotopyLifting
