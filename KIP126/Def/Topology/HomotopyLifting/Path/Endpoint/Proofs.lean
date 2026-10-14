module

public import KIP126.Def.Topology.HomotopyLifting.Path.Endpoint.Data
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Proofs
public import KIP126.Def.Topology.HomotopyGroup.Relative.Transport.Extension.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyLifting

open Set
open scoped unitInterval

universe u v

set_option backward.isDefEq.respectTransparency false

/-- Endpoint maps and a compatible family of boundary paths determine
continuous data on the entire homotopy-cylinder boundary. -/
theorem exists_cylinderBoundary_map_of_paths {E : Type u} [TopologicalSpace E]
    (n : ℕ) (a b : C(Fin n → I,E))
    (g : C(↥(_root_.Cube.boundary (Fin n)),C(I,E)))
    (h0 : ∀ z, g z 0 = a z.val) (h1 : ∀ z, g z 1 = b z.val) :
    ∃ G : C({z : I × (Fin n → I) //
        z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))},E),
      (∀ x, G ⟨(0,x),Or.inl rfl⟩ = a x) ∧
      (∀ x, G ⟨(1,x),Or.inr (Or.inl rfl)⟩ = b x) ∧
      ∀ t x (hx : x ∈ _root_.Cube.boundary (Fin n)),
        G ⟨(t,x),Or.inr (Or.inr hx)⟩ = g ⟨x,hx⟩ t := by
  letI : CompactSpace (↥(_root_.Cube.boundary (Fin n))) :=
    isCompact_iff_compactSpace.mp (cubeBoundary_isClosed n).isCompact
  let i : C(↥(_root_.Cube.boundary (Fin n)),Fin n → I) :=
    ⟨Subtype.val,continuous_subtype_val⟩
  let γ : Path (a.comp i) (b.comp i) := {
    toFun := (⟨fun z : I × ↥(_root_.Cube.boundary (Fin n)) => g z.2 z.1,
      (g.continuous.comp continuous_snd).eval continuous_fst⟩ :
        C(I × ↥(_root_.Cube.boundary (Fin n)),E)).curry
    continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _
      ((g.continuous.comp continuous_snd).eval continuous_fst)
    source' := ContinuousMap.ext h0
    target' := ContinuousMap.ext h1 }
  obtain ⟨F,hF0,hF1,hFs⟩ := exists_cylinderBoundary_boundaryPath_family n a b
    (Path.Homotopy.refl γ) (fun _ => rfl) (fun _ => rfl)
  refine ⟨F.comp ⟨fun z => (z,0),continuous_id.prodMk continuous_const⟩,?_,?_,?_⟩
  · exact hF0 0
  · exact hF1 0
  · intro t x hx
    exact hFs 0 t x hx

/-- Boundary lifting is preserved by the actual endpoint comparison for
path spaces. The lift retains both endpoint maps and the whole boundary
path family. -/
theorem HasCubeBoundaryLifting.pathEndpointComparison
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {f : C(E,B)} (hf : HasCubeBoundaryLifting f) :
    HasCubeBoundaryLifting (pathEndpointComparison f) := by
  intro n g H hcomm
  let a : C(Fin n → I,E) := ⟨fun x => (H x).val.1.1,H.continuous.subtype_val.fst.fst⟩
  let b : C(Fin n → I,E) := ⟨fun x => (H x).val.1.2,H.continuous.subtype_val.fst.snd⟩
  have hg0 (z : ↥(_root_.Cube.boundary (Fin n))) : g z 0 = a z.val :=
    congrArg (fun z : PathEndpointSpace f => z.val.1.1) (hcomm z)
  have hg1 (z : ↥(_root_.Cube.boundary (Fin n))) : g z 1 = b z.val :=
    congrArg (fun z : PathEndpointSpace f => z.val.1.2) (hcomm z)
  have hgp (z : ↥(_root_.Cube.boundary (Fin n))) (t : I) :
      f (g z t) = (H z.val).val.2 t :=
    congrArg (fun z : PathEndpointSpace f => z.val.2 t) (hcomm z)
  obtain ⟨G,hG0,hG1,hGs⟩ := exists_cylinderBoundary_map_of_paths n a b g hg0 hg1
  let P : C(I × (Fin n → I),B) :=
    ⟨fun z => (H z.2).val.2 z.1,
      (H.continuous.comp continuous_snd).subtype_val.snd.eval continuous_fst⟩
  have hG : ∀ z, f (G z) = P z.val := by
    rintro ⟨⟨t,x⟩,ht | ht | hx⟩
    · change t = 0 at ht
      subst t
      rw [hG0]
      exact (H x).property.1.symm
    · change t = 1 at ht
      subst t
      rw [hG1]
      exact (H x).property.2.symm
    · rw [hGs t x hx]
      exact hgp ⟨x,hx⟩ t
  obtain ⟨L,hL,hLb⟩ := hf.lift_cylinderBoundary n G P hG
  let l : C(Fin n → I,C(I,E)) :=
    (L.comp ⟨Prod.swap,continuous_swap⟩).curry
  refine ⟨l,?_,?_⟩
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact (hLb ⟨(0,x),Or.inl rfl⟩).trans (hG0 x)
      · exact (hLb ⟨(1,x),Or.inr (Or.inl rfl)⟩).trans (hG1 x)
    · apply ContinuousMap.ext
      intro t
      exact hL (t,x)
  · intro z
    apply ContinuousMap.ext
    intro t
    exact (hLb ⟨(t,z.val),Or.inr (Or.inr z.property)⟩).trans (hGs t z.val z.property)

end KIP126.Topology.HomotopyLifting
