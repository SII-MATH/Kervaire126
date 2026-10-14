module

public import KIP126.Def.Topology.HomotopyLifting.Path.Endpoint.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyLifting

open scoped unitInterval

universe u v

set_option backward.isDefEq.respectTransparency false

/-- Full cubical boundary lifting survives actual free-path
postcomposition. First lift both endpoint cubes, then lift the retained
path through the proved endpoint comparison. -/
theorem HasCubeBoundaryLifting.pathPostcomp
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {f : C(E, B)} (hf : HasCubeBoundaryLifting f) :
    HasCubeBoundaryLifting
      (⟨fun p => f.comp p, ContinuousMap.continuous_postcomp f⟩ : C(C(I, E), C(I, B))) := by
  intro n g H hcomm
  let g0 : C(↥(_root_.Cube.boundary (Fin n)), E) :=
    ⟨fun z => g z 0, g.continuous.eval continuous_const⟩
  let g1 : C(↥(_root_.Cube.boundary (Fin n)), E) :=
    ⟨fun z => g z 1, g.continuous.eval continuous_const⟩
  let H0 : C(Fin n → I, B) := ⟨fun x => H x 0, H.continuous.eval continuous_const⟩
  let H1 : C(Fin n → I, B) := ⟨fun x => H x 1, H.continuous.eval continuous_const⟩
  obtain ⟨a, ha, hab⟩ := hf n g0 H0
    (fun z => congrArg (fun p : C(I, B) => p 0) (hcomm z))
  obtain ⟨b, hb, hbb⟩ := hf n g1 H1
    (fun z => congrArg (fun p : C(I, B) => p 1) (hcomm z))
  let H' : C(Fin n → I, PathEndpointSpace f) :=
    ⟨fun x => ⟨((a x, b x), H x), (ha x).symm, (hb x).symm⟩,
      ((a.continuous.prodMk b.continuous).prodMk H.continuous).subtype_mk _⟩
  have hc : ∀ z, KIP126.Topology.HomotopyLifting.pathEndpointComparison f (g z) = H' z.val := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (hab z).symm (hbb z).symm
    · exact hcomm z
  obtain ⟨L, hL, hLb⟩ := hf.pathEndpointComparison n g H' hc
  exact ⟨L, fun x => congrArg (fun z : PathEndpointSpace f => z.val.2) (hL x), hLb⟩

end KIP126.Topology.HomotopyLifting
