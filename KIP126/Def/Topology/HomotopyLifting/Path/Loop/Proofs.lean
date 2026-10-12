module

public import KIP126.Def.Topology.HomotopyLifting.Path.Endpoint.Proofs
public import KIP126.Def.Topology.Path.Translation.Pointed.Data

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false

/-- Actual full-boundary lifting is preserved by the based loop map:
use the endpoint comparison with both endpoints fixed at the basepoint. -/
theorem HasCubeBoundaryLifting.continuousBasedLoopMap
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {f : C(E,B)} (hf : HasCubeBoundaryLifting f) (e : E) (b : B) (h : f e = b) :
    HasCubeBoundaryLifting (continuousBasedLoopMap f e b h) := by
  intro n g H hcomm
  let g' : C(↥(_root_.Cube.boundary (Fin n)),C(I,E)) :=
    ⟨fun x => (g x).toContinuousMap,
      ContinuousMap.continuous_of_continuous_uncurry _
        ((g.continuous.comp continuous_fst).eval continuous_snd)⟩
  let H' : C(Fin n → I,PathEndpointSpace f) :=
    ⟨fun x => ⟨((e,e),(H x).toContinuousMap), (H x).source.trans h.symm,
      (H x).target.trans h.symm⟩,
      (continuous_const.prodMk (ContinuousMap.continuous_of_continuous_uncurry _
        ((H.continuous.comp continuous_fst).eval continuous_snd))).subtype_mk _⟩
  have hc : ∀ z, KIP126.Topology.HomotopyLifting.pathEndpointComparison f (g' z) = H' z.val := by
    intro z
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext (g z).source (g z).target
    · exact congrArg Path.toContinuousMap (hcomm z)
  obtain ⟨l, hl, hlb⟩ := hf.pathEndpointComparison n g' H' hc
  let L : C(Fin n → I,Path e e) := {
    toFun x := {
      toContinuousMap := l x
      source' := congrArg (fun z : PathEndpointSpace f => z.val.1.1) (hl x)
      target' := congrArg (fun z : PathEndpointSpace f => z.val.1.2) (hl x) }
    continuous_toFun := Path.continuous_uncurry_iff.mp
      ((l.continuous.comp continuous_fst).eval continuous_snd) }
  refine ⟨L, ?_, ?_⟩
  · intro x
    apply Path.ext
    funext t
    exact congrArg (fun z : PathEndpointSpace f => z.val.2 t) (hl x)
  · intro z
    apply Path.ext
    funext t
    exact congrArg (fun p : C(I,E) => p t) (hlb z)

end KIP126.Topology.HomotopyLifting
