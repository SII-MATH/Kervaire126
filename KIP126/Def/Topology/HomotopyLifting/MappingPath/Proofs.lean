module

public import KIP126.Def.Topology.HomotopyLifting.MappingPath.Data
public import KIP126.Def.Topology.HomotopyLifting.Cube.PathExtension.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false

/-- The actual mapping-path endpoint has full relative cubical homotopy
lifting: every prescribed bottom and side path is retained exactly. -/
theorem mappingPathEndpoint_hasCubicalLifting
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X,Y)) :
    HasCubicalLifting (mappingPathEndpoint f) := by
  intro n g H hcomm
  let a : C(I × (Fin n → I),X) :=
    ⟨fun z => (g (cubeHornRetraction n z)).val.1,
      (g.continuous.comp (cubeHornRetraction n).continuous).subtype_val.fst⟩
  let p : C(CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)),C(I,Y)) :=
    ⟨fun z => (g z).val.2,g.continuous.subtype_val.snd⟩
  obtain ⟨F,hF0,hF1,hFp⟩ := cubeHorn_path_extension n (f.comp a) H p
    (by
      intro z
      change (g z).val.2 0 = f (g (cubeHornRetraction n z.val)).val.1
      rw [cubeHornRetraction_restrict]
      exact (g z).property)
    hcomm
  let L : C(I × (Fin n → I),MappingPathSpace f) :=
    ⟨fun z => ⟨(a z,F.curry z),hF0 z⟩,
      (a.continuous.prodMk F.curry.continuous).subtype_mk _⟩
  refine ⟨L,hF1,?_⟩
  intro z
  apply Subtype.ext
  apply Prod.ext
  · change (g (cubeHornRetraction n z.val)).val.1 = (g z).val.1
    rw [cubeHornRetraction_restrict]
  · apply ContinuousMap.ext
    intro t
    exact hFp z t

end KIP126.Topology.HomotopyLifting
