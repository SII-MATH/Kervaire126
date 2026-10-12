module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Faces.Retraction.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

noncomputable def cubeFacesHornRetraction {n : ℕ} (faces : Set (Fin n × Bool)) :
    C(I × (Fin n → I), CylinderHorn (Fin n → I) (cubeFacesBoundary n faces)) :=
  ⟨fun z => ⟨cubeFacesRetractionRaw faces z,cubeFacesRetractionRaw_range faces z⟩,
    (cubeFacesRetractionRaw_continuous faces).subtype_mk _⟩


end KIP126.Topology.HomotopyLifting
