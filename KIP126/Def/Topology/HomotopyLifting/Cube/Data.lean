module

public import KIP126.Def.Topology.HomotopyLifting.Cube.ClosedBall.Proofs
public import KIP126.Def.Topology.Ball.HomotopyExtension.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open Metric Set
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The actual radial retraction onto the bottom and all side faces. -/
noncomputable def cubeHornRetraction (n : ℕ) :
    C(I × (Fin n → I), CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n))) := by
  let h := cubeClosedBallHomeomorph n
  let r : C(I × (Fin n → I), closedBall (0 : Fin n → ℝ) 1 × I) :=
    ⟨fun z => Ball.cylinderRetraction (h z.2,z.1),
      Ball.cylinderRetraction_continuous.comp ((h.continuous.comp continuous_snd).prodMk continuous_fst)⟩
  have hr (z : I × (Fin n → I)) :
      (r z).2 = 0 ∨ h.symm (r z).1 ∈ _root_.Cube.boundary (Fin n) := by
    rcases Ball.cylinderRetraction_range (h z.2,z.1) with ht | hz
    · exact Or.inl ht
    · right
      apply (cubeClosedBallHomeomorph_boundary n _).mpr
      change ‖(h (h.symm (r z).1)).val‖ = 1
      rw [h.apply_symm_apply]
      exact hz
  exact ⟨fun z => ⟨((r z).2,h.symm (r z).1),hr z⟩,
    (r.continuous.snd.prodMk (h.symm.continuous.comp r.continuous.fst)).subtype_mk hr⟩


end KIP126.Topology.HomotopyLifting
