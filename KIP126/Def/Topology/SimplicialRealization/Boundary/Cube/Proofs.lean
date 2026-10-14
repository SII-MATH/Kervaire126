module

public import KIP126.Def.Topology.SimplicialRealization.Boundary.Proofs
public import KIP126.Def.Topology.Simplex.ClosedBall.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.ClosedBall
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory Simplicial KIP126.Topology.HomotopyLifting
universe u
set_option backward.isDefEq.respectTransparency false

/-- The original realized standard-simplex boundary inclusion is
isomorphic as an actual arrow to the full cubical boundary inclusion.
The target and boundary homeomorphisms commute with the original maps. -/
theorem nonempty_boundary_realization_cube_arrow_iso (n : ℕ) :
    Nonempty (Arrow.mk (SSet.toTop.map (∂Δ[n].ι)) ≅
      Arrow.mk (cubeBoundaryInclusion.{u} n)) := by
  obtain ⟨s, hs⟩ := Simplex.exists_stdSimplex_closedBall_homeomorph n
  let e := s.trans (cubeClosedBallHomeomorph n).symm
  have he (x : stdSimplex ℝ (Fin (n+1))) :
      (∃ i, x.1 i = 0) ↔ e x ∈ _root_.Cube.boundary (Fin n) := by
    rw [cubeClosedBallHomeomorph_boundary]
    change (∃ i, x.1 i = 0) ↔
      ‖(cubeClosedBallHomeomorph n ((cubeClosedBallHomeomorph n).symm (s x))).val‖ = 1
    rw [Homeomorph.apply_symm_apply]
    exact hs x
  obtain ⟨b, hb⟩ := exists_boundary_realization_homeomorph.{u} n
  let d : |(Δ[n] : SSet.{u})| ≃ₜ cubeObject.{u} n :=
    (SimplexCategory.toTopHomeo ⦋n⦌).trans (e.trans Homeomorph.ulift.symm)
  let a : |(∂Δ[n] : SSet.{u})| ≃ₜ cubeBoundaryObject.{u} n :=
    b.trans ((e.subtype he).trans Homeomorph.ulift.symm)
  refine ⟨Arrow.isoMk (TopCat.isoOfHomeo a) (TopCat.isoOfHomeo d) ?_⟩
  ext x
  apply ULift.ext
  exact congrArg e (hb x)

end KIP126.Topology.SimplicialRealization
