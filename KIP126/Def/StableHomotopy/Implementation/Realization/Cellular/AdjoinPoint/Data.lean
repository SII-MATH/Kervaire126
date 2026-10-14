module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.AdjoinPoint.Functor.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Boundary.Cube.Proofs
public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory CategoryTheory.Limits Simplicial HomotopicalAlgebra
open KIP126.Topology.SimplicialRealization KIP126.Topology.HomotopyLifting
universe u
set_option backward.isDefEq.respectTransparency false

/-- The original finite-dimensional simplicial attachment, realized and
given a disjoint point, is an actual cubical based attachment. The original
attaching map and the original indexing family are retained. -/
noncomputable def realizedAdjoinPointCubeAttachCells
    (n : ℕ) {K L : SSet.{u}} {f : K ⟶ L}
    (c : AttachCells.{u} (fun (_ : Unit) => ∂Δ[n].ι) f) :
    AttachCells.{u} (fun k => BasedSpace.adjoinPointMap (cubeBoundaryInclusion.{u} k))
      (BasedSpace.adjoinPointMap (SSet.toTop.map f)) := by
  let F := SSet.toTop ⋙ BasedSpace.adjoinPointFunctor
  let d : AttachCells.{u} (fun (_ : Unit) => F.map (∂Δ[n].ι)) (F.map f) := {
    ι := c.ι
    π := c.π
    cofan₁ := Cofan.mk _ (fun j => F.map (c.cofan₁.inj j))
    cofan₂ := Cofan.mk _ (fun j => F.map (c.cofan₂.inj j))
    isColimit₁ := isColimitCofanMkObjOfIsColimit F _ _ c.isColimit₁
    isColimit₂ := isColimitCofanMkObjOfIsColimit F _ _ c.isColimit₂
    m := F.map c.m
    hm j := by
      change F.map (c.cofan₁.inj j) ≫ F.map c.m =
        F.map (∂Δ[n].ι) ≫ F.map (c.cofan₂.inj j)
      rw [← F.map_comp, ← F.map_comp, c.hm]
    g₁ := F.map c.g₁
    g₂ := F.map c.g₂
    isPushout := c.isPushout.map F }
  exact d.reindexCellTypes
    (fun k => BasedSpace.adjoinPointMap (cubeBoundaryInclusion.{u} k)) (fun _ => n)
    (fun _ => BasedSpace.adjoinPointFunctor.mapArrow.mapIso
      (nonempty_boundary_realization_cube_arrow_iso n).some)

end KIP126.StableHomotopy.Implementation
