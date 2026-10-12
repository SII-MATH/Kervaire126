module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Sequence.Model.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory HomotopicalAlgebra
open KIP126.Topology.HomotopyLifting
universe u

/-- The actual cube attachment theorem constructs the entire compatible
extension package; none of its comparison properties is an input. -/
theorem nonempty_orderRealizationExtension_of_cube_attachCells
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hc : Nonempty (AttachCells.{u} cubeBoundaryInclusion.{u} f))
    (M : OrderRealizationModel X) : Nonempty (OrderRealizationExtension f M) := by
  obtain ⟨c⟩ := hc
  obtain ⟨R,hR,j,E,hE,hEinv⟩ := exists_order_model_of_cube_attachCells c M.order M.equivalence
  letI := hR
  exact ⟨⟨⟨PartOrd.of R,E⟩,j,hE,hEinv⟩⟩

end KIP126.Topology.SimplicialRealization
