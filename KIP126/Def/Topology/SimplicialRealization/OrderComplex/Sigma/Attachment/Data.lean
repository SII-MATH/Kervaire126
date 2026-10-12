module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Attachment.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial

universe u

variable {ι : Type u} (P : ι → Type u) [∀ j, PartialOrder (P j)]
    {Q : Type u} [PartialOrder Q] (f : (Σ j, P j) →o Q)

/-- The explicit order model of a simultaneous family of cone attachments.
Every cone retains its own apex. -/
abbrev OrderSigmaConeAttachment :=
  OrderAttachment (orderSigmaConeEmbedding P) (orderSigmaConeEmbedding_isLowerSet P) f

/-- The old target is an induced suborder of the simultaneous attachment. -/
def orderSigmaConeAttachmentTargetEmbedding : Q ↪o OrderSigmaConeAttachment P f where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Iff.rfl

/-- The actual nerve inclusion of the old target in the simultaneous attachment. -/
def orderSigmaConeAttachmentTargetInclusion : nerve Q ⟶ nerve (OrderSigmaConeAttachment P f) :=
  nerveMap (orderSigmaConeAttachmentTargetEmbedding P f).monotone.functor

end KIP126.Topology.SimplicialRealization
