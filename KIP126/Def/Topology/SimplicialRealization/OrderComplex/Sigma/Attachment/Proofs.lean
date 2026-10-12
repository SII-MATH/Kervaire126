module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Approximation.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Cone.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Attachment.Equivalence.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every actual simultaneous attachment of cones on finite order
realizations to an arbitrary order realization has an explicit order
homotopy model after independently subdividing the bases. The equivalence
and its inverse strictly preserve the old target. -/
theorem exists_orderSigmaConeAttachment_homotopyEquiv
    {ι : Type u} (P : ι → Type u) [∀ j, PartialOrder (P j)] [∀ j, Fintype (P j)]
    (Q : Type u) [PartialOrder Q]
    (a : SSet.toTop.obj (nerve (Σ j, P j)) ⟶ SSet.toTop.obj (nerve Q))
    {T : TopCat.{u}} (u : SSet.toTop.obj (nerve Q) ⟶ T)
    (v : SSet.toTop.obj (nerve (Σ j, WithTop (P j))) ⟶ T)
    (hp : IsPushout a (SSet.toTop.map (nerveMap (orderSigmaConeEmbedding P).monotone.functor)) u v) :
    ∃ (n : ι → ℕ) (f : (Σ j, iteratedOrderSubdivision (P j) (n j + 1)) →o Q)
      (E : ContinuousMap.HomotopyEquiv
        |nerve (OrderSigmaConeAttachment (fun j => iteratedOrderSubdivision (P j) (n j + 1)) f)| T),
      (∀ y : |nerve Q|, E (SSet.toTop.map (orderSigmaConeAttachmentTargetInclusion
        (fun j => iteratedOrderSubdivision (P j) (n j + 1)) f) y) = u y) ∧
      ∀ y : |nerve Q|, E.invFun (u y) = SSet.toTop.map
        (orderSigmaConeAttachmentTargetInclusion
          (fun j => iteratedOrderSubdivision (P j) (n j + 1)) f) y := by
  obtain ⟨n,f,e,he,Ha⟩ := exists_orderSigma_order_approximation P Q a.hom
  let D : ι → Type u := fun j => iteratedOrderSubdivision (P j) (n j + 1)
  letI : ∀ j, Fintype (D j) := fun j => iteratedOrderSubdivisionFintype (P j) (n j + 1)
  obtain ⟨c,hc⟩ := exists_orderSigmaCone_homeomorph D P
    (fun j => iteratedOrderSubdivisionHomeomorph (P j) (n j + 1)) e he
  have hp' : IsPushout ((TopCat.isoOfHomeo e).hom ≫ a)
      (SSet.toTop.map (nerveMap (orderSigmaConeEmbedding D).monotone.functor))
      u ((TopCat.isoOfHomeo c).hom ≫ v) := by
    apply hp.of_iso' (TopCat.isoOfHomeo e) (Iso.refl _)
      (TopCat.isoOfHomeo c) (Iso.refl _)
    · simp
    · exact hc
    · simp
    · simp
  obtain ⟨E,hE,hEinv⟩ := exists_orderAttachment_homotopyEquiv
    (orderSigmaConeEmbedding D) (orderSigmaConeEmbedding_isLowerSet D) f
    ((TopCat.isoOfHomeo e).hom ≫ a) u ((TopCat.isoOfHomeo c).hom ≫ v) hp' Ha
  exact ⟨n,f,E,hE,hEinv⟩

end KIP126.Topology.SimplicialRealization
