import KIP126.Def.Synthetic.Bockstein.Layer.Zero.Raw.Proofs
import KIP126.Def.StableHomotopy.Context.CofiberMap.Iso.Data

/-! The zeroth residual layer is identified with the first lambda quotient
through the actual chosen cofiber map of the specified isomorphism square. -/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The cofiber map of the actual residual-step to first-power square. -/
noncomputable def layerZeroMap (A : Syn) :
    (lambdaTower A).layer 0 ⟶ XModLambdaN A 1 :=
  HasFunctorialCofiber.cofibMap ((lambdaTower A).step 0) (lambdaPow 1 A)
    (layerZeroSourceIso A).hom (layerZeroTargetIso A).hom (layerZeroSquare A)

/-- The same map is an iso because both first two triangle components are
the specified isomorphisms. No independent cofiber identification is chosen. -/
noncomputable def layerZeroIso (A : Syn) :
    (lambdaTower A).layer 0 ≅ XModLambdaN A 1 :=
  cofiberMapIso ((lambdaTower A).step 0) (lambdaPow 1 A)
    (layerZeroSourceIso A).hom (layerZeroTargetIso A).hom (layerZeroSquare A)

end KIP126.Synthetic.Bockstein
