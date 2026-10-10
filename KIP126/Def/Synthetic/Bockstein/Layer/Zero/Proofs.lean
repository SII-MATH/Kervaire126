import KIP126.Def.Synthetic.Bockstein.Layer.Zero.Data

/-! The same actual inclusion and boundary squares for the zeroth layer
identification. These formulas retain both endpoint identifications. -/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

@[simp] theorem layerZeroIso_hom (A : Syn) :
    (layerZeroIso A).hom = layerZeroMap A := rfl

/-- The layer inclusion and the quotient inclusion agree through the
specified zero-shift target map. -/
theorem layerZeroIso_incl (A : Syn) :
    (lambdaTower A).layerIncl 0 ≫ (layerZeroIso A).hom =
      (layerZeroTargetIso A).hom ≫ XModLambdaN.incl A 1 :=
  (HasFunctorialCofiber.cofibMap_ι ((lambdaTower A).step 0) (lambdaPow 1 A)
    (layerZeroSourceIso A).hom (layerZeroTargetIso A).hom (layerZeroSquare A)).symm

/-- The connecting arrows agree after shifting the actual source
identification; no sign or suspension comparison is suppressed. -/
theorem layerZeroIso_boundary (A : Syn) :
    (layerZeroIso A).hom ≫ XModLambdaN.proj A 1 =
      (lambdaTower A).layerBoundary 0 ≫ (layerZeroSourceIso A).hom⟦(1 : ℤ)⟧' :=
  HasFunctorialCofiber.cofibMap_δ ((lambdaTower A).step 0) (lambdaPow 1 A)
    (layerZeroSourceIso A).hom (layerZeroTargetIso A).hom (layerZeroSquare A)

end KIP126.Synthetic.Bockstein
