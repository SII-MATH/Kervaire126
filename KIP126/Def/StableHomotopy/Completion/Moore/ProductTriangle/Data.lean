module

public import KIP126.Def.StableHomotopy.Completion.Moore.Data
public import KIP126.Def.StableHomotopy.Completion.Moore.ScalarInverse.Data
public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Constant.Data

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The actual distinguished cofiber triangle at a Moore tower stage. -/
noncomputable def moorePowerTriangle (p : ℕ) (X : C) (k : ℕ) : Triangle C :=
  Triangle.mk (moorePowerMap p X k)
    (HasFunctorialCofiber.cofibι (moorePowerMap p X k))
    (HasFunctorialCofiber.cofibδ (moorePowerMap p X k))

/-- Reduction is a morphism of the actual stage triangles, with scalar
transition on the first term and identity transition on the second. -/
noncomputable def moorePowerTriangleStep (p : ℕ) (X : C) (k : ℕ) :
    moorePowerTriangle p X (k + 1) ⟶ moorePowerTriangle p X k where
  hom₁ := p • 𝟙 X
  hom₂ := 𝟙 X
  hom₃ := (moorePowerSequence p X).step k
  comm₁ := by
    change moorePowerMap p X (k + 1) ≫ 𝟙 X =
      (p • 𝟙 X) ≫ moorePowerMap p X k
    simp only [moorePowerMap, Category.comp_id,
      Preadditive.nsmul_comp, Category.id_comp, smul_smul, pow_succ']
  comm₂ := (HasFunctorialCofiber.cofibMap_ι _ _ _ _ _).symm
  comm₃ := (HasFunctorialCofiber.cofibMap_δ _ _ _ _ _).symm

variable [HasProductsOfShape ℕ C]

/-- The product of the specified Moore stage triangles. -/
noncomputable def mooreProductTriangle (p : ℕ) (X : C) : Triangle C :=
  productTriangle (moorePowerTriangle p X)

/-- The inverse-sequence shift on the product triangle, including all
three commutative squares. -/
noncomputable def mooreProductTriangleShift (p : ℕ) (X : C) :
    mooreProductTriangle p X ⟶ mooreProductTriangle p X :=
  productTriangle.lift _ (fun k =>
    productTriangle.π _ (k + 1) ≫ moorePowerTriangleStep p X k)

/-- The difference map is a genuine morphism of product triangles. -/
noncomputable def mooreProductTriangleDifference (p : ℕ) (X : C) :
    mooreProductTriangle p X ⟶ mooreProductTriangle p X :=
  𝟙 _ - mooreProductTriangleShift p X

end KIP126.StableHomotopy
