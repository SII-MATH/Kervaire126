module

public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Data

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits

universe u v

section Tower

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasFunctorialCofiber (C := C)]

/-- Multiplication by the specified scalar power on an actual object. -/
noncomputable def moorePowerMap (p : ℕ) (X : C) (k : ℕ) : X ⟶ X :=
  p ^ k • 𝟙 X

/-- The Moore tower uses the specified cofibers and the reduction maps
induced by multiplication by `p` on the source and the identity on the target. -/
noncomputable def moorePowerSequence (p : ℕ) (X : C) : InverseSequence C where
  obj k := HasFunctorialCofiber.cofib (moorePowerMap p X k)
  step k := HasFunctorialCofiber.cofibMap (moorePowerMap p X (k + 1))
    (moorePowerMap p X k) (p • 𝟙 X) (𝟙 X) (by
      simp only [moorePowerMap, Preadditive.nsmul_comp, Category.id_comp,
        Category.comp_id, smul_smul, pow_succ'])

end Tower

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]

/-- The scalar-adic Moore completion candidate, constructed by a Milnor
homotopy limit. Identifying it with a specified localization is a further theorem. -/
noncomputable def mooreCompletion (p : ℕ) (X : C) : C :=
  (moorePowerSequence p X).homotopyLimit

end KIP126.StableHomotopy
