module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Upper.Cofiber.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Upper.Orthogonality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

private theorem second_precomp_bijective (T : Triangle SourceCategory.{0})
    (hT : T ∈ distTriang SourceCategory) (Y : SourceCategory.{0})
    (h₀ : Subsingleton (T.obj₁ ⟶ Y)) (h₁ : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ Y)) :
    Function.Bijective (fun a : T.obj₃ ⟶ Y => T.mor₂ ≫ a) := by
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    obtain ⟨z,hz⟩ := T.yoneda_exact₃ hT (a-b) (by
      change T.mor₂ ≫ a = T.mor₂ ≫ b at hab
      rw [Preadditive.comp_sub,hab,sub_self])
    rw [h₁.elim z 0,comp_zero] at hz
    exact hz
  · intro a
    obtain ⟨b,hb⟩ := T.yoneda_exact₂ hT a (h₀.elim _ _)
    exact ⟨b,hb.symm⟩

/-- Cell killing is invisible to actual maps into any object vanishing
in the upper stable degrees. -/
theorem sourceUpperCellKillingUnit_precomp_bijective (X : SourceCategory.{0}) (n : ℤ)
    (Y : SourceCategory.{0})
    (hY : ∀ d, n ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y)) :
    Function.Bijective (fun a : sourceUpperCellKilling X n ⟶ Y =>
      sourceUpperCellKillingUnit X n ≫ a) :=
  second_precomp_bijective _
    (HasFunctorialCofiber.cofib_distinguished (sourceUpperSphereCoverMap X n)) Y
    (sourceUpperSphereCover_hom_subsingleton X n Y hY)
    (sourceUpperSphereCover_shift_hom_subsingleton X n 1 (by omega) Y hY)

/-- The shifted cell-killing unit has the same actual extension property,
which supplies the adjacent degree needed for the Milnor uniqueness term. -/
theorem sourceUpperCellKillingUnit_shift_precomp_bijective (X : SourceCategory.{0}) (n : ℤ)
    (Y : SourceCategory.{0})
    (hY : ∀ d, n ≤ d → Subsingleton ((sourceStableHomotopyAddFunctor d).obj Y)) :
    Function.Bijective (fun a : (sourceUpperCellKilling X n)⟦(1 : ℤ)⟧ ⟶ Y =>
      (sourceUpperCellKillingUnit X n)⟦(1 : ℤ)⟧' ≫ a) := by
  let A := sourceUpperSphereCover X n
  let T := Triangle.mk (sourceUpperSphereCoverMap X n) (sourceUpperCellKillingUnit X n)
    (HasFunctorialCofiber.cofibδ (sourceUpperSphereCoverMap X n))
  let T' := (shiftFunctor (Triangle SourceCategory) (1 : ℤ)).obj T
  have hT' : T' ∈ distTriang SourceCategory :=
    T.shift_distinguished (HasFunctorialCofiber.cofib_distinguished (sourceUpperSphereCoverMap X n)) 1
  have h₀ : Subsingleton (T'.obj₁ ⟶ Y) :=
    sourceUpperSphereCover_shift_hom_subsingleton X n 1 (by omega) Y hY
  have h₁ : Subsingleton (T'.obj₁⟦(1 : ℤ)⟧ ⟶ Y) := by
    letI := sourceUpperSphereCover_shift_hom_subsingleton X n 2 (by omega) Y hY
    let e : (A⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ A⟦(2 : ℤ)⟧ :=
      (shiftFunctorAdd SourceCategory (1 : ℤ) 1).symm.app A
    exact (Iso.homCongr e (Iso.refl Y)).injective.subsingleton
  have h := second_precomp_bijective T' hT' Y h₀ h₁
  have hneg : Function.Bijective (fun a : (sourceUpperCellKilling X n)⟦(1 : ℤ)⟧ ⟶ Y =>
      -((sourceUpperCellKillingUnit X n)⟦(1 : ℤ)⟧' ≫ a)) := by
    change Function.Bijective (fun a : (sourceUpperCellKilling X n)⟦(1 : ℤ)⟧ ⟶ Y =>
      ((1 : ℤ).negOnePow • (sourceUpperCellKillingUnit X n)⟦(1 : ℤ)⟧') ≫ a) at h
    simpa only [Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.neg_comp] using h
  constructor
  · intro a b hab
    apply hneg.injective
    exact congrArg Neg.neg hab
  · intro b
    obtain ⟨a,ha⟩ := hneg.surjective (-b)
    exact ⟨a,neg_injective ha⟩

end KIP126.StableHomotopy.Implementation
