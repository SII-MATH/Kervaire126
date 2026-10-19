module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Upper.Cofiber.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Upper.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Homological.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Connectivity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- The original cofiber inclusion kills every stable class at or above the bound. -/
theorem sourceUpperCellKillingUnit_map_eq_zero (X : SourceCategory.{0}) (n d : ℤ) (hd : n ≤ d) :
    (sourceStableHomotopyAddFunctor d).map (sourceUpperCellKillingUnit X n) = 0 := by
  let F := sourceStableHomotopyAddFunctor d
  apply AddCommGrpCat.ext
  intro x
  obtain ⟨a,rfl⟩ := sourceUpperSphereCoverMap_surjective X n d hd x
  change (F.map (sourceUpperSphereCoverMap X n) ≫ F.map (sourceUpperCellKillingUnit X n)) a = 0
  rw [← F.map_comp, show sourceUpperSphereCoverMap X n ≫ sourceUpperCellKillingUnit X n = 0 from
    comp_distTriang_mor_zero₁₂ _ (HasFunctorialCofiber.cofib_distinguished (sourceUpperSphereCoverMap X n)),
    F.map_zero]
  rfl

/-- In lower degrees the same actual inclusion induces a bijection. -/
theorem sourceUpperCellKillingUnit_bijective (X : SourceCategory.{0}) (n d : ℤ) (hd : d < n) :
    Function.Bijective ((sourceStableHomotopyAddFunctor d).map (sourceUpperCellKillingUnit X n)) := by
  let F := sourceStableHomotopyAddFunctor d
  let A := sourceUpperSphereCover X n
  let T := Triangle.mk (sourceUpperSphereCoverMap X n) (sourceUpperCellKillingUnit X n)
    (HasFunctorialCofiber.cofibδ (sourceUpperSphereCoverMap X n))
  have hT : T ∈ distTriang SourceCategory :=
    HasFunctorialCofiber.cofib_distinguished (sourceUpperSphereCoverMap X n)
  letI : Subsingleton (F.obj A) := sourceUpperSphereCover_homotopy_subsingleton X n d hd
  have hz₁ : F.map T.mor₁ = 0 := (AddCommGrpCat.isZero_of_subsingleton (F.obj A)).eq_of_src _ _
  letI := sourceUpperSphereCover_homotopy_subsingleton X n (d-1) (by omega)
  letI : Subsingleton (Prespectrum.sourceSphere d ⟶
      sourceLocalization.obj (A⟦(1 : ℤ)⟧).as.obj) := by
    change Subsingleton (Prespectrum.sourceSphere d ⟶ A⟦(1 : ℤ)⟧)
    exact sourceSphere_hom_shift_subsingleton A d
  letI : Subsingleton (F.obj (A⟦(1 : ℤ)⟧)) :=
    (Prespectrum.sourceStableHomotopyEquiv (A⟦(1 : ℤ)⟧).as.obj d).injective.subsingleton
  have hz₃ : F.map T.mor₃ = 0 :=
    (AddCommGrpCat.isZero_of_subsingleton (F.obj (A⟦(1 : ℤ)⟧))).eq_of_tgt _ _
  haveI : Mono (F.map T.mor₂) := (F.map_distinguished_exact T hT).mono_g hz₁
  haveI : Epi (F.map T.mor₂) :=
    (F.map_distinguished_exact T.rotate (rot_of_distTriang T hT)).epi_f hz₃
  exact ⟨(AddCommGrpCat.mono_iff_injective (F.map T.mor₂)).mp inferInstance,
    (AddCommGrpCat.epi_iff_surjective (F.map T.mor₂)).mp inferInstance⟩

end KIP126.StableHomotopy.Implementation
