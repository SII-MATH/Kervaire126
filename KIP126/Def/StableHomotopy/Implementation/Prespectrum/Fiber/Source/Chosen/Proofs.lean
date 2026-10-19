module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Chosen.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Shift.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Homological.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- The specified fiber uses an actual distinguished triangle. -/
theorem sourceChosenFiberTriangle_distinguished {X Y : SourceCategory.{0}} (f : X ⟶ Y) :
    sourceChosenFiberTriangle f ∈ distTriang SourceCategory :=
  inv_rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished f)

/-- The adjacent original degree controls injectivity of the actual fiber inclusion. -/
theorem sourceChosenFiberInclusion_homotopy_injective {X Y : SourceCategory.{0}} (f : X ⟶ Y)
    (d : ℤ) (hf : Function.Surjective ((sourceStableHomotopyAddFunctor (d+1)).map f)) :
    Function.Injective ((sourceStableHomotopyAddFunctor d).map (sourceChosenFiberInclusion f)) := by
  let F := sourceStableHomotopyAddFunctor d
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT : T ∈ distTriang SourceCategory := HasFunctorialCofiber.cofib_distinguished f
  have hs : Function.Surjective (F.map (f⟦(-1 : ℤ)⟧')) :=
    sourceStableHomotopy_map_shift_surjective f d (-1) (by
      rw [show d - (-1) = d+1 by omega]
      exact hf)
  haveI : Epi (F.map (f⟦(-1 : ℤ)⟧')) := (AddCommGrpCat.epi_iff_surjective _).mpr hs
  have hz : F.map (T.mor₂⟦(-1 : ℤ)⟧') = 0 := by
    apply (cancel_epi (F.map (f⟦(-1 : ℤ)⟧'))).mp
    rw [comp_zero, ← F.map_comp, ← Functor.map_comp]
    change F.map ((shiftFunctor SourceCategory (-1)).map (T.mor₁ ≫ T.mor₂)) = 0
    rw [comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero, F.map_zero]
  have hzprev : F.map T.invRotate.invRotate.mor₁ = 0 := by
    simp only [Triangle.invRotate_mor₁, Triangle.invRotate_mor₃,
      Functor.map_comp, Functor.map_neg, hz, zero_comp, neg_zero]
  haveI : Mono (F.map T.invRotate.invRotate.mor₂) :=
    (F.map_distinguished_exact T.invRotate.invRotate
      (inv_rot_of_distTriang _ (inv_rot_of_distTriang T hT))).mono_g hzprev
  exact (AddCommGrpCat.mono_iff_injective (F.map T.invRotate.invRotate.mor₂)).mp inferInstance

end KIP126.StableHomotopy.Implementation
