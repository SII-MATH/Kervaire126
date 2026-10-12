module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Layer.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Tower.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Source.Chosen.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- The actual layer inclusion is injective on every original stable group. -/
theorem sourcePostnikovLayerInclusion_homotopy_injective (X : SourceCategory.{0}) (n d : ℤ) :
    Function.Injective ((sourceStableHomotopyAddFunctor d).map (sourcePostnikovLayerInclusion X n)) :=
  sourceChosenFiberInclusion_homotopy_injective _ d
    (sourcePostnikovRestriction_homotopy_surjective X (n+1) n (d+1) (by omega))

/-- The actual layer has no original stable homotopy outside its specified degree. -/
theorem sourcePostnikovLayer_homotopy_subsingleton (X : SourceCategory.{0}) (n d : ℤ)
    (hd : d ≠ n) : Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourcePostnikovLayer X n)) := by
  let F := sourceStableHomotopyAddFunctor d
  let f := sourcePostnikovRestriction X (n+1) n (by omega)
  let T := sourceChosenFiberTriangle f
  have hT := sourceChosenFiberTriangle_distinguished f
  have hi := sourcePostnikovLayerInclusion_homotopy_injective X n d
  by_cases hdn : d < n
  · have hf : Function.Injective (F.map f) := by
      intro a b hab
      obtain ⟨x,rfl⟩ := (sourcePostnikovUnit_homotopy_bijective X (n+1) d (by omega)).surjective a
      obtain ⟨y,rfl⟩ := (sourcePostnikovUnit_homotopy_bijective X (n+1) d (by omega)).surjective b
      change (F.map (sourcePostnikovUnit X (n+1)) ≫ F.map f) x =
        (F.map (sourcePostnikovUnit X (n+1)) ≫ F.map f) y at hab
      rw [← F.map_comp, sourcePostnikovUnit_restriction] at hab
      exact congrArg _ ((sourcePostnikovUnit_homotopy_bijective X n d hdn).injective hab)
    have hz : F.map T.mor₁ = 0 := by
      haveI : Mono (F.map T.mor₂) := (AddCommGrpCat.mono_iff_injective _).mpr hf
      apply (cancel_mono (F.map T.mor₂)).mp
      rw [zero_comp, ← F.map_comp, comp_distTriang_mor_zero₁₂ T hT, F.map_zero]
    refine ⟨fun a b => hi ?_⟩
    change (F.map T.mor₁) a = (F.map T.mor₁) b
    rw [hz]
    rfl
  · letI := sourcePostnikovTruncation_homotopy_subsingleton X (n+1) d (by omega)
    exact hi.subsingleton

/-- In its only possible nonzero degree, the actual inclusion induces a bijection
onto the truncation group identified with the original group by its unit. -/
theorem sourcePostnikovLayerInclusion_homotopy_bijective (X : SourceCategory.{0}) (n : ℤ) :
    Function.Bijective ((sourceStableHomotopyAddFunctor n).map (sourcePostnikovLayerInclusion X n)) := by
  let F := sourceStableHomotopyAddFunctor n
  let f := sourcePostnikovRestriction X (n+1) n (by omega)
  let T := sourceChosenFiberTriangle f
  letI := sourcePostnikovTruncation_homotopy_subsingleton X n n (le_refl n)
  have hz : F.map T.mor₂ = 0 :=
    (AddCommGrpCat.isZero_of_subsingleton (F.obj (sourcePostnikovTruncation X n))).eq_of_tgt _ _
  haveI : Epi (F.map T.mor₁) :=
    (F.map_distinguished_exact T (sourceChosenFiberTriangle_distinguished f)).epi_f hz
  exact ⟨sourcePostnikovLayerInclusion_homotopy_injective X n n,
    (AddCommGrpCat.epi_iff_surjective (F.map T.mor₁)).mp inferInstance⟩

end KIP126.StableHomotopy.Implementation
