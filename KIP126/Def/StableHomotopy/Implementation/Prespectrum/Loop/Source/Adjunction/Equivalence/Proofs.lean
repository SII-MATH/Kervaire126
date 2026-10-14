module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Adjunction.Equivalence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The original strict suspension-loop unit becomes invertible, retaining
the exact point-set map through both localization comparison isomorphisms. -/
theorem source_suspensionLoopCurry_id_isIso (X : Prespectrum.{u}) :
    IsIso (sourceLocalization.map (suspensionLoopCurry (𝟙 X.suspension))) := by
  letI : CatCommSq suspensionFunctor sourceLocalization sourceLocalization sourceSuspensionFunctor :=
    ⟨eqToIso (Localization.Construction.fac _ _).symm⟩
  letI : CatCommSq loopFunctor sourceLocalization sourceLocalization sourceLoopFunctor :=
    ⟨eqToIso sourceLoopFunctor_fac.symm⟩
  let e := (CatCommSq.iso loopFunctor sourceLocalization sourceLocalization sourceLoopFunctor).app
      (suspensionFunctor.obj X) ≪≫ sourceLoopFunctor.mapIso
        ((CatCommSq.iso suspensionFunctor sourceLocalization sourceLocalization sourceSuspensionFunctor).app X)
  have he : sourceLocalization.map (suspensionLoopCurry (𝟙 X.suspension)) ≫ e.hom =
      sourceSuspensionLoopAdjunction.unit.app (sourceLocalization.obj X) := by
    rw [sourceSuspensionLoopAdjunction, Adjunction.localization_unit_app]
    rfl
  exact IsIso.of_isIso_fac_right he

/-- The original point-set suspension-loop unit is a stable equivalence
for every prespectrum, without any condition on its level spaces. -/
theorem suspensionLoopCurry_id_stableEquivalence (X : Prespectrum.{u}) :
    stableEquivalences (suspensionLoopCurry (𝟙 X.suspension)) :=
  (stableEquivalence_iff_source_isIso _).mpr (source_suspensionLoopCurry_id_isIso X)

end KIP126.StableHomotopy.Implementation.Prespectrum
