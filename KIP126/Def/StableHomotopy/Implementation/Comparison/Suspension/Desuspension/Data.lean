module

public import KIP126.Def.StableHomotopy.Implementation.Comparison.Suspension.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Completion.Functor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Stable.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation
open CategoryTheory MonoidalCategory KIP126.StableHomotopy.Cohomology
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : Mod2EilenbergMacLane (C := C)}

/-- Both actual maps in the rotation zigzag stay invertible after the
specified HF₂ reflection. -/
noncomputable def completedSuspensionDesuspensionIso (X : Prespectrum.{0}) :
    completedLocalization.obj X.desuspension.suspension ≅ completedLocalization.obj X := by
  let f := Prespectrum.suspensionDesuspensionComparison X
  letI : IsIso (completedLocalization.map f.sourceProjection) :=
    completedLocalization_map_isIso_of_stableEquivalence _ f.sourceProjection_stableEquivalence
  letI : IsIso (completedLocalization.map f.targetProjection) :=
    completedLocalization_map_isIso_of_stableEquivalence _
      (Prespectrum.suspensionDesuspensionComparison_targetProjection_stableEquivalence X)
  exact (asIso (completedLocalization.map f.sourceProjection)).symm ≪≫
    asIso (completedLocalization.map f.targetProjection)

/-- Recognition of negative source HF₂ shifts from the proved geometric
suspension/desuspension zigzag and the specified suspension comparison. -/
noncomputable def SourceComparison.hf2_iterateDesuspensionIso (S : SourceComparison H) :
    ∀ k : ℕ, S.equivalence.functor.obj
      (completedLocalization.obj ((Prespectrum.desuspension^[k]) sourceHF2.spectrum)) ≅ H.HF2⟦-(k : ℤ)⟧
  | 0 => S.hf2Iso ≪≫ (shiftFunctorZero C ℤ).symm.app H.HF2
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      let Y := (Prespectrum.desuspension^[k]) sourceHF2.spectrum
      have hY : Y.desuspension.IsWellBased :=
        Prespectrum.desuspension_isWellBased (sourceHF2_iterate_desuspension_wellBased k)
      let ei := (S.suspension Y.desuspension hY).symm ≪≫
        S.equivalence.functor.mapIso (completedSuspensionDesuspensionIso Y) ≪≫
          S.hf2_iterateDesuspensionIso k
      exact (shiftShiftNeg (S.equivalence.functor.obj (completedLocalization.obj Y.desuspension))
          (1 : ℤ)).symm ≪≫
        (shiftFunctor C (-1 : ℤ)).mapIso ei ≪≫
        ((shiftFunctorAdd' C (-(k : ℤ)) (-1 : ℤ) (-((k + 1 : ℕ) : ℤ)) (by omega)).symm.app H.HF2)

/-- Every actual integer source HF₂ test object is recognized as the
corresponding target shift, with no added source-comparison premise. -/
noncomputable def SourceComparison.hf2_sourceShiftIso (S : SourceComparison H) (d : ℤ) :
    S.equivalence.functor.obj (completedLocalization.obj
      (if 0 ≤ d then (Prespectrum.suspension^[d.toNat]) sourceHF2.spectrum
      else (Prespectrum.desuspension^[(-d).toNat]) sourceHF2.spectrum)) ≅ H.HF2⟦d⟧ := by
  split_ifs with hd
  · have h : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd
    exact S.hf2_iterateSuspensionIso d.toNat ≪≫
      eqToIso (congrArg (fun a : ℤ => H.HF2⟦a⟧) h)
  · have h : -(((-d).toNat : ℕ) : ℤ) = d := by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -d)]
      omega
    exact S.hf2_iterateDesuspensionIso (-d).toNat ≪≫ eqToIso (congrArg (fun a : ℤ => H.HF2⟦a⟧) h)

end KIP126.StableHomotopy.Implementation
