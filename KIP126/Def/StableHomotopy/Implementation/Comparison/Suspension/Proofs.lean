module

public import KIP126.Def.StableHomotopy.Implementation.Comparison
public import KIP126.Def.StableHomotopy.Implementation.Completion.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory MonoidalCategory KIP126.StableHomotopy.Cohomology

/-- Iterated levelwise suspension preserves the supplied good models of
the actual source HF₂ spectrum. -/
theorem sourceHF2_iterate_suspension_good (k : ℕ) :
    ∀ n, (((Prespectrum.suspension^[k]) sourceHF2.spectrum).level n).IsGood := by
  induction k with
  | zero => exact sourceHF2.good
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      intro n
      exact BasedSpace.good_suspension (ih n)

universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)}

/-- Recognition of the actual iterated source HF₂ suspensions by the
selected target shifts, constructed from the single-suspension comparison. -/
noncomputable def SourceComparison.hf2_iterateSuspensionIso (S : SourceComparison H) :
    ∀ k : ℕ, S.equivalence.functor.obj
      (completedLocalization.obj ((Prespectrum.suspension^[k]) sourceHF2.spectrum)) ≅ H.HF2⟦(k : ℤ)⟧
  | 0 => S.hf2Iso ≪≫ (shiftFunctorZero C ℤ).symm.app H.HF2
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact S.suspension _ (fun n => (sourceHF2_iterate_suspension_good k n).2.1) ≪≫
        (shiftFunctor C (1 : ℤ)).mapIso (S.hf2_iterateSuspensionIso k) ≪≫
        ((shiftFunctorAdd' C (k : ℤ) (1 : ℤ) ((k + 1 : ℕ) : ℤ) (by omega)).symm.app H.HF2)

theorem Prespectrum.desuspension_isWellBased {X : Prespectrum.{u}} (hX : X.IsWellBased) :
    X.desuspension.IsWellBased := by
  intro n
  cases n with
  | zero =>
      constructor
      · change IsClosed ({PUnit.unit} : Set PUnit)
        exact isClosed_discrete _
      · intro Y f p hp
        refine ⟨⟨fun z => p z.2, p.continuous.comp continuous_snd⟩, ?_, ?_⟩
        · intro x
          cases x
          exact hp
        · intro t
          rfl
  | succ n => exact hX n

theorem sourceHF2_iterate_desuspension_wellBased (k : ℕ) :
    ((Prespectrum.desuspension^[k]) sourceHF2.spectrum).IsWellBased := by
  induction k with
  | zero => exact fun n => (sourceHF2.good n).2.1
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Prespectrum.desuspension_isWellBased ih

end KIP126.StableHomotopy.Implementation
