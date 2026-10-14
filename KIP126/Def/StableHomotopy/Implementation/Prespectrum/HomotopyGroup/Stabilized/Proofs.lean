module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Stabilized.Predicates
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

universe u

set_option backward.isDefEq.respectTransparency false

theorem HasBijectiveStabilization.stableLevelTransition_bijective {X : Prespectrum.{u}}
    (hX : HasBijectiveStabilization X) (d : ℤ) (i k : ℕ) (h : i ≤ k) :
    Function.Bijective (stableLevelTransition X d i k h) := by
  induction h with
  | refl => rw [stableLevelTransition_self]; exact Function.bijective_id
  | @step k h ih =>
    rw [stableLevelTransition_succ X d h]
    exact (hX (stableGroupStage d k) (stableGroupDimension d k)).comp ih

/-- Bijective stabilization identifies the original stable quotient with
one fixed cofinal level, without any family-dependent choice of later stage. -/
theorem HasBijectiveStabilization.stableLevelClass_zero_bijective {X : Prespectrum.{u}}
    (hX : HasBijectiveStabilization X) (d : ℤ) :
    Function.Bijective (stableLevelClass X d 0) := by
  constructor
  · intro p q h
    have hc := congrArg (stableGroupCode X d) h
    rw [stableGroupCode_levelClass,stableGroupCode_levelClass] at hc
    obtain ⟨k,hp,hq,hpq⟩ := Quotient.exact hc
    exact (hX.stableLevelTransition_bijective d 0 k hp).injective hpq
  · intro x
    obtain ⟨k,p,_,hp,_⟩ := exists_stableLevelClass_pair X d x x
    obtain ⟨q,hq⟩ := (hX.stableLevelTransition_bijective d 0 k (Nat.zero_le k)).surjective p
    refine ⟨q, ?_⟩
    exact (stableLevelClass_transition X d 0 k (Nat.zero_le k) q).trans
      ((congrArg (stableLevelClass X d k) hq).trans hp.symm)

end KIP126.StableHomotopy.Implementation.Prespectrum
