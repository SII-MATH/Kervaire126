module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Stabilized.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Stability.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Bijective stabilization identifies each chosen cofinal level with
the original stable homotopy group. -/
theorem HasBijectiveStabilization.stableLevelClass_bijective {X : Prespectrum.{u}}
    (hX : HasBijectiveStabilization X) (d : ℤ) (k : ℕ) :
    Function.Bijective (stableLevelClass X d k) := by
  apply (Function.Bijective.of_comp_iff _
    (hX.stableLevelTransition_bijective d 0 k (Nat.zero_le k))).mp
  have he : stableLevelClass X d k ∘ stableLevelTransition X d 0 k (Nat.zero_le k) =
      stableLevelClass X d 0 :=
    funext (fun x => (stableLevelClass_transition X d 0 k (Nat.zero_le k) x).symm)
  rw [he]
  exact hX.stableLevelClass_zero_bijective d

/-- A stable equivalence between actual stabilized prespectra is
bijective on every chosen cofinal level group. -/
theorem Hom.stableLevelHomotopy_bijective_of_stableEquivalence
    {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hX : HasBijectiveStabilization X) (hY : HasBijectiveStabilization Y)
    (hf : stableEquivalences f) (d : ℤ) (k : ℕ) :
    Function.Bijective (f.levelHomotopy (stableGroupStage d k) (stableGroupDimension d k)) := by
  apply (Function.Bijective.of_comp_iff' (hY.stableLevelClass_bijective d k) _).mp
  have he : stableLevelClass Y d k ∘
        f.levelHomotopy (stableGroupStage d k) (stableGroupDimension d k) =
      stableHomotopyMap f d ∘ stableLevelClass X d k :=
    funext (fun x => (stableLevelClass_natural f d k x).symm)
  rw [he]
  exact (hf d).comp (hX.stableLevelClass_bijective d k)

/-- Actual stabilization bijections propagate a later level comparison
back to an earlier level, including cubical dimensions zero and one. -/
theorem Hom.levelHomotopy_bijective_before {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hX : HasBijectiveStabilization X) (hY : HasBijectiveStabilization Y)
    (k n r : ℕ) (hf : Function.Bijective (f.levelHomotopy (n+k) (r+k))) :
    Function.Bijective (f.levelHomotopy n r) := by
  induction k generalizing n r with
  | zero => exact hf
  | succ k ih =>
    have hs : Function.Bijective (f.levelHomotopy (n+1) (r+1)) :=
      ih (n+1) (r+1) (by
        rw [show n+1+k = n+(k+1) by omega,show r+1+k = r+(k+1) by omega]
        exact hf)
    apply (Function.Bijective.of_comp_iff' (hY n r) _).mp
    have he : stabilizeHomotopy Y n r ∘ f.levelHomotopy n r =
        f.levelHomotopy (n+1) (r+1) ∘ stabilizeHomotopy X n r :=
      funext (fun x => (f.levelHomotopy_stabilize n r x).symm)
    rw [he]
    exact hs.comp (hX n r)

/-- A stable equivalence between actual stabilized prespectra induces
bijections at every original level and every based cubical dimension. -/
theorem Hom.levelHomotopy_bijective_of_stableEquivalence
    {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hX : HasBijectiveStabilization X) (hY : HasBijectiveStabilization Y)
    (hf : stableEquivalences f) (n r : ℕ) :
    Function.Bijective (f.levelHomotopy n r) := by
  let d : ℤ := (r : ℤ) - n
  let k := stableGroupStage d 0
  have hn : n + k = stableGroupStage d n := by simp only [k,stableGroupStage]; omega
  have hr : r + k = stableGroupDimension d n := by
    have hd := stableGroup_degree d n
    dsimp only [k,stableGroupStage,stableGroupDimension,d] at *
    omega
  apply f.levelHomotopy_bijective_before hX hY k n r
  rw [hn,hr]
  exact f.stableLevelHomotopy_bijective_of_stableEquivalence hX hY hf d n

end KIP126.StableHomotopy.Implementation.Prespectrum
