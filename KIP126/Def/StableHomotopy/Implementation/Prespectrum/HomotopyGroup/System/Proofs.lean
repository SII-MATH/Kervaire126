module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.System.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

universe u

@[simp] theorem stableGroup_degree (d : ℤ) (k : ℕ) :
    (stableGroupDimension d k : ℤ) = d + stableGroupStage d k := by
  unfold stableGroupDimension stableGroupStage
  omega

@[simp] theorem stableLevelTransition_self (X : Prespectrum.{u}) (d : ℤ) (i : ℕ) :
    stableLevelTransition X d i i le_rfl = MonoidHom.id _ := by
  exact Nat.leRec_self _ _

theorem stableLevelTransition_succ (X : Prespectrum.{u}) (d : ℤ)
    {i j : ℕ} (h : i ≤ j) :
    stableLevelTransition X d i (j + 1) (Nat.le_succ_of_le h) =
      (stableLevelBond X d j).comp (stableLevelTransition X d i j h) := by
  exact Nat.leRec_succ _ _ h

theorem stableLevelTransition_comp (X : Prespectrum.{u}) (d : ℤ)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (stableLevelTransition X d j k hjk).comp (stableLevelTransition X d i j hij) =
      stableLevelTransition X d i k (hij.trans hjk) := by
  induction hjk with
  | refl => simp
  | @step k h ih =>
    rw [stableLevelTransition_succ X d h,
      stableLevelTransition_succ X d (hij.trans h)]
    rw [MonoidHom.comp_assoc, ih]

instance (X : Prespectrum.{u}) (d : ℤ) :
    DirectedSystem (stableLevelGroup X d) (fun i j h => stableLevelTransition X d i j h) where
  map_self {i} x := by rw [stableLevelTransition_self]; rfl
  map_map {k j i} hij hjk x := DFunLike.congr_fun (stableLevelTransition_comp X d hij hjk) x

end KIP126.StableHomotopy.Implementation.Prespectrum
