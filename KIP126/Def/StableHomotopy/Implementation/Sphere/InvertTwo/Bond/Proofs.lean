module

public import KIP126.Def.StableHomotopy.Implementation.Completion
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.System

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

set_option backward.isDefEq.respectTransparency false

theorem BasedSpace.doubleSuspension_projection (A : BasedSpace.{0}) (a : A) (t : I) :
    (doubleSuspension A).map (suspensionProjection A (a,t)) =
      suspensionProjection A (a,doubleInterval t) :=
  (doubleSuspension_exists A).exists.choose_spec a t

/-- The actual doubled sphere bond traverses the suspended cube twice in
its new first coordinate. This is an equality of actual based cubes. -/
theorem Prespectrum.sphereInvertTwo_stabilizeLoop (n r : ℕ)
    (p : GenLoop (Fin r) (sphereLevel n) (sphereLevel n).point) :
    stabilizeLoop sphereInvertTwo n r p =
      GenLoop.transAt 0 (stabilizeLoop sphere n r p) (stabilizeLoop sphere n r p) := by
  apply GenLoop.ext
  intro t
  have ht (a : I) : (fun j : Fin r => (Function.update t 0 a) j.succ) =
      (fun j : Fin r => t j.succ) := by
    funext j
    exact Function.update_of_ne (Fin.succ_ne_zero j) a t
  change (BasedSpace.doubleSuspension (sphereLevel n)).map
    (BasedSpace.suspensionProjection (sphereLevel n) (p (fun j => t j.succ),t 0)) = _
  rw [BasedSpace.doubleSuspension_projection]
  change _ = if (t 0 : ℝ) ≤ 1/2 then
    (stabilizeLoop sphere n r p)
      (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ))))
    else (stabilizeLoop sphere n r p)
      (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ) - 1)))
  split_ifs with h
  · change BasedSpace.suspensionProjection (sphereLevel n)
        (p (fun j => t j.succ),BasedSpace.doubleInterval (t 0)) =
      BasedSpace.suspensionProjection (sphereLevel n)
        (p (fun j => (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ)))) j.succ),
          (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ)))) 0)
    rw [ht, Function.update_self]
    congr 1
    congr 1
    have hm : 2 * (t 0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith [(t 0).property.1, (t 0).property.2]
    simp only [BasedSpace.doubleInterval, dif_pos h, Set.projIcc_of_mem _ hm]
  · change BasedSpace.suspensionProjection (sphereLevel n)
        (p (fun j => t j.succ),BasedSpace.doubleInterval (t 0)) =
      BasedSpace.suspensionProjection (sphereLevel n)
        (p (fun j => (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ) - 1))) j.succ),
          (Function.update t 0 (Set.projIcc 0 1 zero_le_one (2 * (t 0 : ℝ) - 1))) 0)
    rw [ht, Function.update_self]
    congr 1
    congr 1
    have hm : 2 * (t 0 : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith [(t 0).property.1, (t 0).property.2]
    simp only [BasedSpace.doubleInterval, dif_neg h, Set.projIcc_of_mem _ hm]

/-- The actual successive homotopy-group bond for the fixed 2-inverted
sphere is the square of the ordinary sphere bond. -/
theorem Prespectrum.sphereInvertTwo_stableLevelBond (d : ℤ) (k : ℕ)
    (x : stableLevelGroup sphereInvertTwo d k) :
    stableLevelBond sphereInvertTwo d k x = (stableLevelBond sphere d k x) ^ 2 := by
  induction x using Quotient.inductionOn with
  | h p =>
    rw [pow_two]
    exact (congrArg Quotient.mk' (sphereInvertTwo_stabilizeLoop
      (stableGroupStage d k) (stableGroupDimension d k) p)).trans
        (_root_.HomotopyGroup.mul_spec (i := (0 : Fin (stableGroupDimension d k + 1)))).symm

end KIP126.StableHomotopy.Implementation
