module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Limit.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Homotopy.Surjective.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Conservativity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- The actual map into the Postnikov limit has exactly the original units
as its Milnor coordinates. -/
@[reassoc (attr := simp)]
theorem sourcePostnikovLimitUnit_projection (X : SourceCategory.{0}) (k : ℕ) :
    sourcePostnikovLimitUnit X ≫ (sourceHomotopyLimitWitness (sourcePostnikovTower X)).π k =
      sourcePostnikovUnit X k :=
  ((sourceHomotopyLimitWitness (sourcePostnikovTower X)).exists_lift
    (fun k => sourcePostnikovUnit X k) (sourcePostnikovTower_unit_step X)).choose_spec k

/-- The actual Milnor projections commute with every cutoff restriction,
not only with adjacent steps. -/
@[reassoc]
theorem sourcePostnikovLimit_projection_restriction
    (X : SourceCategory.{0}) (k l : ℕ) (h : l ≤ k) :
    (sourceHomotopyLimitWitness (sourcePostnikovTower X)).π k ≫
      sourcePostnikovRestriction X k l (by exact_mod_cast h) =
        (sourceHomotopyLimitWitness (sourcePostnikovTower X)).π l := by
  induction k, h using Nat.le_induction with
  | base =>
    rw [sourcePostnikovRestriction_refl]
    exact Category.comp_id _
  | succ k h ih =>
    rw [← sourcePostnikovRestriction_trans X (k+1 : ℕ) k l (by omega) (by exact_mod_cast h),
      ← Category.assoc]
    change ((sourceHomotopyLimitWitness (sourcePostnikovTower X)).π (k+1) ≫
      (sourcePostnikovTower X).step k) ≫ _ = _
    rw [SequentialHomotopyLimit.π_step]
    exact ih

/-- Every original stable homotopy group is recovered by the actual
Postnikov limit. The Milnor ambiguity vanishes by the proved surjectivity
of every tower transition. -/
theorem sourcePostnikovLimitUnit_homotopy_bijective (X : SourceCategory.{0}) (d : ℤ) :
    Function.Bijective ((sourceStableHomotopyAddFunctor d).map (sourcePostnikovLimitUnit X)) := by
  let G := sourceStableHomotopyAddFunctor d
  let H := sourceHomotopyLimitWitness (sourcePostnikovTower X)
  obtain ⟨k, hk⟩ := exists_nat_gt d
  have hcoord (j : ℕ) (x : G.obj X) :
      G.map (H.π j) (G.map (sourcePostnikovLimitUnit X) x) =
        G.map (sourcePostnikovUnit X j) x := by
    change (G.map (sourcePostnikovLimitUnit X) ≫ G.map (H.π j)) x = _
    rw [← G.map_comp, sourcePostnikovLimitUnit_projection]
    rfl
  have hrestrict (m l : ℕ) (h : l ≤ m)
      (z : G.obj (sourceHomotopyLimit (sourcePostnikovTower X))) :
      G.map (sourcePostnikovRestriction X m l (by exact_mod_cast h)) (G.map (H.π m) z) =
        G.map (H.π l) z := by
    change (G.map (H.π m) ≫ G.map (sourcePostnikovRestriction X m l (by exact_mod_cast h))) z = _
    rw [← G.map_comp, sourcePostnikovLimit_projection_restriction X m l h]
    rfl
  have hunit (m l : ℕ) (h : l ≤ m) (x : G.obj X) :
      G.map (sourcePostnikovRestriction X m l (by exact_mod_cast h))
          (G.map (sourcePostnikovUnit X m) x) = G.map (sourcePostnikovUnit X l) x := by
    change (G.map (sourcePostnikovUnit X m) ≫
      G.map (sourcePostnikovRestriction X m l (by exact_mod_cast h))) x = _
    rw [← G.map_comp, sourcePostnikovUnit_restriction]
  constructor
  · intro x y hxy
    apply (sourcePostnikovUnit_homotopy_bijective X k d hk).injective
    exact (hcoord k x).symm.trans ((congrArg (G.map (H.π k)) hxy).trans (hcoord k y))
  · intro z
    obtain ⟨x, hx⟩ := (sourcePostnikovUnit_homotopy_bijective X k d hk).surjective
      (G.map (H.π k) z)
    refine ⟨x, ?_⟩
    apply (sourceHomotopyLimitComparison_injective_of_surjective (sourcePostnikovTower X) d
      (sourcePostnikovTower_homotopy_surjective X (d+1)))
    apply Subtype.ext
    funext l
    change G.map (H.π l) (G.map (sourcePostnikovLimitUnit X) x) = G.map (H.π l) z
    rw [hcoord]
    let m := max k l
    have hkm : k ≤ m := Nat.le_max_left _ _
    have hlm : l ≤ m := Nat.le_max_right _ _
    have hdm : d < (m : ℤ) := lt_of_lt_of_le hk (by exact_mod_cast hkm)
    obtain ⟨y, hy⟩ := (sourcePostnikovUnit_homotopy_bijective X m d hdm).surjective
      (G.map (H.π m) z)
    have hyx : y = x := by
      apply (sourcePostnikovUnit_homotopy_bijective X k d hk).injective
      rw [← hunit m k hkm y, hy, hrestrict m k hkm, hx]
    rw [← hunit m l hlm x, ← hyx, hy, hrestrict m l hlm]

/-- Every actual source object is recovered by the homotopy limit of
its constructed Postnikov tower, with the stated original unit maps. -/
instance sourcePostnikovLimitUnit_isIso (X : SourceCategory.{0}) :
    IsIso (sourcePostnikovLimitUnit X) := by
  apply (source_isIso_iff_stableHomotopy_bijective _).mpr
  intro d
  rw [← sourceStableHomotopyAddFunctor_forget_map]
  exact sourcePostnikovLimitUnit_homotopy_bijective X d

end KIP126.StableHomotopy.Implementation
