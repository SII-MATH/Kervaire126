import KIP126.Def.StableHomotopy.Implementation.Generators

/-! A genuine sequential model of the derived smash. The even level 2n is
Xₙ∧Yₙ, and the intervening odd level is its suspension. Thus both suspension
coordinates are accounted for; Xₙ∧Yₙ is never incorrectly put in level n.
All point-set maps are fixed on quotient representatives. -/
namespace KIP126.StableHomotopy.Implementation
open CategoryTheory Topology
open scoped unitInterval
namespace Prespectrum

/-- Levelwise compactly generated, well-based objects of based CW homotopy type. -/
def IsGood (X : Prespectrum.{0}) : Prop := ∀ n, (X.level n).IsGood

theorem IsGood.wellBased {X : Prespectrum.{0}} (hX : X.IsGood) : X.IsWellBased :=
  fun n => (hX n).2.1

/-- These objects cover the entire ordinary stable localization. -/
theorem goodReplacement (X : Prespectrum.{0}) :
    ∃ (Y : Prespectrum.{0}) (_ : Y.IsGood) (q : Y ⟶ X), stableEquivalences q := by sorry

def tail (X : Prespectrum.{0}) : Prespectrum.{0} where
  level n := X.level (n+1)
  bond n := X.bond (n+1)
  bond_point n := X.bond_point (n+1)
  bond_zero n := X.bond_zero (n+1)
  bond_one n := X.bond_one (n+1)

def tailMap {X Y : Prespectrum.{0}} (f : X ⟶ Y) : X.tail ⟶ Y.tail where
  level n := f.level (n+1)
  point n := f.point (n+1)
  bond n := f.bond (n+1)

/-- Two consecutive bonds, on their actual quotient representatives. -/
theorem pairedBond_exists (X Y : Prespectrum.{0}) :
    ∃! b : C((X.level 0 |>.smash (Y.level 0)).suspension × I,
        (X.level 1).smash (Y.level 1)),
      (∀ x y s t,
        b (BasedSpace.suspensionProjection _ (BasedSpace.smashPoint _ _ x y,s),t) =
          BasedSpace.smashPoint _ _ (X.bond 0 (x,s)) (Y.bond 0 (y,t))) ∧
      (∀ t, b (((X.level 0).smash (Y.level 0)).suspension.point,t) =
        ((X.level 1).smash (Y.level 1)).point) ∧
      (∀ a, b (a,0) = ((X.level 1).smash (Y.level 1)).point) ∧
      (∀ a, b (a,1) = ((X.level 1).smash (Y.level 1)).point) := by sorry

noncomputable def pairedBond (X Y : Prespectrum.{0}) :
    C(((X.level 0).smash (Y.level 0)).suspension × I,
      (X.level 1).smash (Y.level 1)) := (pairedBond_exists X Y).exists.choose

def diagonalLevel (X Y : Prespectrum.{0}) : ℕ → BasedSpace.{0}
  | 0 => (X.level 0).smash (Y.level 0)
  | 1 => ((X.level 0).smash (Y.level 0)).suspension
  | n+2 => diagonalLevel X.tail Y.tail n

noncomputable def diagonalBond (X Y : Prespectrum.{0}) :
    ∀ n, C(diagonalLevel X Y n × I, diagonalLevel X Y (n+1))
  | 0 => BasedSpace.suspensionProjection _
  | 1 => pairedBond X Y
  | n+2 => diagonalBond X.tail Y.tail n

theorem diagonalBond_laws (X Y : Prespectrum.{0}) (n : ℕ) :
    (∀ t, diagonalBond X Y n ((diagonalLevel X Y n).point,t) =
      (diagonalLevel X Y (n+1)).point) ∧
    (∀ a, diagonalBond X Y n (a,0) = (diagonalLevel X Y (n+1)).point) ∧
    (∀ a, diagonalBond X Y n (a,1) = (diagonalLevel X Y (n+1)).point) := by sorry

noncomputable def diagonalSmash (X Y : Prespectrum.{0}) : Prespectrum.{0} where
  level := diagonalLevel X Y
  bond := diagonalBond X Y
  bond_point n := (diagonalBond_laws X Y n).1
  bond_zero n := (diagonalBond_laws X Y n).2.1
  bond_one n := (diagonalBond_laws X Y n).2.2

noncomputable def diagonalMapLevel {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    ∀ n, diagonalLevel X Y n ⟶ diagonalLevel X' Y' n
  | 0 => BasedSpace.smashMap ⟨f.level 0, f.point 0⟩ ⟨g.level 0, g.point 0⟩
  | 1 => BasedSpace.suspendMap
      (BasedSpace.smashMap ⟨f.level 0, f.point 0⟩ ⟨g.level 0, g.point 0⟩)
  | n+2 => diagonalMapLevel (tailMap f) (tailMap g) n

theorem diagonalMapLevel_bond {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) (a : diagonalLevel X Y n) (t : I) :
    (diagonalMapLevel f g (n+1)).map (diagonalBond X Y n (a,t)) =
      diagonalBond X' Y' n ((diagonalMapLevel f g n).map a,t) := by sorry

noncomputable def diagonalSmashMap {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') : diagonalSmash X Y ⟶ diagonalSmash X' Y' where
  level n := (diagonalMapLevel f g n).map
  point n := (diagonalMapLevel f g n).point
  bond n := diagonalMapLevel_bond f g n

/-- The flatness statement used by the derived comparison. The proof of
MMSS, Proposition 11.7, uses exactly CW homotopy type of each fixed level.
Our stronger based-CW condition makes that hypothesis explicit; the chosen
point-set double bonds are Definition 11.6 of the same source. -/
theorem diagonalSmash_stable_right (X : Prespectrum.{0}) (hX : X.IsGood)
    {Y Y' : Prespectrum.{0}} (f : Y ⟶ Y') (hf : stableEquivalences f) :
    stableEquivalences (diagonalSmashMap (𝟙 X) f) := by sorry

theorem diagonalSmash_stable_left (Y : Prespectrum.{0}) (hY : Y.IsGood)
    {X X' : Prespectrum.{0}} (f : X ⟶ X') (hf : stableEquivalences f) :
    stableEquivalences (diagonalSmashMap f (𝟙 Y)) := by sorry

/-- The zeroth-stage inclusion is the free/evaluation counit. -/
noncomputable def zeroStage (X : Prespectrum.{0}) : suspensionSpectrum (X.level 0) ⟶ X :=
  freeCounit X 0

end Prespectrum
end KIP126.StableHomotopy.Implementation
