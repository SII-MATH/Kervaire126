import KIP126.Def.StableHomotopy.Implementation.PointSet
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.CWComplex.Classical.Basic

/-! Suspension spectra and free sequential prespectra. These give the
point-set generators used in the tensor recognition and telescope interface. -/
namespace KIP126.StableHomotopy.Implementation
open CategoryTheory Topology
open scoped unitInterval
universe u

namespace BasedSpace

@[ext] structure Hom (X Y : BasedSpace.{u}) where
  map : C(X,Y)
  point : map X.point = Y.point

instance : Category BasedSpace.{u} where
  Hom := Hom
  id X := ⟨ContinuousMap.id _, rfl⟩
  comp f g := ⟨g.map.comp f.map, by simp [f.point, g.point]⟩
  id_comp := by intros; ext; rfl
  comp_id := by intros; ext; rfl
  assoc := by intros; ext; rfl

def suspendMap {X Y : BasedSpace.{u}} (f : X ⟶ Y) : X.suspension ⟶ Y.suspension where
  map := suspensionMap X Y f.map f.point
  point := suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))

def iterateSuspension (X : BasedSpace.{u}) : ℕ → BasedSpace.{u}
  | 0 => X
  | n+1 => (iterateSuspension X n).suspension

def iterateSuspensionMap {X Y : BasedSpace.{u}} (f : X ⟶ Y) :
    ∀ n, iterateSuspension X n ⟶ iterateSuspension Y n
  | 0 => f
  | n+1 => suspendMap (iterateSuspensionMap f n)

def SmashRelation (X Y : BasedSpace.{u}) (p q : X × Y) : Prop :=
  (p.1 = X.point ∨ p.2 = Y.point) ∧ (q.1 = X.point ∨ q.2 = Y.point)

/-- Reduced smash in compactly generated spaces: k-ify the product before
collapsing its wedge. -/
def smash (X Y : BasedSpace.{u}) : BasedSpace.{u} where
  space := by
    letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
    exact TopCat.of (Quot (SmashRelation X Y))
  point := Quot.mk _ (X.point,Y.point)

def smashPoint (X Y : BasedSpace.{u}) (x : X) (y : Y) : X.smash Y := Quot.mk _ (x,y)

theorem smashPoint_base_left (X Y : BasedSpace.{u}) (y : Y) :
    smashPoint X Y X.point y = (X.smash Y).point := Quot.sound ⟨Or.inl rfl, Or.inl rfl⟩

theorem smashPoint_base_right (X Y : BasedSpace.{u}) (x : X) :
    smashPoint X Y x Y.point = (X.smash Y).point := Quot.sound ⟨Or.inr rfl, Or.inl rfl⟩

/-- The representative formulas uniquely determine the induced based maps.
Only their continuous quotient extension is a construction obligation. -/
theorem smashMap_exists {X Y X' Y' : BasedSpace.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    ∃! h : X.smash Y ⟶ X'.smash Y', ∀ x y,
      h.map (smashPoint X Y x y) = smashPoint X' Y' (f.map x) (g.map y) := by
  sorry

noncomputable def smashMap {X Y X' Y' : BasedSpace.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    X.smash Y ⟶ X'.smash Y' := (smashMap_exists f g).exists.choose

theorem smashCoherence_exists :
    (∀ X Y Z : BasedSpace.{u}, ∃! a : (X.smash Y).smash Z ⟶ X.smash (Y.smash Z),
      ∀ x y z, a.map (smashPoint _ Z (smashPoint X Y x y) z) =
        smashPoint X _ x (smashPoint Y Z y z)) ∧
    (∀ X Y : BasedSpace.{u}, ∃! b : X.smash Y ⟶ Y.smash X,
      ∀ x y, b.map (smashPoint X Y x y) = smashPoint Y X y x) := by
  sorry

noncomputable def smashAssoc (X Y Z : BasedSpace.{u}) :
    (X.smash Y).smash Z ⟶ X.smash (Y.smash Z) :=
  (smashCoherence_exists.1 X Y Z).exists.choose

noncomputable def smashSwap (X Y : BasedSpace.{u}) : X.smash Y ⟶ Y.smash X :=
  (smashCoherence_exists.2 X Y).exists.choose

/-- Actual based CW homotopy type, using characteristic cells and weak
CW topology from Mathlib, and homotopies fixed at the specified basepoint. -/
def HasCWType (A : BasedSpace.{u}) : Prop :=
  ∃ Y : BasedSpace.{u}, T2Space Y ∧
    Nonempty (Topology.CWComplex (Set.univ : Set Y)) ∧ Y.IsWellBased ∧
    ∃ (f : A ⟶ Y) (g : Y ⟶ A),
      (g.map.comp f.map).HomotopicRel (ContinuousMap.id A) {A.point} ∧
      (f.map.comp g.map).HomotopicRel (ContinuousMap.id Y) {Y.point}

/-- The derived-smash comparison is restricted to compactly generated,
well-based spaces of actual CW homotopy type. Merely being well-based does
not supply the flatness hypothesis used in MMSS, Proposition 11.7. -/
def IsGood (A : BasedSpace.{u}) : Prop :=
  UCompactlyGeneratedSpace.{u} A ∧ A.IsWellBased ∧ A.HasCWType

def zeroSphere : BasedSpace.{0} := Prespectrum.sphereLevel 0

theorem smashUnit_exists (A : BasedSpace.{0}) (hA : A.IsGood) :
    ∃! f : zeroSphere.smash A ⟶ A,
      ∀ a, f.map (smashPoint zeroSphere A (show zeroSphere from (1 : Fin 2)) a) = a := by
  sorry

noncomputable def smashUnit (A : BasedSpace.{0}) (hA : A.IsGood) :
    zeroSphere.smash A ⟶ A := (smashUnit_exists A hA).exists.choose

theorem good_zeroSphere : zeroSphere.IsGood := by sorry

theorem good_smash {A B : BasedSpace.{u}} (hA : A.IsGood) (hB : B.IsGood) :
    (A.smash B).IsGood := by sorry

/-- The quotient representative [a;t₀,…,tₙ₋₁] in an iterated suspension. -/
def iteratedPoint (A : BasedSpace.{u}) : ∀ n, A → (Fin n → I) → A.iterateSuspension n
  | 0, a, _ => a
  | n+1, a, t => suspensionProjection _ (iteratedPoint A n a (fun i => t i.succ), t 0)

theorem good_suspension {A : BasedSpace.{u}} (hA : A.IsGood) : A.suspension.IsGood := by sorry

/-- Moving the suspension coordinate past the second smash factor. The
formula fixes the comparison and its sign before stable localization. -/
theorem suspensionSmash_exists (A B : BasedSpace.{0})
    (hA : A.IsGood) (hB : B.IsGood) :
    ∃! f : A.suspension.smash B ⟶ (A.smash B).suspension, ∀ a b t,
      f.map (smashPoint _ B (suspensionProjection A (a,t)) b) =
        suspensionProjection (A.smash B) (smashPoint A B a b,t) := by sorry

noncomputable def suspensionSmash (A B : BasedSpace.{0})
    (hA : A.IsGood) (hB : B.IsGood) : A.suspension.smash B ⟶ (A.smash B).suspension :=
  (suspensionSmash_exists A B hA hB).exists.choose

end BasedSpace

namespace Prespectrum

def suspensionSpectrum (A : BasedSpace.{u}) : Prespectrum.{u} where
  level := A.iterateSuspension
  bond n := BasedSpace.suspensionProjection _
  bond_point _ _ := BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
  bond_zero _ _ := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond_one _ _ := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))

theorem suspensionSpectrum_good (A : BasedSpace.{u}) (hA : A.IsGood) :
    (suspensionSpectrum A).IsWellBased := by sorry

theorem suspensionSpectrum_zeroSphere :
    suspensionSpectrum BasedSpace.zeroSphere = sphere := by sorry

def suspensionSpectrumMap {A B : BasedSpace.{u}} (f : A ⟶ B) :
    suspensionSpectrum A ⟶ suspensionSpectrum B where
  level n := (BasedSpace.iterateSuspensionMap f n).map
  point n := (BasedSpace.iterateSuspensionMap f n).point
  bond := by intros; rfl

/-- Rotate the original suspension coordinate to the outside. Unlike an
unjustified levelwise identity, this formula commutes with the bonds. -/
theorem suspensionSpectrumSuspensionIso_exists (A : BasedSpace.{0}) :
    ∃ e : suspensionSpectrum A.suspension ≅ (suspensionSpectrum A).suspension,
      ∀ n a s (t : Fin n → I), e.hom.level n
        (BasedSpace.iteratedPoint A.suspension n (BasedSpace.suspensionProjection A (a,s)) t) =
          BasedSpace.suspensionProjection (A.iterateSuspension n)
            (BasedSpace.iteratedPoint A n a t,s) := by sorry

noncomputable def suspensionSpectrumSuspensionIso (A : BasedSpace.{0}) :
    suspensionSpectrum A.suspension ≅ (suspensionSpectrum A).suspension :=
  (suspensionSpectrumSuspensionIso_exists A).choose

/-- Padding with one zero level gives an actual desuspension prespectrum. -/
def desuspension (X : Prespectrum.{u}) : Prespectrum.{u} where
  level
    | 0 => { space := TopCat.of PUnit, point := PUnit.unit }
    | n+1 => X.level n
  bond
    | 0 => ContinuousMap.const _ (X.level 0).point
    | n+1 => X.bond n
  bond_point := by intro n t; cases n <;> simp [X.bond_point]
  bond_zero := by intro n x; cases n <;> simp [X.bond_zero]
  bond_one := by intro n x; cases n <;> simp [X.bond_one]

def free (n : ℕ) (A : BasedSpace.{u}) : Prespectrum.{u} :=
  (desuspension^[n]) (suspensionSpectrum A)

/-- The free/evaluation adjunction pins down maps from free prespectra;
it is not an independently chosen assignment of stable maps. -/
theorem freeEvaluation_exists (n : ℕ) (A : BasedSpace.{u}) (X : Prespectrum.{u}) :
    ∃ e : (free n A ⟶ X) ≃ (A ⟶ X.level n),
      ∀ f, HEq ((e f).map) (f.level n) := by
  sorry

noncomputable def freeEvaluation (n : ℕ) (A : BasedSpace.{u}) (X : Prespectrum.{u}) :
    (free n A ⟶ X) ≃ (A ⟶ X.level n) :=
  (freeEvaluation_exists n A X).choose

noncomputable def freeCounit (X : Prespectrum.{u}) (n : ℕ) : free n (X.level n) ⟶ X :=
  (freeEvaluation n (X.level n) X).symm (𝟙 _)

end Prespectrum
end KIP126.StableHomotopy.Implementation
