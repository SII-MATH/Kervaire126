module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Proofs
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Homotopy.Product

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits Topology
open scoped Topology.Homotopy

universe u

variable {J : Type}

/-- The actual pointwise product of a small family of prespectra. -/
def piPrespectrum (X : J → Prespectrum.{u}) : Prespectrum.{u} where
  level n := { space := TopCat.of (∀ j, X j |>.level n), point := fun j => (X j |>.level n).point }
  bond n := ⟨fun p j => (X j).bond n (p.1 j,p.2),
    continuous_pi fun j => ((X j).bond n).continuous.comp
      (((continuous_apply j).comp continuous_fst).prodMk continuous_snd)⟩
  bond_point n t := funext fun j => (X j).bond_point n t
  bond_zero n p := funext fun j => (X j).bond_zero n (p j)
  bond_one n p := funext fun j => (X j).bond_one n (p j)

def piProjection (X : J → Prespectrum.{u}) (j : J) : piPrespectrum X ⟶ X j where
  level n := ⟨fun p => p j, continuous_apply j⟩
  point _ := rfl
  bond _ _ _ := rfl

def piLift {A : Prespectrum.{u}} {X : J → Prespectrum.{u}} (f : ∀ j, A ⟶ X j) :
    A ⟶ piPrespectrum X where
  level n := ContinuousMap.pi (fun j => (f j).level n)
  point n := funext fun j => (f j).point n
  bond n x t := funext fun j => (f j).bond n x t

/-- The pointwise product of actual prespectrum maps. -/
def piMap {X Y : J → Prespectrum.{u}} (f : ∀ j, X j ⟶ Y j) :
    piPrespectrum X ⟶ piPrespectrum Y :=
  piLift (fun j => piProjection X j ≫ f j)

/-- The actual product cone; its universal property is proved separately. -/
def piFan (X : J → Prespectrum.{u}) : Fan X := Fan.mk _ (piProjection X)

/-- A family of actual loops gives the corresponding loop into the levelwise product. -/
def piLoop (X : J → Prespectrum.{u}) (n r : ℕ)
    (p : ∀ j, GenLoop (Fin r) (X j |>.level n) (X j |>.level n).point) :
    GenLoop (Fin r) ((piPrespectrum X).level n) ((piPrespectrum X).level n).point :=
  ⟨ContinuousMap.pi (fun j => (p j).val), fun t ht => funext fun j => (p j).property t ht⟩

def levelPiComparison (X : J → Prespectrum.{u}) (n r : ℕ) :
    _root_.HomotopyGroup (Fin r) ((piPrespectrum X).level n) ((piPrespectrum X).level n).point →
      ∀ j, _root_.HomotopyGroup (Fin r) (X j |>.level n) (X j |>.level n).point :=
  fun p j => (piProjection X j).levelHomotopy n r p

end KIP126.StableHomotopy.Implementation.Prespectrum
