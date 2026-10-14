module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Instances
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Equivalence
public import Mathlib.Algebra.Category.Grp.Preadditive

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

universe u

/-- A constant point-set morphism induces the zero map on the actual stable groups. -/
theorem Prespectrum.stableHomotopyMap_zero_morphism (X Y : Prespectrum.{u}) (d : ℤ)
    (x : X.StableHomotopy d) : stableHomotopyMap (0 : X ⟶ Y) d x = 0 := by
  induction x using Quot.inductionOn with
  | h a => exact loopClass_const Y d a.stage a.dimension a.degree

instance Prespectrum.stableHomotopyAddFunctor_preservesZeroMorphisms (d : ℤ) :
    (stableHomotopyAddFunctor.{u} d).PreservesZeroMorphisms where
  map_zero X Y := by
    ext x
    exact stableHomotopyMap_zero_morphism X Y d x

instance sourceStableHomotopyAddFunctor_preservesZeroMorphisms (d : ℤ) :
    (sourceStableHomotopyAddFunctor.{u} d).PreservesZeroMorphisms where
  map_zero X Y := by
    rcases X with ⟨⟨X⟩⟩
    rcases Y with ⟨⟨Y⟩⟩
    change (sourceStableHomotopyAddFunctor d).map
      (0 : sourceLocalization.obj X ⟶ sourceLocalization.obj Y) = _
    rw [← sourceLocalization.map_zero X Y, sourceStableHomotopyAddFunctor_map]
    exact (Prespectrum.stableHomotopyAddFunctor d).map_zero X Y

/-- Ordinary source sphere representability preserves the categorical zero
already constructed from the point prespectrum. -/
theorem Prespectrum.sourceStableHomotopyEquiv_zero (X : Prespectrum) (d : ℤ) :
    sourceStableHomotopyEquiv X d 0 = 0 := by
  have h := sourceStableHomotopyEquiv_natural
    (sourceLocalization.map (0 : X ⟶ X)) d 0
  rw [sourceStableHomotopyFunctor_map] at h
  change sourceStableHomotopyEquiv X d (stableHomotopyMap (0 : X ⟶ X) d 0) = _ at h
  rw [stableHomotopyMap_zero_morphism, sourceLocalization.map_zero, comp_zero] at h
  exact h

end KIP126.StableHomotopy.Implementation
