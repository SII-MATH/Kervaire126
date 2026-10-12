module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Adjunction.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Instances

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem loopMap_zero (X Y : Prespectrum.{u}) :
    loopMap (0 : X ⟶ Y) = 0 := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  rfl

/-- The loop functor preserves the already specified source zero morphisms. -/
instance sourceLoopFunctor_preservesZeroMorphisms :
    sourceLoopFunctor.{u}.PreservesZeroMorphisms where
  map_zero A B := by
    change sourceLoopFunctor.map (0 : sourceLocalization.obj A.as.obj ⟶
      sourceLocalization.obj B.as.obj) = _
    rw [← sourceLocalization.map_zero, sourceLoopFunctor_map, loopMap_zero,
      sourceLocalization.map_zero]

instance sourceLoopFunctor_full : sourceLoopFunctor.{u}.Full := by
  letI : sourceDesuspensionFunctor.{u}.Full :=
    sourceSuspensionEquivalence.fullyFaithfulInverse.full
  exact Functor.Full.of_iso sourceLoopDesuspensionIso.symm

instance sourceLoopFunctor_faithful : sourceLoopFunctor.{u}.Faithful := by
  letI : sourceDesuspensionFunctor.{u}.Faithful :=
    sourceSuspensionEquivalence.fullyFaithfulInverse.faithful
  exact Functor.Faithful.of_iso sourceLoopDesuspensionIso.symm

end KIP126.StableHomotopy.Implementation.Prespectrum
