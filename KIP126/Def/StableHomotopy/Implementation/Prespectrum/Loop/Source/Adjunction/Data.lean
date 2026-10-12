module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Adjunction.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Functor
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Equivalence
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Descend the actual suspension-loop adjunction through the original
stable equivalences. -/
noncomputable def sourceSuspensionLoopAdjunction :
    sourceSuspensionFunctor.{u} ⊣ sourceLoopFunctor := by
  letI : CatCommSq suspensionFunctor sourceLocalization sourceLocalization sourceSuspensionFunctor :=
    ⟨eqToIso (Localization.Construction.fac _ _).symm⟩
  letI : CatCommSq loopFunctor sourceLocalization sourceLocalization sourceLoopFunctor :=
    ⟨eqToIso sourceLoopFunctor_fac.symm⟩
  exact suspensionLoopAdjunction.localization sourceLocalization stableEquivalences
    sourceLocalization stableEquivalences sourceSuspensionFunctor sourceLoopFunctor

/-- Ordinary compact-open loops and padded desuspension become naturally
isomorphic on the actual source category, by uniqueness of right adjoints. -/
noncomputable def sourceLoopDesuspensionIso : sourceLoopFunctor.{u} ≅ sourceDesuspensionFunctor :=
  sourceSuspensionLoopAdjunction.rightAdjointUniq sourceSuspensionEquivalence.toAdjunction

/-- The pointwise loop object agrees with the existing negative shift in the
original stable localization. -/
noncomputable def sourceLoopComparisonIso (X : Prespectrum.{u}) :
    sourceLocalization.obj (Prespectrum.loop X) ≅ sourceLocalization.obj (desuspension X) :=
  sourceLoopDesuspensionIso.app (sourceLocalization.obj X)

end KIP126.StableHomotopy.Implementation.Prespectrum
