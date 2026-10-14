module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Adjunction.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Chain.Data
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- The actual suspension-loop unit is invertible in the original source,
by the proved full faithfulness of the actual suspension functor. -/
noncomputable def sourceSuspensionLoopUnitIso :
    𝟭 SourceCategory.{u} ≅ sourceSuspensionFunctor ⋙ sourceLoopFunctor :=
  asIso sourceSuspensionLoopAdjunction.unit

end KIP126.StableHomotopy.Implementation.Prespectrum
