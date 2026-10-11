module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import KIP126.Mathlib.SpectralSequence.FilteredComplex.Adapter.Proofs
public import KIP126.Mathlib.SpectralSequence.FilteredComplex.Relations.Proofs
public import KIP126.Mathlib.SpectralSequence.SSData.Assembly.Proofs
public import KIP126.Mathlib.SpectralSequence.Endpoint.Convergence.Proofs
public import KIP126.Mathlib.SpectralSequence.Permanence.Data
public import KIP126.Mathlib.ClassicalAdams.Comparison.Construction.Data
public import KIP126.Mathlib.ClassicalAdams.SurvivalComparison.Proofs
public import KIP126.Mathlib.ClassicalAdams.FinalComparison.Proofs

@[expose] public section

/-!
# Mathlib dependencies

This layer imports upstream Mathlib and houses checked adapters from KIP126's
`SSData`-based presentation to Mathlib's spectral-sequence API. No upstream
declaration is copied, and no mathematical assumption is added.
-/
