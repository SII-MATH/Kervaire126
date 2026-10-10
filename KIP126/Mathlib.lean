import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import KIP126.Mathlib.SpectralSequence.FilteredComplex.Adapter.Proofs
import KIP126.Mathlib.SpectralSequence.FilteredComplex.Relations.Proofs
import KIP126.Mathlib.SpectralSequence.SSData.Assembly.Proofs
import KIP126.Mathlib.SpectralSequence.Endpoint.Convergence.Proofs
import KIP126.Mathlib.SpectralSequence.Permanence.Data
import KIP126.Mathlib.ClassicalAdams.Comparison.Construction.Data
import KIP126.Mathlib.ClassicalAdams.SurvivalComparison.Proofs
import KIP126.Mathlib.ClassicalAdams.FinalComparison.Proofs

/-!
# Mathlib dependencies

This layer imports upstream Mathlib and houses checked adapters from KIP126's
`SSData`-based presentation to Mathlib's spectral-sequence API. No upstream
declaration is copied, and no mathematical assumption is added.
-/
