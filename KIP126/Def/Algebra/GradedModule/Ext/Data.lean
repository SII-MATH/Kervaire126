import KIP126.Def.Algebra.GradedModule.Trivial.Data
import KIP126.Def.Algebra.GradedModule.Structure.Data
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! Actual derived Ext of graded left modules. The coefficient convention
is `Ext^s(k,k[t])`, so contravariant same-degree dualization reverses the
right-comodule arguments without changing the internal integer `t`. -/

namespace KIP126.Algebra.GradedModule

open CategoryTheory GradedVectorSpace

universe u
variable {K : Type u} [Field K]

/-- The standard localization universe defines actual derived Ext. -/
instance hasExt (A : Mon (GrVect K)) : HasExt.{u + 1} (LeftModule A) :=
  HasExt.standard _

/-- Derived Ext in the actual category of graded left modules. -/
abbrev DerivedExt {A : Mon (GrVect K)} (M N : LeftModule A) (s : ℕ) : Type (u + 1) :=
  Abelian.Ext.{u + 1} M N s

/-- Left-module coefficient Ext: the internal shift belongs to the target.
This is a derived-category object, not a renamed cobar cohomology quotient. -/
abbrev CoefficientExt {A : Mon (GrVect K)} (ε : Augmentation A)
    (s : ℕ) (t : ℤ) : Type (u + 1) :=
  DerivedExt (trivialAt K ε 0) (trivialAt K ε t) s

/-- The degree-zero class of the identity of the actual trivial left module. -/
noncomputable def coefficientUnit {A : Mon (GrVect K)} (ε : Augmentation A) :
    CoefficientExt ε 0 0 :=
  Abelian.Ext.mk₀ (𝟙 (trivialAt K ε 0))

end KIP126.Algebra.GradedModule
