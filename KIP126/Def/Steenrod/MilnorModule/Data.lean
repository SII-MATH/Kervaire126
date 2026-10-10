import KIP126.Def.Algebra.GradedDual.Augmentation.Data
import KIP126.Def.Algebra.GradedModule.Ext.Data
import KIP126.Def.Steenrod.MilnorCoalgebra.Data

/-! The left Steenrod-module model is fixed by transposing the existing
Milnor coproduct, without exchanging its slots. Its actual derived Ext is
distinct from the right-comodule Ext until a comparison is constructed. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory KIP126.Core.Algebra KIP126.Algebra
open GradedVectorSpace

/-- The same-degree dual of the fixed Milnor coalgebra, with its actual
convolution multiplication. -/
noncomputable def steenrod : Mon (GrVect F2) :=
  GradedDual.convolutionAlgebra Coalgebra.dualSteenrod

/-- Evaluation on the fixed constant polynomial `1`. -/
noncomputable def augmentation : GradedModule.Augmentation steenrod :=
  GradedDual.convolutionAugmentation Coalgebra.coaugmentation

/-- Actual graded left modules over this fixed convolution algebra. -/
abbrev LeftModule := GradedModule.LeftModule steenrod

/-- The actual trivial module in internal degree `t`. -/
noncomputable def trivialAt (t : ℤ) : LeftModule :=
  GradedModule.trivialAt F2 augmentation t

/-- Sphere coefficients in the left-module convention `Ext^s(k,k[t])`. -/
abbrev SphereExt (s : ℕ) (t : ℤ) : Type 1 :=
  GradedModule.CoefficientExt augmentation s t

/-- The identity class in bidegree `(0,0)`. -/
noncomputable def unit : SphereExt 0 0 :=
  GradedModule.coefficientUnit augmentation

end KIP126.Steenrod.Milnor.Module
