import KIP126.Def.Steenrod.MilnorModule.TrivialDual.Data
import KIP126.Def.Steenrod.MilnorExt.Resolution.Data
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
The specified terms, reversed differentials and augmentation obtained by
dualizing a supplied normalized Milnor cofree resolution. No projective
resolution or comparison is chosen independently of that supplied resolution.
-/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory

noncomputable section

/-- The same-degree dual of the supplied resolution's actual term. -/
def dualCobarTerm (R : Ext.CobarResolution) (s : ℕ) : LeftModule :=
  dualLeftModule (R.resolution.cocomplex.X s)

/-- Reverse the supplied differential and transpose that exact comodule map. -/
def dualCobarDifferential (R : Ext.CobarResolution) (i j : ℕ) :
    dualCobarTerm R i ⟶ dualCobarTerm R j :=
  dualLeftMap (R.resolution.cocomplex.d j i)

/-- Transpose the specified coaugmentation and use the fixed coefficient
evaluation isomorphism in degree zero. -/
def dualCobarAugmentationZero (R : Ext.CobarResolution) :
    dualCobarTerm R 0 ⟶ trivialAt 0 :=
  dualLeftMap (R.resolution.ι.f 0) ≫ (trivialDualIso 0).hom

end
end KIP126.Steenrod.Milnor.Module
