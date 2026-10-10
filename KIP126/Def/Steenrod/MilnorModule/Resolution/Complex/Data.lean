import KIP126.Def.Steenrod.MilnorModule.Resolution.Raw.Proofs

/-! The actual dual chain complex and its actual augmentation. All terms
and all differentials are the previously specified dual objects and maps. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory

noncomputable section

/-- Termwise contravariant dualization of the supplied cobar resolution. -/
def dualCobarComplex (R : Ext.CobarResolution) : ChainComplex LeftModule ℕ where
  X := dualCobarTerm R
  d := dualCobarDifferential R
  shape := dualCobarDifferential_shape R
  d_comp_d' := fun i j k _ _ => dualCobarDifferential_comp R i j k

/-- Extend the fixed degree-zero augmentation to the single-object complex. -/
def dualCobarAugmentation (R : Ext.CobarResolution) :
    dualCobarComplex R ⟶ (ChainComplex.single₀ LeftModule).obj (trivialAt 0) :=
  (ChainComplex.toSingle₀Equiv (dualCobarComplex R) (trivialAt 0)).symm
    ⟨dualCobarAugmentationZero R, dualCobarDifferential_augmentation R⟩

end
end KIP126.Steenrod.Milnor.Module
