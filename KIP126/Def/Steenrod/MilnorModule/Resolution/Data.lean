import KIP126.Def.Steenrod.MilnorModule.Resolution.Complex.Proofs

/-!
The projective resolution formed from the specified dual cobar complex.
Its mathematical property obligations are separate; the bundled terms,
differentials and augmentation are exactly those constructed earlier.
-/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory

/-- The actual termwise dual projective resolution of the fixed trivial
left module, for the supplied normalized cofree right-comodule resolution. -/
noncomputable def dualCobarResolution (R : Ext.CobarResolution) :
    ProjectiveResolution (trivialAt 0) where
  complex := dualCobarComplex R
  projective := dualCobarTerm_projective R
  π := dualCobarAugmentation R
  quasiIso := dualCobarAugmentation_quasiIso R

end KIP126.Steenrod.Milnor.Module
