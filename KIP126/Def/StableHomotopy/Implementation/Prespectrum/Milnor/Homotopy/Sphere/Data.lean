module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Source.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Coherence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- The specified representing sphere is the coherent integer shift of
the original point-set sphere in the actual source category. -/
noncomputable def sourceSphere_shiftIso (d : ℤ) :
    sourceSphere d ≅ (sourceLocalization.obj sphere)⟦d⟧ :=
  sourceSphere_actualShiftIso d ≪≫ eqToIso (source_shiftFunctor_obj d sphere).symm

/-- Shifting the actual representing sphere once gives the next specified
sphere, using the proved integer-shift coherence. -/
noncomputable def sourceSphere_succShiftIso (d : ℤ) :
    (sourceSphere d)⟦(1 : ℤ)⟧ ≅ sourceSphere (d+1) :=
  (shiftFunctor SourceCategory (1 : ℤ)).mapIso (sourceSphere_shiftIso d) ≪≫
    (shiftFunctorAdd SourceCategory d 1).symm.app (sourceLocalization.obj sphere) ≪≫
    (sourceSphere_shiftIso (d+1)).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
