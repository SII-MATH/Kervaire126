module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Homotopy.Sphere.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

/-- Every coherent integer shift of the specified source sphere is the
specified sphere in the sum degree. -/
noncomputable def sourceSphere_addShiftIso (d k : ℤ) :
    (sourceSphere d)⟦k⟧ ≅ sourceSphere (d+k) :=
  (shiftFunctor SourceCategory k).mapIso (sourceSphere_shiftIso d) ≪≫
    (shiftFunctorAdd SourceCategory d k).symm.app (sourceLocalization.obj sphere) ≪≫
    (sourceSphere_shiftIso (d+k)).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
