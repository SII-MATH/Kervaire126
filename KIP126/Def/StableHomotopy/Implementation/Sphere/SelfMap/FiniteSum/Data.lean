module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.SelfMap.Data
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Coproduct.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Additive.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits

/-- The actual projection of the quotient wedge retaining the indicated
branch and sending every other branch to its original basepoint. -/
noncomputable def sphereWedgeProjection {J : Type} (Y : J → BasedSpace) (j : J) :
    BasedSpace.wedge Y ⟶ Y j := by
  classical
  exact BasedSpace.wedgeDesc (fun k => if h : k = j then eqToHom (congrArg Y h)
    else ⟨ContinuousMap.const _ (Y j).point,rfl⟩)

/-- The free prespectrum on the actual quotient wedge, with its original
branch inclusions. -/
noncomputable def sphereWedgeFreeCofan {J : Type} (n : ℕ) (Y : J → BasedSpace) :
    Cofan (fun j => free n (Y j)) :=
  Cofan.mk (free n (BasedSpace.wedge Y)) (fun j => freeMap n (BasedSpace.wedgeι Y j))

/-- The same actual wedge cofan in the original stable localization. -/
noncomputable def sphereWedgeSourceCofan {J : Type} (n : ℕ) (Y : J → BasedSpace) :
    Cofan (fun j => sourceLocalization.obj (free n (Y j))) :=
  Cofan.mk (sourceLocalization.obj (free n (BasedSpace.wedge Y)))
    (fun j => sourceLocalization.map (freeMap n (BasedSpace.wedgeι Y j)))

end KIP126.StableHomotopy.Implementation.Prespectrum
