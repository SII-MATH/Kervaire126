module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Abelian.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual additive connecting homomorphism, using the proved loop-degree
comparison and the inclusion of based loops into the path homotopy fiber. -/
noncomputable def fiberBoundary {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ) :
    StableHomotopy Y (d+1) →+ StableHomotopy (fiber f) d :=
  (stableHomotopyAddHom (fiberConnecting f) d).comp
    (stableLoopHomotopyAddEquiv Y d).symm.toAddMonoidHom

end KIP126.StableHomotopy.Implementation.Prespectrum
