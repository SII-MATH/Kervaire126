module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Stable.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Kernel.Lift.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Equivalence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u

/-- Exactness at the actual fiber's stable homotopy groups, in every degree. -/
theorem fiberConnecting_stableHomotopy_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (d : ℤ) (z : StableHomotopy (fiber f) d) :
    stableHomotopyMap (fiberProjection f) d z = 0 ↔
      ∃ y, stableHomotopyMap (fiberConnecting f) d y = z :=
  stableHomotopy_exact_of_levelLoop_exact (fiberConnecting f) (fiberProjection f)
    (fiberConnecting_levelLoop_exact f) d z

/-- The connecting term has the actual shifted degree, via the already
proved last-coordinate stable loop equivalence. -/
theorem fiberConnecting_shifted_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (d : ℤ) (z : StableHomotopy (fiber f) d) :
    stableHomotopyMap (fiberProjection f) d z = 0 ↔
      ∃ y : StableHomotopy Y (d+1),
        stableHomotopyMap (fiberConnecting f) d ((stableLoopHomotopyEquiv Y d).symm y) = z := by
  rw [fiberConnecting_stableHomotopy_exact]
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨stableLoopHomotopyEquiv Y d y,by simpa only [Equiv.symm_apply_apply] using hy⟩
  · rintro ⟨y,hy⟩
    exact ⟨(stableLoopHomotopyEquiv Y d).symm y,hy⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
