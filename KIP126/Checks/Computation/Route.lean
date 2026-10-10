import KIP126.Interface.Challenge.Challenge2
import KIP126.Interface.Solution.Literature.Applications

/-! Selected C(M) interface regressions. These check interpretation and binding,
not the mathematical correctness of the archived calculation. -/
namespace KIP126.Checks.Computation.Route
open KIP126.Computation.Route
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  {D : Model H M Syn} (R : Realization D)

set_option maxRecDepth 10000

-- Missing and invalid indices cannot turn into a zero mathematical label.
example : R.decode .sphere 999 999 [] = none := by rfl
example : R.decode .sphere 8 134 [999] = none := by rfl
example : R.decode .sphere 8 134 [0,0] = none := by
  have h : Raw.coordinatesValid Raw.degrees .sphere 8 134 [0,0] = false := by decide
  simp [Realization.decode, h]
example : R.decode .sphere 8 134 [3,0] = none := by
  have h : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3,0] = false := by decide
  simp [Realization.decode, h]

-- Empty vector and unknown value have different meanings.
example : R.decode .sphere 8 134 [] = some 0 := by
  have h : Raw.coordinatesValid Raw.degrees .sphere 8 134 [] = true := by decide
  simp [Realization.decode, h]

-- There is no independent cofiber or sphere sequence hidden in the realization.
example : sequence D .sphere = adamsTowerInternalSpectralSequence H.unit SphereSpectrum := rfl
example : sequence D .nuCofiber = adamsTowerInternalSpectralSequence H.unit
    (HasFunctorialCofiber.cofib D.auxiliary.nuMap) := rfl

-- Check ALL coordinate ranges and differential degrees using an executable check.
-- This evaluates concrete data; it supplies no axiom asserting mathematical truth.
#eval do
  if Raw.claims.all (Raw.Claim.valid Raw.degrees) then
    IO.println "Selected route: all records have valid coordinates and Adams degrees."
  else throw (IO.userError "invalid selected route record")

end KIP126.Checks.Computation.Route
