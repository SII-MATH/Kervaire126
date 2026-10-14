module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Abelian.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Exact.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.LoopKernel.Proofs
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- Exactness at the actual loop prespectrum's stable homotopy group. -/
theorem loopMap_fiberConnecting_stableHomotopy_exact {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (d : ℤ) (y : StableHomotopy (Prespectrum.loop Y) d) :
    stableHomotopyMap (fiberConnecting f) d y = 0 ↔
      ∃ x, stableHomotopyMap (loopMap f) d x = y :=
  stableHomotopy_exact_of_levelLoop_exact (loopMap f) (fiberConnecting f)
    (loopMap_fiberConnecting_levelLoop_exact f) d y

/-- The incoming original map and the additive boundary are exact in every
integer degree, with no condition on the map of prespectra. -/
theorem fiberBoundary_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ) :
    Function.Exact (stableHomotopyAddHom f (d+1)) (fiberBoundary f d) := by
  intro y
  change stableHomotopyMap (fiberConnecting f) d
    ((stableLoopHomotopyEquiv Y d).symm y) = 0 ↔
      ∃ x, stableHomotopyMap f (d+1) x = y
  rw [loopMap_fiberConnecting_stableHomotopy_exact]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨stableLoopHomotopyEquiv X d x,?_⟩
    exact (stableLoopHomotopyMap_natural f d x).symm.trans
      ((congrArg (stableLoopHomotopyEquiv Y d) hx).trans
        ((stableLoopHomotopyEquiv Y d).apply_symm_apply y))
  · rintro ⟨x,hx⟩
    refine ⟨(stableLoopHomotopyEquiv X d).symm x,?_⟩
    apply (stableLoopHomotopyEquiv Y d).injective
    exact (stableLoopHomotopyMap_natural f d ((stableLoopHomotopyEquiv X d).symm x)).trans
      ((congrArg (stableHomotopyMap f (d+1))
        ((stableLoopHomotopyEquiv X d).apply_symm_apply x)).trans
        (hx.trans ((stableLoopHomotopyEquiv Y d).apply_symm_apply y).symm))

/-- The boundary and fiber projection form an exact pair of abelian-group maps. -/
theorem fiberBoundary_projection_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ) :
    Function.Exact (fiberBoundary f d) (stableHomotopyAddHom (fiberProjection f) d) :=
  fiberConnecting_shifted_exact f d

/-- The fiber projection and original map form an exact pair of abelian-group maps. -/
theorem fiberProjection_map_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ) :
    Function.Exact (stableHomotopyAddHom (fiberProjection f) d) (stableHomotopyAddHom f d) :=
  fiberProjection_stableHomotopy_exact f d

/-- The three consecutive exact positions of the stable homotopy long exact
sequence, for every integer degree and every actual strict map. -/
theorem fiber_stableHomotopy_longExact {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ) :
    Function.Exact (stableHomotopyAddHom f (d+1)) (fiberBoundary f d) ∧
    Function.Exact (fiberBoundary f d) (stableHomotopyAddHom (fiberProjection f) d) ∧
    Function.Exact (stableHomotopyAddHom (fiberProjection f) d) (stableHomotopyAddHom f d) :=
  ⟨fiberBoundary_exact f d, fiberBoundary_projection_exact f d, fiberProjection_map_exact f d⟩

end KIP126.StableHomotopy.Implementation.Prespectrum

end
