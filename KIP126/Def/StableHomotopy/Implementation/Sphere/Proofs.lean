module

public import KIP126.Def.StableHomotopy.Implementation.PointSet
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Proofs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import KIP126.Def.StableHomotopy.Implementation.Sphere.OnePoint.Proofs
public import KIP126.Def.Topology.Sphere.Approximation.Proofs

@[expose] public section

/-! Concrete topology of the actual point-set sphere. Paths are constructed
on reduced-suspension representatives. Higher connectivity follows from its
homeomorphism to the Euclidean sphere and relative smooth approximation.
The stable quotient consequently vanishes in every negative degree. -/

namespace KIP126.StableHomotopy.Implementation

open Topology
open scoped unitInterval Topology.Homotopy

universe u

namespace BasedSpace

/-- Move along the suspension coordinate from the collapsed end to the
chosen point. This constructs a path separately for each quotient class. -/
theorem suspension_joined_point (X : BasedSpace.{u}) (x : X.suspension) :
    Joined X.suspension.point x := by
  induction x using Quot.inductionOn with
  | h p =>
    refine ⟨{
      toFun := fun t => suspensionProjection X (p.1, t * p.2)
      continuous_toFun := (suspensionProjection X).continuous.comp
        (continuous_const.prodMk
          ((continuous_subtype_val.mul_const (p.2 : ℝ)).subtype_mk _))
      source' := ?_
      target' := ?_ }⟩
    · simpa only [zero_mul] using
        suspensionProjection_collapsed X (p.1, 0) (Or.inr (Or.inl rfl))
    · simp only [one_mul]
      rfl

theorem suspension_pathConnected (X : BasedSpace.{u}) :
    PathConnectedSpace X.suspension where
  nonempty := ⟨X.suspension.point⟩
  joined x y := (suspension_joined_point X x).symm.trans (suspension_joined_point X y)

/-- A nonzero-dimensional cubical loop in a discrete based space is
constant: its connected domain maps to one point, and its boundary fixes
that point to be the basepoint. -/
theorem genLoop_eq_const_of_discrete (X : BasedSpace.{u}) [DiscreteTopology X]
    (r : ℕ) (p : GenLoop (Fin (r + 1)) X X.point) : p = GenLoop.const := by
  apply GenLoop.ext
  intro t
  change p t = X.point
  have h : p t = p (fun _ => 0) :=
    PreconnectedSpace.constant inferInstance p.val.continuous
  exact h.trans (p.property _ ⟨0, Or.inl rfl⟩)

end BasedSpace

namespace Prespectrum

/-- All positive levels of the selected sphere are path-connected by their
actual reduced-suspension construction. -/
theorem sphereLevel_pathConnected (n : ℕ) : PathConnectedSpace (sphereLevel (n + 1)) :=
  BasedSpace.suspension_pathConnected (sphereLevel n)

/-- The zeroth homotopy set of every positive sphere level is a singleton. -/
theorem sphereLevel_pi0_subsingleton (n : ℕ) :
    Subsingleton (_root_.HomotopyGroup.Pi 0 (sphereLevel (n + 1))
      (sphereLevel (n + 1)).point) := by
  letI := sphereLevel_pathConnected n
  exact (_root_.HomotopyGroup.pi0EquivZerothHomotopy
    (X := sphereLevel (n + 1)) (x := (sphereLevel (n + 1)).point)).injective.subsingleton

/-- The preceding singleton assertion gives an actual based nullhomotopy
of each zero-dimensional cubical map to a positive sphere level. -/
theorem sphereLevel_zeroLoop_nullhomotopic (n : ℕ)
    (p : GenLoop (Fin 0) (sphereLevel (n + 1)) (sphereLevel (n + 1)).point) :
    GenLoop.Homotopic p GenLoop.const := by
  exact Quotient.exact ((sphereLevel_pi0_subsingleton n).elim
    (⟦p⟧ : _root_.HomotopyGroup.Pi 0 (sphereLevel (n + 1))
      (sphereLevel (n + 1)).point) ⟦GenLoop.const⟧)

/-- A representative in cubical dimension zero at a positive sphere level
already represents the stable basepoint in its negative stable degree. -/
theorem sphere_zeroLoopClass_eq_const (n : ℕ)
    (p : GenLoop (Fin 0) (sphere.level (n + 1)) (sphere.level (n + 1)).point) :
    loopClass sphere (-((n : ℤ) + 1)) (n + 1) 0 (by omega) p =
      loopClass sphere (-((n : ℤ) + 1)) (n + 1) 0 (by omega) GenLoop.const :=
  loopClass_eq_of_homotopic _ _ _ _ _ (sphereLevel_zeroLoop_nullhomotopic n p)

/-- In degree zero the chosen sphere level is literally the discrete based
two-point space, so every positive-dimensional cubical loop is constant. -/
theorem sphereLevel_zero_genLoop_eq_const (r : ℕ)
    (p : GenLoop (Fin (r + 1)) (sphereLevel 0) (sphereLevel 0).point) :
    p = GenLoop.const := by
  letI : DiscreteTopology (sphereLevel 0) := inferInstanceAs (DiscreteTopology (Fin 2))
  exact BasedSpace.genLoop_eq_const_of_discrete (sphereLevel 0) r p

/-- Every cubical map below the level dimension is based nullhomotopic.
This is transported from the Euclidean sphere along the proved homeomorphism
of the actual iterated reduced suspension. -/
theorem sphereLevel_genLoop_nullhomotopic {n r : ℕ} (hrn : r < n)
    (p : GenLoop (Fin r) (sphereLevel n) (sphereLevel n).point) :
    GenLoop.Homotopic p GenLoop.const := by
  obtain ⟨e⟩ := exists_sphereLevel_homeomorph_euclideanSphere n
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  let q : GenLoop (Fin r) (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (e (sphereLevel n).point) :=
    ⟨⟨fun x => e (p x), e.continuous.comp p.val.continuous⟩, by
      intro x hx
      exact congrArg e (p.property x hx)⟩
  obtain ⟨H⟩ := KIP126.Topology.Sphere.genLoop_nullhomotopic_of_lt_dimension hrn q
  refine ⟨{
    toFun := fun z => e.symm (H z)
    continuous_toFun := e.symm.continuous.comp H.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    change e.symm (H (0, x)) = p x
    rw [H.apply_zero]
    exact e.symm_apply_apply (p x)
  · intro x
    change e.symm (H (1, x)) = (sphereLevel n).point
    rw [H.apply_one]
    exact e.symm_apply_apply (sphereLevel n).point
  · intro s x hx
    change e.symm (H (s, x)) = p x
    rw [H.eq_fst s hx]
    exact e.symm_apply_apply (p x)

/-- The levelwise ordinary homotopy sets below the sphere dimension vanish. -/
theorem sphereLevel_homotopyGroup_subsingleton {n r : ℕ} (hrn : r < n) :
    Subsingleton (_root_.HomotopyGroup.Pi r (sphereLevel n) (sphereLevel n).point) := by
  constructor
  intro x y
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q => exact Quotient.sound ((sphereLevel_genLoop_nullhomotopic hrn p).trans
        (sphereLevel_genLoop_nullhomotopic hrn q).symm)

/-- The ordinary point-set sphere is connective. This computes the actual
stable homotopy quotient and does not use any completion or source comparison. -/
theorem sphere_stableHomotopy_subsingleton_of_neg (d : ℤ) (hd : d < 0) :
    Subsingleton (StableHomotopy sphere d) := by
  apply stableHomotopy_subsingleton_of_eventually_nullhomotopic 0
  intro n _ r hr p
  exact sphereLevel_genLoop_nullhomotopic (by omega) p

end Prespectrum
end KIP126.StableHomotopy.Implementation
