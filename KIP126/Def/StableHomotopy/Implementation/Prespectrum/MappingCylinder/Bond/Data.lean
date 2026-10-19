module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Lift.Data
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The source bonds retain the mapping-cylinder parameter. -/
noncomputable def mappingCylinderRawBond {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(mappingCylinderRaw f n,C(I,mappingCylinderLevel f (n+1))) := by
  let a : C(X.level n × I,C(I,mappingCylinderLevel f (n+1))) :=
    (⟨fun z => mappingCylinderMk f (n+1) (.inl (X.bond n (z.1.1,z.2),z.1.2)),
      (mappingCylinderMk f (n+1)).continuous.comp
        (continuous_inl.comp (((X.bond n).continuous.comp
          (continuous_fst.fst.prodMk continuous_snd)).prodMk continuous_fst.snd))⟩ :
      C((X.level n × I) × I,mappingCylinderLevel f (n+1))).curry
  let b : C(Y.level n,C(I,mappingCylinderLevel f (n+1))) :=
    (⟨fun z => mappingCylinderMk f (n+1) (.inr (Y.bond n z)),
      (mappingCylinderMk f (n+1)).continuous.comp (continuous_inr.comp (Y.bond n).continuous)⟩ :
      C(Y.level n × I,mappingCylinderLevel f (n+1))).curry
  exact ⟨Sum.elim a b,a.continuous.sumElim b.continuous⟩

/-- Descend the actual bonds through the quotient, then uncurry. -/
noncomputable def mappingCylinderBond {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(mappingCylinderLevel f n × I,mappingCylinderLevel f (n+1)) :=
  (mappingCylinderLift f n (mappingCylinderRawBond f n)
    (by
      intro s
      apply ContinuousMap.ext
      intro t
      change mappingCylinderMk f (n+1) (.inl (X.bond n ((X.level n).point,t),s)) =
        mappingCylinderMk f (n+1) (.inr (Y.bond n ((Y.level n).point,t)))
      rw [X.bond_point,Y.bond_point,mappingCylinderMk_point]
      rfl)
    (by
      intro x
      apply ContinuousMap.ext
      intro t
      change mappingCylinderMk f (n+1) (.inl (X.bond n (x,t),1)) =
        mappingCylinderMk f (n+1) (.inr (Y.bond n (f.level n x,t)))
      rw [mappingCylinderMk_top,f.bond])).uncurry

end KIP126.StableHomotopy.Implementation.Prespectrum
