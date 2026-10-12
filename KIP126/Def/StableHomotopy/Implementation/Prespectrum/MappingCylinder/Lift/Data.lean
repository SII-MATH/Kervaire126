module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Level

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u v

/-- Continuous descent through the actual reduced mapping-cylinder quotient. -/
noncomputable def mappingCylinderLift {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    {Z : Type v} [TopologicalSpace Z] (g : C(mappingCylinderRaw f n,Z))
    (hp : ∀ t, g (.inl ((X.level n).point,t)) = g (.inr (Y.level n).point))
    (ht : ∀ x, g (.inl (x,1)) = g (.inr (f.level n x))) :
    C(mappingCylinderLevel f n,Z) := by
  let hg : ∀ a b, Setoid.ker (mappingCylinderNormalize f n) a b → g a = g b :=
    fun a b h => (mappingCylinder_normalize_invariant f n g hp ht a).symm.trans
      ((congrArg g h).trans (mappingCylinder_normalize_invariant f n g hp ht b))
  exact ⟨Quotient.lift g hg, g.continuous.quotient_lift hg⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
