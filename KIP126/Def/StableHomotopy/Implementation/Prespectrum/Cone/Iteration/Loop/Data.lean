module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Adjunction.Hom.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The outer cylinder, traversed backwards, followed by the inner
cylinder is an actual based loop in the twice-iterated mapping cone. -/
noncomputable def coneIterationLoop {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    X ⟶ loop (cone (coneInclusion f)) := by
  let D := cone (coneInclusion f)
  let outer : StrictHomotopy (f ≫ coneInclusion f ≫ coneInclusion (coneInclusion f))
      (zeroMap X D) := {
    hom := f ≫ coneNullPath (coneInclusion f)
    zero := by rw [Category.assoc, coneNullPath_zero]
    one := by rw [Category.assoc, coneNullPath_one]; rfl }
  let inner : StrictHomotopy (f ≫ coneInclusion f ≫ coneInclusion (coneInclusion f))
      (zeroMap X D) := {
    hom := coneNullPath f ≫ pathMap (coneInclusion (coneInclusion f))
    zero := by rw [Category.assoc, pathMap_evaluation, ← Category.assoc, coneNullPath_zero, Category.assoc]
    one := by
      rw [Category.assoc, pathMap_evaluation, ← Category.assoc, coneNullPath_one]
      rfl }
  let H := outer.symm.trans inner
  exact {
    level n := ⟨H.levelPath n, Path.continuous_uncurry_iff.mp
      (show Continuous (fun z : X.level n × I => (H.levelPath n z.1) z.2) from
        ((show C(X.level n,C(I,D.level n)) from H.hom.level n).continuous.comp
          continuous_fst).eval continuous_snd)⟩
    point n := by
      apply Path.ext; funext s
      exact congrArg (fun q : C(I,D.level n) => q s) (H.hom.point n)
    bond n x t := by
      apply Path.ext; funext s
      exact congrArg (fun q : C(I,D.level (n+1)) => q s) (H.hom.bond n x t) }

/-- The reverse Puppe comparison is the actual suspension adjoint of
the two retained cone cylinders. -/
noncomputable def coneIterationInverse {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    X.suspension ⟶ cone (coneInclusion f) :=
  suspensionLoopUncurry (coneIterationLoop f)

end KIP126.StableHomotopy.Implementation.Prespectrum
