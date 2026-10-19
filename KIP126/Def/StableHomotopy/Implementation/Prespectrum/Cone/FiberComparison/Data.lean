module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Adjunction.Hom.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory _root_.Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual fiber path and the original cone cylinder define a strict
map from the fiber to the loops of the literal cone. The cone cylinder is
traversed backwards, followed by the retained fiber path. -/
noncomputable def fiberConeLoop {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiber f ⟶ loop (cone f) := by
  let D := cone f
  let outer : StrictHomotopy
      (fiberProjection f ≫ f ≫ coneInclusion f) (zeroMap (fiber f) D) := {
    hom := fiberProjection f ≫ coneNullPath f
    zero := by rw [Category.assoc, coneNullPath_zero]
    one := by rw [Category.assoc, coneNullPath_one]; rfl }
  let inner : StrictHomotopy
      (fiberProjection f ≫ f ≫ coneInclusion f) (zeroMap (fiber f) D) := {
    hom := fiberNullPath f ≫ pathMap (coneInclusion f)
    zero := by
      rw [Category.assoc, pathMap_evaluation, ← Category.assoc,
        fiberNullPath_zero, Category.assoc]
    one := by
      rw [Category.assoc, pathMap_evaluation, ← Category.assoc, fiberNullPath_one]
      rfl }
  let H := outer.symm.trans inner
  exact {
    level n := ⟨H.levelPath n, Path.continuous_uncurry_iff.mp
      (show Continuous (fun z : (fiber f).level n × I => (H.levelPath n z.1) z.2) from
        ((show C((fiber f).level n,C(I,D.level n)) from H.hom.level n).continuous.comp
          continuous_fst).eval continuous_snd)⟩
    point n := by
      apply Path.ext
      funext s
      exact congrArg (fun q : C(I,D.level n) => q s) (H.hom.point n)
    bond n x t := by
      apply Path.ext
      funext s
      exact congrArg (fun q : C(I,D.level (n+1)) => q s) (H.hom.bond n x t) }

end KIP126.StableHomotopy.Implementation.Prespectrum
