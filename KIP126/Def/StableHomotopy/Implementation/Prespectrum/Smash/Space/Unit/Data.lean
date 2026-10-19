module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Unit.Homotopy.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The actual zero-sphere unit comparison, with arbitrary spectrum levels. -/
noncomputable def spaceSmashUnit (X : Prespectrum.{0}) : spaceSmash BasedSpace.zeroSphere X ⟶ X where
  level n := (BasedSpace.smashUnitComparison (X.level n)).map
  point n := (BasedSpace.smashUnitComparison (X.level n)).point
  bond n z t := by
    refine Quot.inductionOn z ?_
    rintro ⟨a,x⟩
    change Fin 2 at a
    fin_cases a
    · change (BasedSpace.smashUnitComparison (X.level (n+1))).map
        ((spaceSmash BasedSpace.zeroSphere X).bond n
          (BasedSpace.smashPoint _ (X.level n) BasedSpace.zeroSphere.point x,t)) =
        X.bond n ((BasedSpace.smashUnitComparison (X.level n)).map
          (BasedSpace.smashPoint _ (X.level n) BasedSpace.zeroSphere.point x),t)
      rw [spaceSmash_bond,BasedSpace.smashPoint_base_left,BasedSpace.smashPoint_base_left,
        (BasedSpace.smashUnitComparison (X.level (n+1))).point,
        (BasedSpace.smashUnitComparison (X.level n)).point,X.bond_point]
    · change (BasedSpace.smashUnitComparison (X.level (n+1))).map
        ((spaceSmash BasedSpace.zeroSphere X).bond n
          (BasedSpace.smashPoint _ (X.level n) (show BasedSpace.zeroSphere from (1 : Fin 2)) x,t)) = _
      rw [spaceSmash_bond,BasedSpace.smashUnitComparison_apply]
      change _ = X.bond n ((BasedSpace.smashUnitComparison (X.level n)).map
        (BasedSpace.smashPoint _ (X.level n) (show BasedSpace.zeroSphere from (1 : Fin 2)) x),t)
      rw [BasedSpace.smashUnitComparison_apply]
end KIP126.StableHomotopy.Implementation.Prespectrum
