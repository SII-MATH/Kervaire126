module

public import KIP126.Def.StableHomotopy.Implementation.Generators

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

universe u

/-- The actual quotient k-smash already has a compactly generated
topology, independently of any properties of its two original inputs. -/
theorem smash_uCompactlyGeneratedSpace (X Y : BasedSpace.{u}) :
    UCompactlyGeneratedSpace.{u} (X.smash Y) := by
  have hcg : @UCompactlyGeneratedSpace.{u} (X × Y)
      (TopologicalSpace.compactlyGenerated.{u} (X × Y)) := by
    let ev : (Σ i : (S : CompHaus.{u}) × C(S, X × Y), i.fst) → X × Y :=
      fun p => p.1.2 p.2
    letI : TopologicalSpace (X × Y) := TopologicalSpace.coinduced ev inferInstance
    exact uCompactlyGeneratedSpace_of_coinduced
      (show Continuous ev from continuous_coinduced_rng) rfl
  letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
  letI : UCompactlyGeneratedSpace.{u} (X × Y) := hcg
  exact uCompactlyGeneratedSpace_of_coinduced
    (show Continuous (Quot.mk (SmashRelation X Y)) from continuous_quot_mk) rfl

end KIP126.StableHomotopy.Implementation.BasedSpace
