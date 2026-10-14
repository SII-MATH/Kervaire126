module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Unit

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

/-- Smash representatives vary continuously on any compactly generated
parameter space. -/
theorem continuous_smashPoint {D : Type} [TopologicalSpace D]
    [UCompactlyGeneratedSpace.{0} D] (A B : BasedSpace.{0}) (a : C(D,A)) (b : C(D,B)) :
    Continuous (fun d => smashPoint A B (a d) (b d)) := by
  apply continuous_from_uCompactlyGeneratedSpace
  intro K k
  exact continuous_smashPoint_compact A B (a.comp k) (b.comp k)

/-- Products with a compact Hausdorff parameter retain the actual
compact-generation topology. -/
theorem compactlyGenerated_prod_compHaus (X : Type) [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{0} X] (K : CompHaus.{0}) :
    UCompactlyGeneratedSpace.{0} (X × K) := by
  apply uCompactlyGeneratedSpace_of_continuous_maps
  intro Y _ f hf
  let F : X → C(K,Y) := fun x =>
    ⟨fun k => f (x,k),hf K ⟨fun k => (x,k),continuous_const.prodMk continuous_id⟩⟩
  have hF : Continuous F := by
    apply continuous_from_uCompactlyGeneratedSpace
    intro S g
    have hg : Continuous (fun p : S × K => f (g p.1,p.2)) :=
      hf (CompHaus.of (S × K)) ⟨fun p => (g p.1,p.2),
        (g.continuous.comp continuous_fst).prodMk continuous_snd⟩
    exact (ContinuousMap.curry ⟨_,hg⟩).continuous
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨F,hF⟩

end KIP126.StableHomotopy.Implementation.BasedSpace
