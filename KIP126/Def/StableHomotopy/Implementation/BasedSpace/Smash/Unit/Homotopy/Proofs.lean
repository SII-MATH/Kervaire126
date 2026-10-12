module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Unit.Proofs
public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy
set_option backward.isDefEq.respectTransparency false

/-- Compact maps have an exact continuous section, including the full
compact parameter space of a cubical homotopy. -/
theorem continuousMap_lift_smashUnitComparison (A : BasedSpace.{0}) {D : Type}
    [TopologicalSpace D] [CompactSpace D] [T2Space D] (f : C(D,A)) :
    ∃ g : C(D,zeroSphere.smash A), (smashUnitComparison A).map.comp g = f := by
  refine ⟨⟨fun d => smashPoint zeroSphere A (show zeroSphere from (1 : Fin 2)) (f d),
    continuous_smashPoint_compact zeroSphere A (ContinuousMap.const D (show zeroSphere from (1 : Fin 2))) f⟩,?_⟩
  exact ContinuousMap.ext (fun d => smashUnitComparison_apply A (f d))

theorem smashUnitComparison_homotopicRel_iff (A : BasedSpace.{0}) {D : Type}
    [TopologicalSpace D] [CompactSpace D] [T2Space D]
    (a b : C(D,zeroSphere.smash A)) (S : Set D) :
    ((smashUnitComparison A).map.comp a).HomotopicRel
      ((smashUnitComparison A).map.comp b) S ↔ a.HomotopicRel b S := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨h,hh⟩ := continuousMap_lift_smashUnitComparison A H.toContinuousMap
    have hinj := (smashUnitComparison_bijective A).1
    exact ⟨{
      toContinuousMap := h
      map_zero_left := fun x => hinj ((ContinuousMap.congr_fun hh (0,x)).trans (H.apply_zero x))
      map_one_left := fun x => hinj ((ContinuousMap.congr_fun hh (1,x)).trans (H.apply_one x))
      prop' := fun t x hx => hinj ((ContinuousMap.congr_fun hh (t,x)).trans (H.eq_fst t hx)) }⟩
  · exact fun H => H.comp_continuousMap (smashUnitComparison A).map

theorem genLoop_lift_smashUnitComparison (A : BasedSpace.{0}) (r : ℕ)
    (p : GenLoop (Fin r) A A.point) :
    ∃ q : GenLoop (Fin r) (zeroSphere.smash A) (zeroSphere.smash A).point,
      (smashUnitComparison A).map.comp q.val = p.val := by
  obtain ⟨q,hq⟩ := continuousMap_lift_smashUnitComparison A p.val
  refine ⟨⟨q,?_⟩,hq⟩
  intro t ht
  apply (smashUnitComparison_bijective A).1
  exact (ContinuousMap.congr_fun hq t).trans ((p.property t ht).trans (smashUnitComparison A).point.symm)

end KIP126.StableHomotopy.Implementation.BasedSpace
