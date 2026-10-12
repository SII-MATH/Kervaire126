module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Unit.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

@[simp] theorem smashUnitComparison_apply (A : BasedSpace.{0}) (a : A) :
    (smashUnitComparison A).map (smashPoint zeroSphere A (show zeroSphere from (1 : Fin 2)) a) = a :=
  (smashUnitComparison_exists A).exists.choose_spec a

@[simp] theorem smashUnitComparison_section (A : BasedSpace.{0}) (z : zeroSphere.smash A) :
    smashPoint zeroSphere A (show zeroSphere from (1 : Fin 2)) ((smashUnitComparison A).map z) = z := by
  refine Quot.inductionOn z ?_
  rintro ⟨s,a⟩
  change Fin 2 at s
  fin_cases s
  · change smashPoint zeroSphere A (show zeroSphere from (1 : Fin 2))
      ((smashUnitComparison A).map (smashPoint zeroSphere A zeroSphere.point a)) =
      smashPoint zeroSphere A zeroSphere.point a
    rw [smashPoint_base_left,(smashUnitComparison A).point,smashPoint_base_right]
  · exact congrArg (smashPoint zeroSphere A (show zeroSphere from (1 : Fin 2)))
      (smashUnitComparison_apply A a)

theorem smashUnitComparison_bijective (A : BasedSpace.{0}) :
    Function.Bijective (smashUnitComparison A).map :=
  ⟨Function.HasLeftInverse.injective ⟨_,smashUnitComparison_section A⟩,
   Function.HasRightInverse.surjective ⟨_,smashUnitComparison_apply A⟩⟩

/-- Compact Hausdorff test maps lift continuously through the compactly
generated smash quotient. -/
theorem continuous_smashPoint_compact (A B : BasedSpace.{0}) {D : Type}
    [TopologicalSpace D] [CompactSpace D] [T2Space D] (a : C(D,A)) (b : C(D,B)) :
    Continuous (fun d => smashPoint A B (a d) (b d)) := by
  let S := CompHaus.of D
  let k : C(S,A × B) := ⟨fun d => (a d,b d),a.continuous.prodMk b.continuous⟩
  let ev : (Σ i : (T : CompHaus.{0}) × C(T,A × B),i.fst) → A × B :=
    fun q => q.1.2 q.2
  have hi : Continuous (fun d : D => (⟨⟨S,k⟩,d⟩ :
      Σ i : (T : CompHaus.{0}) × C(T,A × B),i.fst)) :=
    @continuous_sigmaMk _ (fun i : (T : CompHaus.{0}) × C(T,A × B) => i.fst)
      (fun _ => inferInstance) ⟨S,k⟩
  letI : TopologicalSpace (A × B) := TopologicalSpace.coinduced ev inferInstance
  exact continuous_quot_mk.comp ((show Continuous ev from continuous_coinduced_rng).comp hi)

end KIP126.StableHomotopy.Implementation.BasedSpace
