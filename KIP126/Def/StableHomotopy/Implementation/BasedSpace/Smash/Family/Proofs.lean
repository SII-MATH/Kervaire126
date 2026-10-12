module

public import KIP126.Def.StableHomotopy.Implementation.Generators

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Smashing two actual continuous based families gives a continuous
based family on the compactly generated smash, with the original quotient
representative formula. No CW or well-based hypothesis is needed. -/
theorem smashFamily_exists {A B A' B' : BasedSpace.{0}}
    (f : C(A × I,A')) (g : C(B × I,B'))
    (hf : ∀ t, f (A.point,t) = A'.point)
    (hg : ∀ t, g (B.point,t) = B'.point) :
    ∃! H : C((A.smash B) × I,A'.smash B'),
      (∀ a b t, H (smashPoint A B a b,t) =
        smashPoint A' B' (f (a,t)) (g (b,t))) ∧
      (∀ t, H ((A.smash B).point,t) = (A'.smash B').point) := by
  have kc (S : CompHaus.{0}) (k : C(S,A' × B')) :
      Continuous (fun s => smashPoint A' B' (k s).1 (k s).2) := by
    let ev : (Σ i : (T : CompHaus.{0}) × C(T,A' × B'),i.fst) → A' × B' :=
      fun q => q.1.2 q.2
    have hi : Continuous (fun s : S => (⟨⟨S,k⟩,s⟩ :
        Σ i : (T : CompHaus.{0}) × C(T,A' × B'),i.fst)) :=
      @continuous_sigmaMk _ (fun i : (T : CompHaus.{0}) × C(T,A' × B') => i.fst)
        (fun _ => inferInstance) ⟨S,k⟩
    letI : TopologicalSpace (A' × B') := TopologicalSpace.coinduced ev inferInstance
    exact continuous_quot_mk.comp ((show Continuous ev from continuous_coinduced_rng).comp hi)
  let family (p : A × B) : C(I,A'.smash B') :=
    ⟨fun t => smashPoint A' B' (f (p.1,t)) (g (p.2,t)),
      kc (CompHaus.of I) ⟨fun t => (f (p.1,t),g (p.2,t)),
        (f.continuous.comp (continuous_const.prodMk continuous_id)).prodMk
          (g.continuous.comp (continuous_const.prodMk continuous_id))⟩⟩
  have hc : Continuous[TopologicalSpace.compactlyGenerated.{0} (A × B),inferInstance]
      family := by
    apply continuous_from_compactlyGenerated
    intro S k
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact kc (CompHaus.of (S × I)) ⟨fun p => (f ((k p.1).1,p.2),g ((k p.1).2,p.2)),
      (f.continuous.comp ((k.continuous.fst.comp continuous_fst).prodMk continuous_snd)).prodMk
        (g.continuous.comp ((k.continuous.snd.comp continuous_fst).prodMk continuous_snd))⟩
  have collapsed (p : A × B) (hp : p.1 = A.point ∨ p.2 = B.point) :
      family p = ContinuousMap.const I (A'.smash B').point := by
    apply ContinuousMap.ext
    intro t
    change smashPoint A' B' (f (p.1,t)) (g (p.2,t)) = (A'.smash B').point
    rcases hp with h | h
    · rw [h,hf,smashPoint_base_left]
    · rw [h,hg,smashPoint_base_right]
  have respects : ∀ p q, SmashRelation A B p q → family p = family q :=
    fun p q h => (collapsed p h.1).trans (collapsed q h.2).symm
  letI : TopologicalSpace (A × B) := TopologicalSpace.compactlyGenerated.{0} (A × B)
  let H : C((A.smash B) × I,A'.smash B') :=
    (⟨Quot.lift family respects,continuous_quot_lift respects hc⟩ :
      C(A.smash B,C(I,A'.smash B'))).uncurry
  refine ⟨H,⟨fun _ _ _ => rfl,?_⟩,?_⟩
  · intro t
    exact congrArg (fun p : C(I,A'.smash B') => p t)
      (collapsed (A.point,B.point) (Or.inl rfl))
  · intro H' hH'
    apply ContinuousMap.ext
    rintro ⟨z,t⟩
    refine Quot.inductionOn z ?_
    rintro ⟨a,b⟩
    exact hH'.1 a b t

end KIP126.StableHomotopy.Implementation.BasedSpace
