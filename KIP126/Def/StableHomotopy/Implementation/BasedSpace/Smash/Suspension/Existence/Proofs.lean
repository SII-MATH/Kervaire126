module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Family.Evaluation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Moving the suspended compactly generated factor past the smash quotient;
the other factor is an arbitrary based space. -/
theorem smashSuspensionComparison_exists (A B : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A] :
    ∃! f : A.suspension.smash B ⟶ (A.smash B).suspension, ∀ a b t,
      f.map (smashPoint _ B (suspensionProjection A (a,t)) b) =
        suspensionProjection (A.smash B) (smashPoint A B a b,t) := by
  have product_k (K : CompHaus.{0}) : UCompactlyGeneratedSpace.{0} (A × K) := by
    apply uCompactlyGeneratedSpace_of_continuous_maps
    intro Y _ f hf
    let F : A → C(K,Y) := fun a =>
      ⟨fun k => f (a,k),hf K ⟨fun k => (a,k),continuous_const.prodMk continuous_id⟩⟩
    have hF : Continuous F := by
      apply continuous_from_uCompactlyGeneratedSpace
      intro S g
      have hg : Continuous (fun p : S × K => f (g p.1,p.2)) :=
        hf (CompHaus.of (S × K)) ⟨fun p => (g p.1,p.2),(g.continuous.comp continuous_fst).prodMk continuous_snd⟩
      exact (ContinuousMap.curry ⟨_,hg⟩).continuous
    exact ContinuousMap.continuous_uncurry_of_continuous ⟨F,hF⟩
  have into_k (K : CompHaus.{0}) (g : C(K,A × B)) :
      Continuous[inferInstance,TopologicalSpace.compactlyGenerated.{0} (A × B)] g := by
    let ev : (Σ i : (T : CompHaus.{0}) × C(T,A × B),i.fst) → A × B :=
      fun q => q.1.2 q.2
    have hi : Continuous (fun k : K => (⟨⟨K,g⟩,k⟩ :
        Σ i : (T : CompHaus.{0}) × C(T,A × B),i.fst)) :=
      @continuous_sigmaMk _ (fun i : (T : CompHaus.{0}) × C(T,A × B) => i.fst)
        (fun _ => inferInstance) ⟨K,g⟩
    letI : TopologicalSpace (A × B) := TopologicalSpace.coinduced ev inferInstance
    exact (show Continuous ev from continuous_coinduced_rng).comp hi
  have smashK (K : CompHaus.{0}) (β : C(K,B)) :
      Continuous (fun p : A × K => smashPoint A B p.1 (β p.2)) := by
    letI : UCompactlyGeneratedSpace.{0} (A × K) := product_k K
    have hk : Continuous[inferInstance,TopologicalSpace.compactlyGenerated.{0} (A × B)]
        (fun p : A × K => (p.1,β p.2)) := by
      refine @continuous_from_uCompactlyGeneratedSpace.{0} (A × K) (A × B)
        inferInstance (TopologicalSpace.compactlyGenerated.{0} (A × B)) inferInstance _ ?_
      intro S g
      exact into_k S ⟨fun s => ((g s).1,β (g s).2),
        g.continuous.fst.prodMk (β.continuous.comp g.continuous.snd)⟩
    letI : TopologicalSpace (A × B) := TopologicalSpace.compactlyGenerated.{0} (A × B)
    exact continuous_quot_mk.comp hk
  have inner_collapsed (b : B) (p : A × I) (hp : SuspensionCollapsed A p) :
      suspensionProjection (A.smash B) (smashPoint A B p.1 b,p.2) = (A.smash B).suspension.point := by
    rcases hp with h | h | h
    · rw [h,smashPoint_base_left]
      exact suspensionProjection_collapsed _ _ (Or.inl rfl)
    · exact suspensionProjection_collapsed _ _ (Or.inr (Or.inl h))
    · exact suspensionProjection_collapsed _ _ (Or.inr (Or.inr h))
  let raw : A.suspension × B → (A.smash B).suspension := fun p =>
    Quot.lift (fun q : A × I => suspensionProjection (A.smash B) (smashPoint A B q.1 p.2,q.2))
      (fun q r h => (inner_collapsed p.2 q h.1).trans (inner_collapsed p.2 r h.2).symm) p.1
  have rawK (K : CompHaus.{0}) (β : C(K,B)) :
      Continuous (fun p : A.suspension × K => raw (p.1,β p.2)) := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_left
    change Continuous (fun p : (A × I) × K =>
      suspensionProjection (A.smash B) (smashPoint A B p.1.1 (β p.2),p.1.2))
    exact (suspensionProjection (A.smash B)).continuous.comp
      (((smashK K β).comp (continuous_fst.fst.prodMk continuous_snd)).prodMk continuous_fst.snd)
  have hc : Continuous[TopologicalSpace.compactlyGenerated.{0} (A.suspension × B),inferInstance] raw := by
    apply continuous_from_compactlyGenerated
    intro K g
    exact (rawK K ⟨fun k => (g k).2,g.continuous.snd⟩).comp
      (g.continuous.fst.prodMk continuous_id)
  have collapsed (p : A.suspension × B) (hp : p.1 = A.suspension.point ∨ p.2 = B.point) :
      raw p = (A.smash B).suspension.point := by
    rcases hp with h | h
    · rcases p with ⟨a,b⟩
      dsimp only [Prod.fst] at h
      subst a
      exact inner_collapsed b (A.point,0) (Or.inl rfl)
    · rcases p with ⟨a,b⟩
      dsimp only [Prod.snd] at h
      subst b
      refine Quot.inductionOn a ?_
      intro p
      change suspensionProjection (A.smash B) (smashPoint A B p.1 B.point,p.2) = _
      rw [smashPoint_base_right]
      exact suspensionProjection_collapsed _ _ (Or.inl rfl)
  have respects : ∀ p q, SmashRelation A.suspension B p q → raw p = raw q :=
    fun p q h => (collapsed p h.1).trans (collapsed q h.2).symm
  letI : TopologicalSpace (A.suspension × B) :=
    TopologicalSpace.compactlyGenerated.{0} (A.suspension × B)
  let f : A.suspension.smash B ⟶ (A.smash B).suspension :=
    { map := ⟨Quot.lift raw respects,continuous_quot_lift respects hc⟩
      point := collapsed (A.suspension.point,B.point) (Or.inl rfl) }
  refine ⟨f,fun _ _ _ => rfl,?_⟩
  intro g hg
  apply Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,b⟩
  refine Quot.inductionOn a ?_
  rintro ⟨a,t⟩
  exact hg a b t


/-- The inverse interchange is constructed from an actual based family
before descending the reduced-suspension quotient. -/
theorem smashSuspensionInverse_exists (A B : BasedSpace.{0}) :
    ∃! f : (A.smash B).suspension ⟶ A.suspension.smash B, ∀ a b t,
      f.map (suspensionProjection (A.smash B) (smashPoint A B a b,t)) =
        smashPoint A.suspension B (suspensionProjection A (a,t)) b := by
  let F := smashFamily (suspensionProjection A) (ContinuousMap.fst : C(B × I,B))
    (fun t => suspensionProjection_collapsed A (A.point,t) (Or.inl rfl)) (fun _ => rfl)
  have hF (a : A) (b : B) (t : I) : F (smashPoint A B a b,t) =
      smashPoint A.suspension B (suspensionProjection A (a,t)) b :=
    smashFamily_apply (suspensionProjection A) (ContinuousMap.fst : C(B × I,B))
      (fun t => suspensionProjection_collapsed A (A.point,t) (Or.inl rfl)) (fun _ => rfl) a b t
  have collapsed (p : (A.smash B) × I) (hp : SuspensionCollapsed (A.smash B) p) :
      F p = (A.suspension.smash B).point := by
    rcases hp with h | h | h
    · rcases p with ⟨z,t⟩
      dsimp only [Prod.fst] at h
      subst z
      exact smashFamily_point _ _ _ _ t
    · rcases p with ⟨z,t⟩
      dsimp only [Prod.snd] at h
      subst t
      refine Quot.inductionOn z ?_
      rintro ⟨a,b⟩
      change F (smashPoint A B a b,0) = _
      rw [hF,suspensionProjection_collapsed A (a,0) (Or.inr (Or.inl rfl)),smashPoint_base_left]
    · rcases p with ⟨z,t⟩
      dsimp only [Prod.snd] at h
      subst t
      refine Quot.inductionOn z ?_
      rintro ⟨a,b⟩
      change F (smashPoint A B a b,1) = _
      rw [hF,suspensionProjection_collapsed A (a,1) (Or.inr (Or.inr rfl)),smashPoint_base_left]
  have respects : ∀ p q, SuspensionRelation (A.smash B) p q → F p = F q :=
    fun p q h => (collapsed p h.1).trans (collapsed q h.2).symm
  let f : (A.smash B).suspension ⟶ A.suspension.smash B :=
    { map := ⟨Quot.lift F respects,continuous_quot_lift respects F.continuous⟩
      point := collapsed _ (Or.inl rfl) }
  refine ⟨f,hF,?_⟩
  intro g hg
  apply Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨z,t⟩
  refine Quot.inductionOn z ?_
  rintro ⟨a,b⟩
  exact (hg a b t).trans (hF a b t).symm

end KIP126.StableHomotopy.Implementation.BasedSpace
