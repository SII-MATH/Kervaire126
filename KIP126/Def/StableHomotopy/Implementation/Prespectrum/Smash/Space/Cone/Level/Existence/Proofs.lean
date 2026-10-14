module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Continuity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The cone of the actual smashed map maps to the smash of the literal
mapping cone by its original quotient representatives. -/
theorem spaceSmashConeComparison_exists (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ) :
    ∃! q : coneLevel (spaceSmashMap (𝟙 A) f) n ⟶ A.smash (coneLevel f n),
      (∀ a y, q.map (Quot.mk _ (.inl (BasedSpace.smashPoint A (Y.level n) a y))) =
        BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inl y))) ∧
      (∀ a x t, q.map (Quot.mk _ (.inr (BasedSpace.smashPoint A (X.level n) a x,t))) =
        BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inr (x,t)))) := by
  let i : Y.level n ⟶ coneLevel f n := ⟨(coneInclusion f).level n,rfl⟩
  let c : C(X.level n × I,coneLevel f n) :=
    ⟨fun p => Quot.mk _ (.inr p),continuous_quot_mk.comp continuous_inr⟩
  have cp (t : I) : c ((X.level n).point,t) = (coneLevel f n).point :=
    Quot.sound (ConeRelation.point t)
  let left := BasedSpace.smashMap (𝟙 A) i
  let right := BasedSpace.smashFamily (ContinuousMap.fst : C(A × I,A)) c (fun _ => rfl) cp
  have hl (a : A) (y : Y.level n) : left.map (BasedSpace.smashPoint A (Y.level n) a y) =
      BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inl y)) :=
    (BasedSpace.smashMap_exists (𝟙 A) i).exists.choose_spec a y
  have hr (a : A) (x : X.level n) (t : I) :
      right (BasedSpace.smashPoint A (X.level n) a x,t) =
        BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inr (x,t))) :=
    BasedSpace.smashFamily_apply (ContinuousMap.fst : C(A × I,A)) c (fun _ => rfl) cp a x t
  let raw : C((spaceSmash A Y).level n ⊕ ((spaceSmash A X).level n × I),
      A.smash (coneLevel f n)) :=
    ⟨Sum.elim left.map right,left.map.continuous.sumElim right.continuous⟩
  have respects : ∀ p q, ConeRelation (spaceSmashMap (𝟙 A) f) n p q → raw p = raw q := by
    intro p q h
    cases h with
    | start z =>
      refine Quot.inductionOn z ?_
      rintro ⟨a,x⟩
      change right (BasedSpace.smashPoint A (X.level n) a x,0) =
        left.map ((spaceSmashMap (𝟙 A) f).level n (BasedSpace.smashPoint A (X.level n) a x))
      rw [hr,spaceSmashMap_apply]
      change _ = left.map (BasedSpace.smashPoint A (Y.level n) a (f.level n x))
      rw [hl]
      exact congrArg (BasedSpace.smashPoint A (coneLevel f n) a) (Quot.sound (ConeRelation.start x))
    | finish z =>
      refine Quot.inductionOn z ?_
      rintro ⟨a,x⟩
      change right (BasedSpace.smashPoint A (X.level n) a x,1) = left.map (A.smash (Y.level n)).point
      rw [hr,left.point]
      exact (congrArg (BasedSpace.smashPoint A (coneLevel f n) a)
        (Quot.sound (ConeRelation.finish x))).trans (BasedSpace.smashPoint_base_right _ _ _)
    | point t =>
      change right ((A.smash (X.level n)).point,t) = left.map (A.smash (Y.level n)).point
      rw [left.point]
      exact BasedSpace.smashFamily_point _ _ _ _ t
  let q : coneLevel (spaceSmashMap (𝟙 A) f) n ⟶ A.smash (coneLevel f n) :=
    { map := ⟨Quot.lift raw respects,continuous_quot_lift respects raw.continuous⟩
      point := left.point }
  refine ⟨q,⟨hl,hr⟩,?_⟩
  intro q' hq'
  apply BasedSpace.Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,t⟩)
  · refine Quot.inductionOn y ?_
    rintro ⟨a,y⟩
    exact (hq'.1 a y).trans (hl a y).symm
  · refine Quot.inductionOn x ?_
    rintro ⟨a,x⟩
    exact (hq'.2 a x t).trans (hr a x t).symm

/-- For actual compactly generated source and target levels, smashing
commutes with the ordinary mapping-cone quotient in the reverse direction. -/
theorem spaceSmashConeInverse_exists (A : BasedSpace.{0})
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) (n : ℕ)
    [UCompactlyGeneratedSpace.{0} (X.level n)] [UCompactlyGeneratedSpace.{0} (Y.level n)] :
    ∃! q : A.smash (coneLevel f n) ⟶ coneLevel (spaceSmashMap (𝟙 A) f) n,
      (∀ a y, q.map (BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inl y))) =
        Quot.mk _ (.inl (BasedSpace.smashPoint A (Y.level n) a y))) ∧
      (∀ a x t, q.map (BasedSpace.smashPoint A (coneLevel f n) a (Quot.mk _ (.inr (x,t)))) =
        Quot.mk _ (.inr (BasedSpace.smashPoint A (X.level n) a x,t))) := by
  let g := spaceSmashMap (𝟙 A) f
  let rep (a : A) : Y.level n ⊕ (X.level n × I) → coneLevel g n :=
    Sum.elim (fun y => Quot.mk _ (.inl (BasedSpace.smashPoint A (Y.level n) a y)))
      (fun p => Quot.mk _ (.inr (BasedSpace.smashPoint A (X.level n) a p.1,p.2)))
  have respects (a : A) : ∀ p q, ConeRelation f n p q → rep a p = rep a q := by
    intro p q h
    cases h with
    | start x =>
      change Quot.mk (ConeRelation g n) (.inr (BasedSpace.smashPoint A (X.level n) a x,0)) =
        Quot.mk (ConeRelation g n) (.inl (BasedSpace.smashPoint A (Y.level n) a (f.level n x)))
      have hstart := Quot.sound (ConeRelation.start (f := g) (n := n) (BasedSpace.smashPoint A (X.level n) a x))
      change _ = Quot.mk (ConeRelation g n) (.inl ((spaceSmashMap (𝟙 A) f).level n
        (BasedSpace.smashPoint A (X.level n) a x))) at hstart
      rw [spaceSmashMap_apply] at hstart
      exact hstart
    | finish x =>
      change Quot.mk (ConeRelation g n) (.inr (BasedSpace.smashPoint A (X.level n) a x,1)) =
        Quot.mk (ConeRelation g n) (.inl (BasedSpace.smashPoint A (Y.level n) a (Y.level n).point))
      rw [BasedSpace.smashPoint_base_right]
      exact Quot.sound (ConeRelation.finish _)
    | point t =>
      change Quot.mk (ConeRelation g n) (.inr (BasedSpace.smashPoint A (X.level n) a (X.level n).point,t)) =
        Quot.mk (ConeRelation g n) (.inl (BasedSpace.smashPoint A (Y.level n) a (Y.level n).point))
      rw [BasedSpace.smashPoint_base_right,BasedSpace.smashPoint_base_right]
      exact Quot.sound (ConeRelation.point t)
  let raw : A × coneLevel f n → coneLevel g n :=
    fun p => Quot.lift (rep p.1) (respects p.1) p.2
  have rawK (K : CompHaus.{0}) (α : C(K,A)) :
      Continuous (fun p : coneLevel f n × K => raw (α p.2,p.1)) := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_left
    letI := BasedSpace.compactlyGenerated_prod_compHaus (X.level n) K
    letI := BasedSpace.compactlyGenerated_prod_compHaus (Y.level n) K
    have hx : Continuous (fun p : X.level n × K => BasedSpace.smashPoint A (X.level n) (α p.2) p.1) :=
      BasedSpace.continuous_smashPoint A (X.level n) (α.comp ContinuousMap.snd) ContinuousMap.fst
    have hy : Continuous (fun p : Y.level n × K => BasedSpace.smashPoint A (Y.level n) (α p.2) p.1) :=
      BasedSpace.continuous_smashPoint A (Y.level n) (α.comp ContinuousMap.snd) ContinuousMap.fst
    have hl : Continuous (fun p : Y.level n × K =>
        Quot.mk (ConeRelation g n) (.inl (BasedSpace.smashPoint A (Y.level n) (α p.2) p.1))) :=
      continuous_quot_mk.comp (continuous_inl.comp hy)
    have hr : Continuous (fun p : (X.level n × I) × K =>
        Quot.mk (ConeRelation g n) (.inr (BasedSpace.smashPoint A (X.level n) (α p.2) p.1.1,p.1.2))) :=
      continuous_quot_mk.comp (continuous_inr.comp
        ((hx.comp (continuous_fst.fst.prodMk continuous_snd)).prodMk continuous_fst.snd))
    have hh := (hl.sumElim hr).comp
      (Homeomorph.sumProdDistrib (X := Y.level n) (Y := X.level n × I) (Z := K)).continuous
    apply hh.congr
    rintro ⟨p,k⟩
    cases p <;> rfl
  have hc : Continuous[TopologicalSpace.compactlyGenerated.{0} (A × coneLevel f n),inferInstance] raw := by
    apply continuous_from_compactlyGenerated
    intro K k
    exact (rawK K ⟨fun s => (k s).1,k.continuous.fst⟩).comp
      (k.continuous.snd.prodMk continuous_id)
  have collapsed (p : A × coneLevel f n)
      (hp : p.1 = A.point ∨ p.2 = (coneLevel f n).point) : raw p = (coneLevel g n).point := by
    rcases p with ⟨a,z⟩
    rcases hp with h | h
    · change a = A.point at h
      subst a
      refine Quot.inductionOn z ?_
      rintro (y | ⟨x,t⟩)
      · change Quot.mk (ConeRelation g n) (.inl (BasedSpace.smashPoint A (Y.level n) A.point y)) = _
        rw [BasedSpace.smashPoint_base_left]
        rfl
      · change Quot.mk (ConeRelation g n) (.inr (BasedSpace.smashPoint A (X.level n) A.point x,t)) = _
        rw [BasedSpace.smashPoint_base_left]
        exact Quot.sound (ConeRelation.point t)
    · change z = (coneLevel f n).point at h
      subst z
      change Quot.mk (ConeRelation g n) (.inl (BasedSpace.smashPoint A (Y.level n) a (Y.level n).point)) = _
      rw [BasedSpace.smashPoint_base_right]
      rfl
  have hr : ∀ p q, BasedSpace.SmashRelation A (coneLevel f n) p q → raw p = raw q :=
    fun p q h => (collapsed p h.1).trans (collapsed q h.2).symm
  letI : TopologicalSpace (A × coneLevel f n) := TopologicalSpace.compactlyGenerated.{0} (A × coneLevel f n)
  let q : A.smash (coneLevel f n) ⟶ coneLevel g n :=
    { map := ⟨Quot.lift raw hr,continuous_quot_lift hr hc⟩
      point := collapsed (A.point,(coneLevel f n).point) (Or.inl rfl) }
  refine ⟨q,⟨fun _ _ => rfl,fun _ _ _ => rfl⟩,?_⟩
  intro q' hq'
  apply BasedSpace.Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,z⟩
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,t⟩)
  · exact hq'.1 a y
  · exact hq'.2 a x t

end KIP126.StableHomotopy.Implementation.Prespectrum
