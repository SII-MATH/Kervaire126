module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Stable.Data
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Rotation.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Suspension.HomotopyMap.Stable.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u
variable (X : Prespectrum.{u})

theorem suspensionDesuspensionInverseLoop_homotopic (n r : ℕ)
    (p q : GenLoop (Fin r) (X.level n) (X.level n).point)
    (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (suspensionDesuspensionInverseLoop X n r p)
      (suspensionDesuspensionInverseLoop X n r q) := by
  obtain ⟨H⟩ := hpq
  refine ⟨{
    toFun := fun z => BasedSpace.suspensionProjection _
      (H (z.1, fun i => z.2 i.succ), suspensionDesuspensionSign n (z.2 0))
    continuous_toFun := (BasedSpace.suspensionProjection _).continuous.comp
      ((H.continuous.comp (continuous_fst.prodMk
        (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))).prodMk
          ((suspensionDesuspensionSign n).continuous.comp ((continuous_apply 0).comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    change BasedSpace.suspensionProjection _ (H (0, _), _) = _
    rw [H.apply_zero]
    rfl
  · intro t
    change BasedSpace.suspensionProjection _ (H (1, _), _) = _
    rw [H.apply_one]
    rfl
  · intro s t ht
    obtain ⟨i, hi⟩ := ht
    induction i using Fin.cases with
    | zero =>
      change BasedSpace.suspensionProjection _ (H (s, _), suspensionDesuspensionSign n (t 0)) =
        BasedSpace.suspensionProjection _ (p _, suspensionDesuspensionSign n (t 0))
      have hb := suspensionDesuspensionSign_boundary n (t 0) hi
      exact (BasedSpace.suspensionProjection_collapsed _ _ (Or.inr hb)).trans
        (BasedSpace.suspensionProjection_collapsed _ _ (Or.inr hb)).symm
    | succ i =>
      change BasedSpace.suspensionProjection _ (H (s, _), _) =
        BasedSpace.suspensionProjection _ (p _, _)
      rw [H.eq_fst s ⟨i, hi⟩]
      rfl

/-- Suspension of a stabilized representative agrees up to the explicitly
constructed square rotation with stabilization of its suspension. -/
theorem suspensionDesuspensionInverseLoop_stabilize (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
    GenLoop.Homotopic
      (stabilizeLoop (desuspension X).suspension (n + 1) (r + 1)
        (suspensionDesuspensionInverseLoop X n r p))
      (suspensionDesuspensionInverseLoop X (n + 1) (r + 1) (stabilizeLoop X n r p)) := by
  obtain ⟨H, h0, h1, hb⟩ := suspensionDesuspension_interchange_exists X n
  let q := suspensionDesuspensionInverseLoop X n r p
  refine ⟨{
    toFun := fun z => H (z.1, (q (fun i => z.2 i.succ), z.2 0))
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk
        ((q.val.continuous.comp (continuous_pi fun i =>
          (continuous_apply i.succ).comp continuous_snd)).prodMk
            ((continuous_apply 0).comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    exact h0 _ _ _
  · intro t
    change H (1, (BasedSpace.suspensionProjection _
      (p (fun i => t i.succ.succ), suspensionDesuspensionSign n (t 1)), t 0)) = _
    rw [h1, suspensionDesuspensionSign_twice]
    rfl
  · intro s t ht
    change H (s, (q (fun i => t i.succ), t 0)) =
      stabilizeLoop (desuspension X).suspension (n + 1) (r + 1) q t
    have hz : stabilizeLoop (desuspension X).suspension (n + 1) (r + 1) q t =
        (X.level (n + 1)).suspension.point :=
      (stabilizeLoop (desuspension X).suspension (n + 1) (r + 1) q).property t ht
    rw [hz]
    apply hb
    obtain ⟨i, hi⟩ := ht
    induction i using Fin.cases with
    | zero => exact Or.inr hi
    | succ i => exact Or.inl (q.property _ ⟨i, hi⟩)

theorem Representative.suspensionDesuspensionInverse_relation {d : ℤ}
    {a b : Representative X d} (h : StableRelation X d a b) :
    (Quot.mk (StableRelation (desuspension X).suspension d)
      (a.suspensionDesuspensionInverse X) : StableHomotopy (desuspension X).suspension d) =
    Quot.mk _ (b.suspensionDesuspensionInverse X) := by
  cases h with
  | homotopy p h =>
    exact Quot.sound (StableRelation.homotopy (a.suspensionDesuspensionInverse X) _
      (suspensionDesuspensionInverseLoop_homotopic X _ _ _ _ h))
  | stabilization =>
    exact (Quot.sound (StableRelation.stabilization (a.suspensionDesuspensionInverse X))).trans
      (Quot.sound (StableRelation.homotopy (a.suspensionDesuspensionInverse X).next _
        (suspensionDesuspensionInverseLoop_stabilize X _ _ _)))

/-- The comparison after its displayed inverse is literally one stabilization. -/
theorem Representative.suspensionDesuspensionComparison_inverse {d : ℤ}
    (a : Representative X d) :
    (suspensionDesuspensionComparison X).mapRepresentative (a.suspensionDesuspensionInverse X) =
      a.next := by
  rcases a with ⟨n, r, hr, p⟩
  unfold HomotopyMap.mapRepresentative Representative.suspensionDesuspensionInverse Representative.next
  congr 1
  apply GenLoop.ext
  intro t
  change X.bond n (p (fun i => t i.succ),
    suspensionDesuspensionSign n (suspensionDesuspensionSign n (t 0))) = _
  rw [suspensionDesuspensionSign_twice]
  rfl

/-- In the opposite order the two displayed maps give one stabilization
up to the same boundary-preserving rotation. -/
theorem suspensionDesuspensionInverse_comparison_homotopic (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n).suspension (X.level n).suspension.point) :
    GenLoop.Homotopic
      (stabilizeLoop (desuspension X).suspension (n + 1) r p)
      (suspensionDesuspensionInverseLoop X (n + 1) r
        ((suspensionDesuspensionComparison X).mapLoop (n + 1) r p)) := by
  obtain ⟨H, h0, h1, hb⟩ := suspensionDesuspension_interchange_exists X n
  refine ⟨{
    toFun := fun z => H (z.1, (p (fun i => z.2 i.succ), z.2 0))
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk
        ((p.val.continuous.comp (continuous_pi fun i =>
          (continuous_apply i.succ).comp continuous_snd)).prodMk
            ((continuous_apply 0).comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    change H (0, (p (fun i => t i.succ), t 0)) =
      BasedSpace.suspensionFamily _ _ (X.bond n) (X.bond_point n)
        (p (fun i => t i.succ), t 0)
    refine Quot.inductionOn (p (fun i => t i.succ)) ?_
    intro w
    exact h0 w.1 w.2 (t 0)
  · intro t
    change H (1, (p (fun i => t i.succ), t 0)) =
      BasedSpace.suspensionProjection _
        ((suspensionDesuspensionComparison X).level (n + 1) (p (fun i => t i.succ)),
          suspensionDesuspensionSign (n + 1) (t 0))
    refine Quot.inductionOn (p (fun i => t i.succ)) ?_
    intro w
    exact h1 w.1 w.2 (t 0)
  · intro s t ht
    change H (s, (p (fun i => t i.succ), t 0)) =
      stabilizeLoop (desuspension X).suspension (n + 1) r p t
    have hz : stabilizeLoop (desuspension X).suspension (n + 1) r p t =
        (X.level (n + 1)).suspension.point :=
      (stabilizeLoop (desuspension X).suspension (n + 1) r p).property t ht
    rw [hz]
    apply hb
    obtain ⟨i, hi⟩ := ht
    induction i using Fin.cases with
    | zero => exact Or.inr hi
    | succ i => exact Or.inl (p.property _ ⟨i, hi⟩)

/-- The explicit suspension/desuspension comparison induces bijections in
every integer stable degree. Both inverse identities are proved from actual
representatives and the square rotation, with no stable-category premise. -/
theorem suspensionDesuspensionComparison_stableMap_bijective (d : ℤ) :
    Function.Bijective ((suspensionDesuspensionComparison X).stableMap d) := by
  let back : StableHomotopy X d → StableHomotopy (desuspension X).suspension d :=
    Quot.lift (fun a => Quot.mk _ (a.suspensionDesuspensionInverse X))
      (fun _ _ h => Representative.suspensionDesuspensionInverse_relation X h)
  have hr : Function.RightInverse back ((suspensionDesuspensionComparison X).stableMap d) := by
    intro x
    induction x using Quot.inductionOn with
    | h a =>
      change Quot.mk _ ((suspensionDesuspensionComparison X).mapRepresentative
        (a.suspensionDesuspensionInverse X)) = Quot.mk _ a
      rw [Representative.suspensionDesuspensionComparison_inverse]
      exact (Quot.sound (StableRelation.stabilization a)).symm
  have hl : Function.LeftInverse back ((suspensionDesuspensionComparison X).stableMap d) := by
    intro x
    obtain ⟨a, ha, hax⟩ := exists_representative_stage_ge x 1
    rw [← hax]
    rcases a with ⟨n, r, hr, p⟩
    cases n with
    | zero => simp only at ha; omega
    | succ n =>
      let a : Representative (desuspension X).suspension d := ⟨n + 1, r, hr, p⟩
      change Quot.mk _ (((suspensionDesuspensionComparison X).mapRepresentative a).suspensionDesuspensionInverse X) =
        Quot.mk _ a
      exact (Quot.sound (StableRelation.homotopy
        (((suspensionDesuspensionComparison X).mapRepresentative a).suspensionDesuspensionInverse X)
        a.next.loop (suspensionDesuspensionInverse_comparison_homotopic X n r p).symm)).trans
          (Quot.sound (StableRelation.stabilization a)).symm
  exact ⟨hl.injective, hr.surjective⟩

/-- Both arrows of the actual strict comparison zigzag are stable equivalences. -/
theorem suspensionDesuspensionComparison_targetProjection_stableEquivalence :
    stableEquivalences (suspensionDesuspensionComparison X).targetProjection :=
  (suspensionDesuspensionComparison X).targetProjection_stableEquivalence
    (suspensionDesuspensionComparison_stableMap_bijective X)

/-- Levelwise suspension inverts the padded desuspension in the actual
source localization, through the proved mapping-path zigzag. -/
theorem suspension_desuspension_source_iso :
    Nonempty (sourceLocalization.obj (desuspension X).suspension ≅ sourceLocalization.obj X) :=
  (suspensionDesuspensionComparison X).source_isomorphic_of_stableMap_bijective
    (suspensionDesuspensionComparison_stableMap_bijective X)

end KIP126.StableHomotopy.Implementation.Prespectrum
