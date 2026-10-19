module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.HomotopyMap.Data
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum.HomotopyMap

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u
variable {X Y : Prespectrum.{u}} (f : HomotopyMap X Y)

@[simp] theorem sourceSection_point (n : ℕ) :
    f.sourceSection n (X.level n).point = (f.pathLevel n).point := by
  apply Subtype.ext
  apply Prod.ext <;> try rfl
  apply ContinuousMap.ext
  intro t
  exact f.point n

@[simp] theorem sourceProjection_section (n : ℕ) :
    (f.sourceProjection.level n).comp (f.sourceSection n) = ContinuousMap.id _ := rfl

/-- Shortening each carried path contracts the source projection's fibers
while fixing the specified basepoint throughout. -/
theorem sourceProjection_level_deformation (n : ℕ) :
    ((f.sourceSection n).comp (f.sourceProjection.level n)).HomotopicRel
      (ContinuousMap.id (f.pathLevel n)) {(f.pathLevel n).point} := by
  have hmul : Continuous (fun z : (I × f.pathLevel n) × I => z.1.1 * z.2) :=
    ((continuous_fst.fst.subtype_val.mul continuous_snd.subtype_val).subtype_mk _)
  have hev : Continuous (fun z : (I × f.pathLevel n) × I => z.1.2.val.2 (z.1.1 * z.2)) :=
    continuous_fst.snd.subtype_val.snd.eval hmul
  let paths : C(I × f.pathLevel n, C(I, Y.level n)) :=
    (⟨_, hev⟩ : C((I × f.pathLevel n) × I, Y.level n)).curry
  have hsource (z : I × f.pathLevel n) : paths z 0 = f.level n z.2.val.1 := by
    change z.2.val.2 (z.1 * 0) = f.level n z.2.val.1
    rw [mul_zero]
    exact z.2.property
  refine ⟨{
    toFun := fun z => ⟨(z.2.val.1, paths z), hsource z⟩
    continuous_toFun := (continuous_snd.subtype_val.fst.prodMk paths.continuous).subtype_mk
      (p := fun p : X.level n × C(I, Y.level n) => p.2 0 = f.level n p.1) hsource
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro z
    apply Subtype.ext
    apply Prod.ext <;> try rfl
    apply ContinuousMap.ext
    intro t
    change z.val.2 (0 * t) = f.level n z.val.1
    rw [zero_mul]
    exact z.property
  · intro z
    apply Subtype.ext
    apply Prod.ext <;> try rfl
    apply ContinuousMap.ext
    intro t
    change z.val.2 (1 * t) = z.val.2 t
    rw [one_mul]
  · intro s z hz
    rcases hz with rfl
    apply Subtype.ext
    apply Prod.ext <;> try rfl
    apply ContinuousMap.ext
    intro t
    exact (f.point n).symm

/-- Applying the levelwise deformation to cubical loops preserves the
entire boundary. -/
theorem sourceProjection_loop_deformation (n r : ℕ)
    (p : GenLoop (Fin r) (f.pathLevel n) (f.pathLevel n).point) :
    ((f.sourceSection n).comp ((f.sourceProjection.level n).comp p.val)).HomotopicRel
      p.val (_root_.Cube.boundary (Fin r)) := by
  obtain ⟨H⟩ := f.sourceProjection_level_deformation n
  refine ⟨{
    toFun := fun z => H (z.1, p z.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk
      (p.val.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    exact H.apply_zero (p t)
  · intro t
    exact H.apply_one (p t)
  · intro s t ht
    change H (s, p t) = f.sourceSection n (f.sourceProjection.level n (p t))
    have hp : p t = (f.pathLevel n).point := p.property t ht
    rw [hp]
    exact H.eq_fst s rfl

/-- The left arrow of the strict mapping-path zigzag is a stable equivalence,
proved from its explicit levelwise based contraction. -/
theorem sourceProjection_stableEquivalence : stableEquivalences f.sourceProjection := by
  apply stableEquivalence_of_levelwise_loops
  · intro n r p q hpq
    exact (f.sourceProjection_loop_deformation n r p).symm.trans
      ((hpq.comp_continuousMap (f.sourceSection n)).trans
        (f.sourceProjection_loop_deformation n r q))
  · intro n r p
    let q : GenLoop (Fin r) (f.pathLevel n) (f.pathLevel n).point :=
      ⟨(f.sourceSection n).comp p.val, by
        intro t ht
        change f.sourceSection n (p t) = _
        have hp : p t = (X.level n).point := p.property t ht
        rw [hp, f.sourceSection_point]⟩
    exact ⟨q, GenLoop.Homotopic.refl p⟩

theorem sourceProjection_isIso : IsIso (sourceLocalization.map f.sourceProjection) :=
  stableEquivalences.Q_inverts _ f.sourceProjection_stableEquivalence

/-- The supplied bonding homotopy gives precisely the compatibility needed
by the actual stable-quotient relation. -/
theorem mapLoop_stabilize_homotopic (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
    GenLoop.Homotopic (f.mapLoop (n + 1) (r + 1) (stabilizeLoop X n r p))
      (stabilizeLoop Y n r (f.mapLoop n r p)) := by
  refine ⟨{
    toFun := fun z => f.bondHomotopy n (z.1, (p (fun i => z.2 i.succ), z.2 0))
    continuous_toFun := (f.bondHomotopy n).continuous.comp
      (continuous_fst.prodMk
        ((p.val.continuous.comp (continuous_pi fun i =>
          (continuous_apply i.succ).comp continuous_snd)).prodMk
            ((continuous_apply 0).comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    exact f.bondHomotopy_zero n _ _
  · intro t
    exact f.bondHomotopy_one n _ _
  · intro s t ht
    change f.bondHomotopy n (s, (p (fun i => t i.succ), t 0)) =
      f.mapLoop (n + 1) (r + 1) (stabilizeLoop X n r p) t
    have hb : f.mapLoop (n + 1) (r + 1) (stabilizeLoop X n r p) t =
        (Y.level (n + 1)).point :=
      (f.mapLoop (n + 1) (r + 1) (stabilizeLoop X n r p)).property t ht
    rw [hb]
    apply f.bondHomotopy_collapsed
    obtain ⟨i, hi⟩ := ht
    induction i using Fin.cases with
    | zero => exact Or.inr hi
    | succ i => exact Or.inl (p.property _ ⟨i, hi⟩)

/-- A map commuting with bonds up to the specified homotopy descends to
the stable quotient; no strict compatibility is silently substituted. -/
theorem mapRepresentative_relation {d : ℤ} {a b : Representative X d}
    (h : StableRelation X d a b) :
    (Quot.mk (StableRelation Y d) (f.mapRepresentative a) : StableHomotopy Y d) =
      Quot.mk _ (f.mapRepresentative b) := by
  cases h with
  | homotopy p h =>
    exact Quot.sound (StableRelation.homotopy (f.mapRepresentative a) _
      (h.comp_continuousMap (f.level a.stage)))
  | stabilization =>
    exact (Quot.sound (StableRelation.stabilization (f.mapRepresentative a))).trans
      (Quot.sound (StableRelation.homotopy (f.mapRepresentative a).next _
        (f.mapLoop_stabilize_homotopic a.stage a.dimension a.loop).symm))

end KIP126.StableHomotopy.Implementation.Prespectrum.HomotopyMap
