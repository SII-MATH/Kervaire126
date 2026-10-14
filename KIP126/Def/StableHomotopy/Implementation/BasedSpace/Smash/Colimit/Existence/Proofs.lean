module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Continuity.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Associativity.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Colimit.CompactlyGenerated.Proofs
public import Mathlib.CategoryTheory.Limits.IsLimit

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory CategoryTheory.Limits Topology
universe v w
set_option backward.isDefEq.respectTransparency false

/-- The actual quotient smash carries a compactly generated based
colimit to a colimit. Continuity is proved using compact Hausdorff tests
and the original colimit universal property, rather than assumed
preservation of products by arbitrary topological quotients. -/
theorem exists_smash_colimit_desc
    {J : Type v} [Category.{w} J] (F : J ⥤ BasedSpace.{0})
    (c : Cocone F) (hc : IsColimit c)
    [∀ j, UCompactlyGeneratedSpace.{0} (F.obj j)]
    (B Z : BasedSpace.{0}) (s : ∀ j, (F.obj j).smash B ⟶ Z)
    (hs : ∀ {i j} (f : i ⟶ j), smashMap (F.map f) (𝟙 B) ≫ s j = s i) :
    ∃! d : c.pt.smash B ⟶ Z, ∀ j, smashMap (c.ι.app j) (𝟙 B) ≫ d = s j := by
  letI := uCompactlyGeneratedSpace_of_isColimit F c hc
  let a (b : B) : Cocone F := {
    pt := Z
    ι := {
      app j := {
        map := ⟨fun x => (s j).map (smashPoint (F.obj j) B x b),
          (s j).map.continuous.comp
            (continuous_smashPoint (F.obj j) B (ContinuousMap.id _) (ContinuousMap.const _ b))⟩
        point := by
          change (s j).map (smashPoint (F.obj j) B (F.obj j).point b) = Z.point
          rw [smashPoint_base_left,(s j).point] }
      naturality := by
        intro i j f
        apply Hom.ext
        apply ContinuousMap.ext
        intro x
        have h := congrArg (fun g : (F.obj i).smash B ⟶ Z =>
          g.map (smashPoint (F.obj i) B x b)) (hs f)
        change (s j).map ((smashMap (F.map f) (𝟙 B)).map
          (smashPoint (F.obj i) B x b)) = _ at h
        rw [smashMap_apply] at h
        exact h } }
  let raw (p : c.pt × B) : Z := (hc.desc (a p.2)).map p.1
  have raw_fac (j : J) (x : F.obj j) (b : B) :
      raw ((c.ι.app j).map x,b) = (s j).map (smashPoint (F.obj j) B x b) :=
    congrArg (fun g : F.obj j ⟶ Z => g.map x) (hc.fac (a b) j)
  have raw_left (b : B) : raw (c.pt.point,b) = Z.point := (hc.desc (a b)).point
  have raw_right (x : c.pt) : raw (x,B.point) = Z.point := by
    have he : hc.desc (a B.point) =
        (⟨ContinuousMap.const _ Z.point,rfl⟩ : c.pt ⟶ Z) := by
      apply hc.hom_ext
      intro j
      rw [hc.fac]
      apply Hom.ext
      apply ContinuousMap.ext
      intro y
      change (s j).map (smashPoint (F.obj j) B y B.point) = Z.point
      rw [smashPoint_base_right,(s j).point]
    exact congrArg (fun g : c.pt ⟶ Z => g.map x) he
  have hraw : Continuous[TopologicalSpace.compactlyGenerated.{0} (c.pt × B),inferInstance] raw := by
    apply continuous_from_compactlyGenerated
    intro K g
    let ZK : BasedSpace.{0} := ⟨TopCat.of C(K,Z),ContinuousMap.const K Z.point⟩
    let aK : Cocone F := {
      pt := ZK
      ι := {
        app j := {
          map := (⟨fun p : F.obj j × K =>
            (s j).map (smashPoint (F.obj j) B p.1 (g p.2).2),by
              letI := compactlyGenerated_prod_compHaus (F.obj j) K
              exact (s j).map.continuous.comp
                (continuous_smashPoint (F.obj j) B ContinuousMap.fst
                  ⟨fun p => (g p.2).2,g.continuous.snd.comp continuous_snd⟩)⟩ :
            C(F.obj j × K,Z)).curry
          point := by
            apply ContinuousMap.ext
            intro k
            change (s j).map (smashPoint (F.obj j) B (F.obj j).point (g k).2) = Z.point
            rw [smashPoint_base_left,(s j).point] }
        naturality := by
          intro i j f
          apply Hom.ext
          apply ContinuousMap.ext
          intro x
          apply ContinuousMap.ext
          intro k
          have h := congrArg (fun q : (F.obj i).smash B ⟶ Z =>
            q.map (smashPoint (F.obj i) B x (g k).2)) (hs f)
          change (s j).map ((smashMap (F.map f) (𝟙 B)).map
            (smashPoint (F.obj i) B x (g k).2)) = _ at h
          rw [smashMap_apply] at h
          exact h } }
    let ev (k : K) : ZK ⟶ Z := ⟨⟨fun h => h k,continuous_eval_const k⟩,rfl⟩
    have he (k : K) : hc.desc aK ≫ ev k = hc.desc (a (g k).2) := by
      apply hc.hom_ext
      intro j
      rw [← Category.assoc,hc.fac,hc.fac]
      rfl
    have H : Continuous (fun p : c.pt × K => (hc.desc aK).map p.1 p.2) :=
      (hc.desc aK).map.uncurry.continuous
    have he' (k : K) : (hc.desc aK).map (g k).1 k = raw (g k) :=
      congrArg (fun q : c.pt ⟶ Z => q.map (g k).1) (he k)
    exact (H.comp (g.continuous.fst.prodMk continuous_id)).congr (fun k => he' k)
  have collapse (p : c.pt × B) (hp : p.1 = c.pt.point ∨ p.2 = B.point) :
      raw p = Z.point := by
    rcases p with ⟨x,b⟩
    rcases hp with h | h
    · change x = c.pt.point at h
      subst x
      exact raw_left b
    · change b = B.point at h
      subst b
      exact raw_right x
  have hr : ∀ p q, SmashRelation c.pt B p q → raw p = raw q :=
    fun p q h => (collapse p h.1).trans (collapse q h.2).symm
  let d : c.pt.smash B ⟶ Z := {
    map := ⟨Quot.lift raw hr,by
      letI : TopologicalSpace (c.pt × B) := TopologicalSpace.compactlyGenerated.{0} (c.pt × B)
      exact continuous_quot_lift hr hraw⟩
    point := raw_left B.point }
  refine ⟨d,?_,?_⟩
  · intro j
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨x,b⟩
    change d.map ((smashMap (c.ι.app j) (𝟙 B)).map (smashPoint (F.obj j) B x b)) = _
    rw [smashMap_apply]
    exact raw_fac j x b
  · intro d' hd'
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨x,b⟩
    let q : c.pt ⟶ Z := {
      map := ⟨fun y => d'.map (smashPoint c.pt B y b),
        d'.map.continuous.comp
          (continuous_smashPoint c.pt B (ContinuousMap.id _) (ContinuousMap.const _ b))⟩
      point := by
        change d'.map (smashPoint c.pt B c.pt.point b) = Z.point
        rw [smashPoint_base_left,d'.point] }
    have hq : q = hc.desc (a b) := by
      apply hc.hom_ext
      intro j
      rw [hc.fac]
      apply Hom.ext
      apply ContinuousMap.ext
      intro y
      have h := congrArg (fun t : (F.obj j).smash B ⟶ Z =>
        t.map (smashPoint (F.obj j) B y b)) (hd' j)
      change d'.map ((smashMap (c.ι.app j) (𝟙 B)).map
        (smashPoint (F.obj j) B y b)) = _ at h
      rw [smashMap_apply] at h
      exact h
    exact congrArg (fun t : c.pt ⟶ Z => t.map x) hq

end KIP126.StableHomotopy.Implementation.BasedSpace
