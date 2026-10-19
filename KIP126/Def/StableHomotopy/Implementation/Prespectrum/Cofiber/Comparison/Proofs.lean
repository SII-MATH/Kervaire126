module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Proofs
public import KIP126.Def.Topology.HomotopyExtension.Predicates

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual extension of the specified cone cylinder supplies a based
homotopy inverse of the original cone-to-quotient comparison. -/
theorem coneToCofiber_level_homotopyInverse_of_extension {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (H : C(Y.level n × I,coneLevel f n))
    (hH0 : ∀ y, H (y,0) = (coneInclusion f).level n y)
    (hHf : ∀ x t, H (f.level n x,t) = Quot.mk (ConeRelation f n) (.inr (x,t))) :
    ∃ r : C(cofiberLevel f n,coneLevel f n),
      r (cofiberLevel f n).point = (coneLevel f n).point ∧
      (r.comp ((coneToCofiber f).level n)).HomotopicRel (ContinuousMap.id _) {(coneLevel f n).point} ∧
      (((coneToCofiber f).level n).comp r).HomotopicRel (ContinuousMap.id _) {(cofiberLevel f n).point} := by
  let C := coneLevel f n
  let Q := cofiberLevel f n
  let i : C(Y.level n,C) := (coneInclusion f).level n
  let c : C(X.level n × I,C) := ⟨fun p => Quot.mk _ (.inr p),continuous_quot_mk.comp continuous_inr⟩
  let q : C(C,Q) := (coneToCofiber f).level n
  change ∀ (x : X.level n) (t : I), H (f.level n x,t) = c (x,t) at hHf
  have hHp (t : I) : H ((Y.level n).point,t) = C.point := by
    rw [← f.point n,hHf]
    exact Quot.sound (ConeRelation.point t)
  have hH1 (x : X.level n) : H (f.level n x,1) = C.point := by
    rw [hHf]
    exact Quot.sound (ConeRelation.finish x)
  have hHq (x : X.level n) (t : I) : q (H (f.level n x,t)) = Q.point := by
    rw [hHf]
    rfl
  have hr : ∀ y z, CofiberRelation f n y z → H (y,1) = H (z,1) := by
    rintro y z ⟨⟨x,rfl⟩,⟨x',rfl⟩⟩
    exact (hH1 x).trans (hH1 x').symm
  let r : C(Q,C) := ⟨Quot.lift (fun y => H (y,1)) hr,
    continuous_quot_lift hr (H.continuous.comp (continuous_id.prodMk continuous_const))⟩
  have rp : r Q.point = C.point := hHp 1
  let m : I × I → I := fun p => unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2)
  have hm : Continuous m := by
    apply unitInterval.continuous_symm.comp
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp unitInterval.continuous_symm).comp continuous_fst).mul
      ((continuous_subtype_val.comp unitInterval.continuous_symm).comp continuous_snd)
  have m0 (s : I) : m (s,0) = s := by simp [m]
  have m1 (s : I) : m (s,1) = 1 := by simp [m]
  have m0' (t : I) : m (0,t) = t := by simp [m]
  have m1' (t : I) : m (1,t) = 1 := by simp [m]
  let raw (t : I) : Y.level n ⊕ (X.level n × I) → C :=
    Sum.elim (fun y => H (y,t)) (fun p => c (p.1,m (p.2,t)))
  have raw_rel (t : I) : ∀ a b, ConeRelation f n a b → raw t a = raw t b := by
    intro a b hab
    cases hab with
    | start x =>
      change c (x,m (0,t)) = H (f.level n x,t)
      rw [m0',hHf]
    | finish x =>
      change c (x,m (1,t)) = H ((Y.level n).point,t)
      rw [m1',hHp]
      exact Quot.sound (ConeRelation.finish x)
    | point s =>
      change c ((X.level n).point,m (s,t)) = H ((Y.level n).point,t)
      rw [hHp]
      exact Quot.sound (ConeRelation.point _)
  let G : C × I → C := fun p => Quot.lift (raw p.2) (raw_rel p.2) p.1
  have hG : Continuous G := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_left
    have hc : Continuous (fun p : (X.level n × I) × I => c (p.1.1,m (p.1.2,p.2))) :=
      c.continuous.comp (continuous_fst.fst.prodMk (hm.comp (continuous_fst.snd.prodMk continuous_snd)))
    have hh := (H.continuous.sumElim hc).comp
      (Homeomorph.sumProdDistrib (X := Y.level n) (Y := X.level n × I) (Z := I)).continuous
    apply hh.congr
    rintro ⟨p,t⟩
    cases p <;> rfl
  have hG0 (z : C) : G (z,0) = z := by
    refine Quot.inductionOn z ?_
    rintro (y | ⟨x,s⟩)
    · exact hH0 y
    · change c (x,m (s,0)) = c (x,s)
      rw [m0]
  have hG1 (z : C) : G (z,1) = r (q z) := by
    refine Quot.inductionOn z ?_
    rintro (y | ⟨x,s⟩)
    · rfl
    · change c (x,m (s,1)) = r Q.point
      rw [m1,rp]
      exact Quot.sound (ConeRelation.finish x)
  have hGp (t : I) : G (C.point,t) = C.point := hHp t
  have qr : ∀ (t : I) y z, CofiberRelation f n y z → q (H (y,t)) = q (H (z,t)) := by
    rintro t y z ⟨⟨x,rfl⟩,⟨x',rfl⟩⟩
    exact (hHq x t).trans (hHq x' t).symm
  let K : Q × I → Q := fun p => Quot.lift (fun y => q (H (y,p.2))) (qr p.2) p.1
  have hK : Continuous K := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_left
    exact q.continuous.comp H.continuous
  have hK0 (z : Q) : K (z,0) = z := by
    refine Quot.inductionOn z ?_
    intro y
    change q (H (y,0)) = Quot.mk (CofiberRelation f n) y
    rw [hH0]
    rfl
  have hK1 (z : Q) : K (z,1) = q (r z) := by
    refine Quot.inductionOn z ?_
    intro y
    rfl
  have hKp (t : I) : K (Q.point,t) = Q.point := by
    change q (H ((Y.level n).point,t)) = Q.point
    rw [hHp]
    exact (coneToCofiber f).point n
  refine ⟨r,rp,?_,?_⟩
  · apply ContinuousMap.HomotopicRel.symm
    exact ⟨{
      toContinuousMap := ⟨fun p => G (p.2,p.1),hG.comp continuous_swap⟩
      map_zero_left := hG0
      map_one_left := hG1
      prop' := fun t z hz => by
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact hGp t }⟩
  · apply ContinuousMap.HomotopicRel.symm
    exact ⟨{
      toContinuousMap := ⟨fun p => K (p.2,p.1),hK.comp continuous_swap⟩
      map_zero_left := hK0
      map_one_left := hK1
      prop' := fun t z hz => by
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact hKp t }⟩

/-- Actual homotopy extension of the displayed level map supplies a
based homotopy inverse of the canonical cone-to-quotient map. -/
theorem coneToCofiber_level_homotopyInverse_exists {X Y : Prespectrum.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (hf : KIP126.Topology.HomotopyExtension.HasHomotopyExtension (TopCat.ofHom (f.level n))) :
    ∃ r : C(cofiberLevel f n,coneLevel f n),
      r (cofiberLevel f n).point = (coneLevel f n).point ∧
      (r.comp ((coneToCofiber f).level n)).HomotopicRel (ContinuousMap.id _) {(coneLevel f n).point} ∧
      (((coneToCofiber f).level n).comp r).HomotopicRel (ContinuousMap.id _) {(cofiberLevel f n).point} := by
  let c : C(X.level n × I,coneLevel f n) :=
    ⟨fun p => Quot.mk _ (.inr p),continuous_quot_mk.comp continuous_inr⟩
  obtain ⟨H,hH0,hHf⟩ := hf (coneLevel f n).space ((coneInclusion f).level n) c
    (fun x => Quot.sound (ConeRelation.start x))
  exact coneToCofiber_level_homotopyInverse_of_extension f n H hH0 hHf

end KIP126.StableHomotopy.Implementation.Prespectrum
