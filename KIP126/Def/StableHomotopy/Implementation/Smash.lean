import KIP126.Def.StableHomotopy.Implementation.Generators

/-! A genuine sequential model of the derived smash. The even level 2n is
Xₙ∧Yₙ, and the intervening odd level is its suspension. Thus both suspension
coordinates are accounted for; Xₙ∧Yₙ is never incorrectly put in level n.
All point-set maps are fixed on quotient representatives. -/
namespace KIP126.StableHomotopy.Implementation
open CategoryTheory Topology
open scoped unitInterval
namespace Prespectrum

/-- Levelwise compactly generated, well-based objects of based CW homotopy type. -/
def IsGood (X : Prespectrum.{0}) : Prop := ∀ n, (X.level n).IsGood

theorem IsGood.wellBased {X : Prespectrum.{0}} (hX : X.IsGood) : X.IsWellBased :=
  fun n => (hX n).2.1

/-- These objects cover the entire ordinary stable localization. -/
theorem goodReplacement (X : Prespectrum.{0}) :
    ∃ (Y : Prespectrum.{0}) (_ : Y.IsGood) (q : Y ⟶ X), stableEquivalences q := by sorry

def tail (X : Prespectrum.{0}) : Prespectrum.{0} where
  level n := X.level (n+1)
  bond n := X.bond (n+1)
  bond_point n := X.bond_point (n+1)
  bond_zero n := X.bond_zero (n+1)
  bond_one n := X.bond_one (n+1)

def tailMap {X Y : Prespectrum.{0}} (f : X ⟶ Y) : X.tail ⟶ Y.tail where
  level n := f.level (n+1)
  point n := f.point (n+1)
  bond n := f.bond (n+1)

/-- Two consecutive bonds, on their actual quotient representatives. -/
theorem pairedBond_exists (X Y : Prespectrum.{0}) :
    ∃! b : C((X.level 0 |>.smash (Y.level 0)).suspension × I,
        (X.level 1).smash (Y.level 1)),
      (∀ x y s t,
        b (BasedSpace.suspensionProjection _ (BasedSpace.smashPoint _ _ x y,s),t) =
          BasedSpace.smashPoint _ _ (X.bond 0 (x,s)) (Y.bond 0 (y,t))) ∧
      (∀ t, b (((X.level 0).smash (Y.level 0)).suspension.point,t) =
        ((X.level 1).smash (Y.level 1)).point) ∧
      (∀ a, b (a,0) = ((X.level 1).smash (Y.level 1)).point) ∧
      (∀ a, b (a,1) = ((X.level 1).smash (Y.level 1)).point) := by
  have kc (S : CompHaus.{0}) (k : C(S, X.level 1 × Y.level 1)) :
      Continuous (fun s : S => BasedSpace.smashPoint (X.level 1) (Y.level 1) (k s).1 (k s).2) := by
    let ev : (Σ i : (T : CompHaus.{0}) × C(T, X.level 1 × Y.level 1), i.fst) →
        X.level 1 × Y.level 1 := fun q => q.1.2 q.2
    have hi : Continuous (fun s : S => (⟨⟨S,k⟩,s⟩ :
        Σ i : (T : CompHaus.{0}) × C(T, X.level 1 × Y.level 1), i.fst)) :=
      @continuous_sigmaMk _ (fun i : (T : CompHaus.{0}) × C(T, X.level 1 × Y.level 1) => i.fst)
        (fun _ => inferInstance) ⟨S,k⟩
    letI : TopologicalSpace (X.level 1 × Y.level 1) := TopologicalSpace.coinduced ev inferInstance
    exact continuous_quot_mk.comp ((show Continuous ev from continuous_coinduced_rng).comp hi)
  let family (p : X.level 0 × Y.level 0) :
      C(I, C(I, (X.level 1).smash (Y.level 1))) :=
    (⟨fun st : I × I => BasedSpace.smashPoint _ _ (X.bond 0 (p.1,st.1)) (Y.bond 0 (p.2,st.2)),
      kc (CompHaus.of (I × I)) ⟨_,
        ((X.bond 0).continuous.comp (continuous_const.prodMk continuous_fst)).prodMk
          ((Y.bond 0).continuous.comp (continuous_const.prodMk continuous_snd))⟩⟩ :
      C(I × I, (X.level 1).smash (Y.level 1))).curry
  have hf : Continuous[TopologicalSpace.compactlyGenerated.{0} (X.level 0 × Y.level 0),
      inferInstance] family := by
    refine @continuous_from_compactlyGenerated (X.level 0 × Y.level 0) _ _ _ family ?_
    intro S k
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact kc (CompHaus.of ((S × I) × I)) ⟨fun p =>
      (X.bond 0 ((k p.1.1).1,p.1.2), Y.bond 0 ((k p.1.1).2,p.2)),
      ((X.bond 0).continuous.comp ((k.continuous.fst.comp continuous_fst.fst).prodMk
        continuous_fst.snd)).prodMk
      ((Y.bond 0).continuous.comp ((k.continuous.snd.comp continuous_fst.fst).prodMk
        continuous_snd))⟩
  let raw (p : (X.level 0 × Y.level 0) × (I × I)) : (X.level 1).smash (Y.level 1) :=
    BasedSpace.smashPoint _ _ (X.bond 0 (p.1.1,p.2.1)) (Y.bond 0 (p.1.2,p.2.2))
  have collapsed (p : X.level 0 × Y.level 0) (st : I × I)
      (hp : p.1 = (X.level 0).point ∨ p.2 = (Y.level 0).point) :
      raw (p,st) = ((X.level 1).smash (Y.level 1)).point := by
    rcases hp with h | h
    · dsimp [raw]
      rw [h, X.bond_point]
      exact BasedSpace.smashPoint_base_left _ _ _
    · dsimp [raw]
      rw [h, Y.bond_point]
      exact BasedSpace.smashPoint_base_right _ _ _
  have hr (st : I × I) : ∀ a b, BasedSpace.SmashRelation (X.level 0) (Y.level 0) a b →
      raw (a,st) = raw (b,st) :=
    fun a b h => (collapsed a st h.1).trans (collapsed b st h.2).symm
  let mid (p : (X.level 0).smash (Y.level 0) × (I × I)) :=
    Quot.lift (fun q => raw (q,p.2)) (hr p.2) p.1
  have hm : Continuous mid := by
    letI : TopologicalSpace (X.level 0 × Y.level 0) :=
      TopologicalSpace.compactlyGenerated.{0} (X.level 0 × Y.level 0)
    apply isQuotientMap_quot_mk.continuous_lift_prod_left
    exact ((⟨family,hf⟩ : C(X.level 0 × Y.level 0,
      C(I,C(I,(X.level 1).smash (Y.level 1))))).uncurry.uncurry.continuous).comp
      ((continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd)
  have mid_left (s t : I) : mid (((X.level 0).smash (Y.level 0)).point,(s,t)) =
      ((X.level 1).smash (Y.level 1)).point := collapsed _ _ (Or.inl rfl)
  have mid_zero (a : (X.level 0).smash (Y.level 0)) (t : I) :
      mid (a,(0,t)) = ((X.level 1).smash (Y.level 1)).point := by
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,0)) (Y.bond 0 (y,t)) = _
    rw [X.bond_zero]
    exact BasedSpace.smashPoint_base_left _ _ _
  have mid_one (a : (X.level 0).smash (Y.level 0)) (t : I) :
      mid (a,(1,t)) = ((X.level 1).smash (Y.level 1)).point := by
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,1)) (Y.bond 0 (y,t)) = _
    rw [X.bond_one]
    exact BasedSpace.smashPoint_base_left _ _ _
  have collapse_outer (p : (X.level 0).smash (Y.level 0) × I) (t : I)
      (hp : BasedSpace.SuspensionCollapsed ((X.level 0).smash (Y.level 0)) p) :
      mid (p.1,(p.2,t)) = ((X.level 1).smash (Y.level 1)).point := by
    rcases hp with h | h | h
    · rw [h, mid_left]
    · rw [h, mid_zero]
    · rw [h, mid_one]
  have hrout (t : I) : ∀ a b,
      BasedSpace.SuspensionRelation ((X.level 0).smash (Y.level 0)) a b →
      mid (a.1,(a.2,t)) = mid (b.1,(b.2,t)) :=
    fun a b h => (collapse_outer a t h.1).trans (collapse_outer b t h.2).symm
  let b : C(((X.level 0).smash (Y.level 0)).suspension × I,
      (X.level 1).smash (Y.level 1)) :=
    ⟨fun p => Quot.lift (fun q => mid (q.1,(q.2,p.2))) (hrout p.2) p.1, by
      apply isQuotientMap_quot_mk.continuous_lift_prod_left
      exact hm.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))⟩
  refine ⟨b, ⟨fun _ _ _ _ => rfl, fun t => mid_left 0 t, ?_, ?_⟩, ?_⟩
  · intro a
    refine Quot.inductionOn a ?_
    rintro ⟨a,s⟩
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,s)) (Y.bond 0 (y,0)) = _
    rw [Y.bond_zero]
    exact BasedSpace.smashPoint_base_right _ _ _
  · intro a
    refine Quot.inductionOn a ?_
    rintro ⟨a,s⟩
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,s)) (Y.bond 0 (y,1)) = _
    rw [Y.bond_one]
    exact BasedSpace.smashPoint_base_right _ _ _
  · intro c hc
    apply ContinuousMap.ext
    rintro ⟨a,t⟩
    refine Quot.inductionOn a ?_
    rintro ⟨a,s⟩
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    exact hc.1 x y s t

noncomputable def pairedBond (X Y : Prespectrum.{0}) :
    C(((X.level 0).smash (Y.level 0)).suspension × I,
      (X.level 1).smash (Y.level 1)) := (pairedBond_exists X Y).exists.choose

def diagonalLevel (X Y : Prespectrum.{0}) : ℕ → BasedSpace.{0}
  | 0 => (X.level 0).smash (Y.level 0)
  | 1 => ((X.level 0).smash (Y.level 0)).suspension
  | n+2 => diagonalLevel X.tail Y.tail n

noncomputable def diagonalBond (X Y : Prespectrum.{0}) :
    ∀ n, C(diagonalLevel X Y n × I, diagonalLevel X Y (n+1))
  | 0 => BasedSpace.suspensionProjection _
  | 1 => pairedBond X Y
  | n+2 => diagonalBond X.tail Y.tail n

theorem diagonalBond_laws (X Y : Prespectrum.{0}) (n : ℕ) :
    (∀ t, diagonalBond X Y n ((diagonalLevel X Y n).point,t) =
      (diagonalLevel X Y (n+1)).point) ∧
    (∀ a, diagonalBond X Y n (a,0) = (diagonalLevel X Y (n+1)).point) ∧
    (∀ a, diagonalBond X Y n (a,1) = (diagonalLevel X Y (n+1)).point) := by
  induction n using Nat.twoStepInduction generalizing X Y with
  | zero =>
    exact ⟨fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl),
      fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl)),
      fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))⟩
  | one => exact (pairedBond_exists X Y).exists.choose_spec.2
  | more n ih _ => exact ih X.tail Y.tail

noncomputable def diagonalSmash (X Y : Prespectrum.{0}) : Prespectrum.{0} where
  level := diagonalLevel X Y
  bond := diagonalBond X Y
  bond_point n := (diagonalBond_laws X Y n).1
  bond_zero n := (diagonalBond_laws X Y n).2.1
  bond_one n := (diagonalBond_laws X Y n).2.2

noncomputable def diagonalMapLevel {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    ∀ n, diagonalLevel X Y n ⟶ diagonalLevel X' Y' n
  | 0 => BasedSpace.smashMap ⟨f.level 0, f.point 0⟩ ⟨g.level 0, g.point 0⟩
  | 1 => BasedSpace.suspendMap
      (BasedSpace.smashMap ⟨f.level 0, f.point 0⟩ ⟨g.level 0, g.point 0⟩)
  | n+2 => diagonalMapLevel (tailMap f) (tailMap g) n

theorem diagonalMapLevel_bond {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) (a : diagonalLevel X Y n) (t : I) :
    (diagonalMapLevel f g (n+1)).map (diagonalBond X Y n (a,t)) =
      diagonalBond X' Y' n ((diagonalMapLevel f g n).map a,t) := by
  induction n using Nat.twoStepInduction generalizing X Y X' Y' with
  | zero => rfl
  | one =>
    refine Quot.inductionOn a ?_
    rintro ⟨b,s⟩
    refine Quot.inductionOn b ?_
    rintro ⟨x,y⟩
    have hsm {A B A' B' : BasedSpace.{0}} (p : A ⟶ A') (q : B ⟶ B') (x : A) (y : B) :
        (BasedSpace.smashMap p q).map (BasedSpace.smashPoint A B x y) =
          BasedSpace.smashPoint A' B' (p.map x) (q.map y) :=
      (BasedSpace.smashMap_exists p q).exists.choose_spec x y
    have hp (U V : Prespectrum.{0}) (x : U.level 0) (y : V.level 0) (s t : I) :
        pairedBond U V (BasedSpace.suspensionProjection _
          (BasedSpace.smashPoint _ _ x y,s),t) =
        BasedSpace.smashPoint _ _ (U.bond 0 (x,s)) (V.bond 0 (y,t)) :=
      (pairedBond_exists U V).exists.choose_spec.1 x y s t
    change (BasedSpace.smashMap ⟨f.level 1, f.point 1⟩ ⟨g.level 1, g.point 1⟩).map
        (pairedBond X Y (BasedSpace.suspensionProjection _
          (BasedSpace.smashPoint _ _ x y,s),t)) =
      pairedBond X' Y' (BasedSpace.suspensionProjection _
        ((BasedSpace.smashMap ⟨f.level 0, f.point 0⟩ ⟨g.level 0, g.point 0⟩).map
          (BasedSpace.smashPoint _ _ x y),s),t)
    rw [hp, hsm, hsm, hp]
    change BasedSpace.smashPoint _ _ (f.level 1 (X.bond 0 (x,s)))
        (g.level 1 (Y.bond 0 (y,t))) = _
    rw [f.bond, g.bond]
  | more n ih _ => exact ih (tailMap f) (tailMap g) a

noncomputable def diagonalSmashMap {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') : diagonalSmash X Y ⟶ diagonalSmash X' Y' where
  level n := (diagonalMapLevel f g n).map
  point n := (diagonalMapLevel f g n).point
  bond n := diagonalMapLevel_bond f g n

/-- The flatness statement used by the derived comparison. The proof of
MMSS, Proposition 11.7, uses exactly CW homotopy type of each fixed level.
Our stronger based-CW condition makes that hypothesis explicit; the chosen
point-set double bonds are Definition 11.6 of the same source. -/
theorem diagonalSmash_stable_right (X : Prespectrum.{0}) (hX : X.IsGood)
    {Y Y' : Prespectrum.{0}} (f : Y ⟶ Y') (hf : stableEquivalences f) :
    stableEquivalences (diagonalSmashMap (𝟙 X) f) := by sorry

private theorem stable_even_representative (P : Prespectrum.{0}) (d : ℤ)
    (x : StableHomotopy P d) :
    ∃ a : Representative P d, a.stage % 2 = 0 ∧ Quot.mk _ a = x := by
  refine Quot.inductionOn x ?_
  intro a
  by_cases h : a.stage % 2 = 0
  · exact ⟨a,h,rfl⟩
  · refine ⟨a.next,?_,(Quot.sound (StableRelation.stabilization a)).symm⟩
    change (a.stage+1)%2=0
    omega

private theorem stableHomotopy_equiv_of_even_loops (P Q : Prespectrum.{0})
    (L : ∀ n r, GenLoop (Fin r) (P.level n) (P.level n).point →
      GenLoop (Fin r) (Q.level n) (Q.level n).point)
    (M : ∀ n r, GenLoop (Fin r) (Q.level n) (Q.level n).point →
      GenLoop (Fin r) (P.level n) (P.level n).point)
    (hL : ∀ n r p q, GenLoop.Homotopic p q → GenLoop.Homotopic (L n r p) (L n r q))
    (hM : ∀ n r p q, GenLoop.Homotopic p q → GenLoop.Homotopic (M n r p) (M n r q))
    (hLstep : ∀ n r (_hn : n%2=0) p,
      L (n+2) (r+2) (stabilizeLoop P (n+1) (r+1) (stabilizeLoop P n r p)) =
        stabilizeLoop Q (n+1) (r+1) (stabilizeLoop Q n r (L n r p)))
    (hMstep : ∀ n r (_hn : n%2=0) p,
      M (n+2) (r+2) (stabilizeLoop Q (n+1) (r+1) (stabilizeLoop Q n r p)) =
        stabilizeLoop P (n+1) (r+1) (stabilizeLoop P n r (M n r p)))
    (hML : ∀ n r p, M n r (L n r p)=p)
    (hLM : ∀ n r p, L n r (M n r p)=p) (d : ℤ) :
    ∃ e : StableHomotopy P d ≃ StableHomotopy Q d,
      ∀ a : Representative P d, a.stage%2=0 →
        e (Quot.mk _ a) = Quot.mk _ ⟨a.stage,a.dimension,a.degree,L _ _ a.loop⟩ := by
  have stabilizeLoop_homotopic (P : Prespectrum.{0}) (n r : ℕ)
      (p q : GenLoop (Fin r) (P.level n) (P.level n).point) (h : GenLoop.Homotopic p q) :
      GenLoop.Homotopic (stabilizeLoop P n r p) (stabilizeLoop P n r q) := by
    obtain ⟨H⟩ := h
    refine ⟨{ toFun := fun t => P.bond n (H (t.1,fun i => t.2 i.succ),t.2 0)
              continuous_toFun := (P.bond n).continuous.comp
                ((H.continuous.comp (continuous_fst.prodMk
                  (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))).prodMk
                    ((continuous_apply 0).comp continuous_snd))
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro t
      change P.bond n (H (0,_),_) = _
      rw [H.apply_zero]
      rfl
    · intro t
      change P.bond n (H (1,_),_) = _
      rw [H.apply_one]
      rfl
    · intro s t ht
      obtain ⟨i,hi⟩ := ht
      induction i using Fin.cases with
      | zero =>
        rcases hi with h | h
        · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
          rw [h,P.bond_zero,P.bond_zero]
        · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
          rw [h,P.bond_one,P.bond_one]
      | succ j =>
        change P.bond n (H (s,_),_) = P.bond n (p _,_)
        rw [H.eq_fst s ⟨j,hi⟩]
        rfl
  let mapRep {R S : Prespectrum.{0}}
      (U : ∀ n r, GenLoop (Fin r) (R.level n) (R.level n).point →
        GenLoop (Fin r) (S.level n) (S.level n).point)
      (a : Representative R d) : Representative S d :=
    ⟨a.stage,a.dimension,a.degree,U _ _ a.loop⟩
  let φ {R S : Prespectrum.{0}}
      (U : ∀ n r, GenLoop (Fin r) (R.level n) (R.level n).point →
        GenLoop (Fin r) (S.level n) (S.level n).point)
      (a : Representative R d) : StableHomotopy S d :=
    if a.stage%2=0 then Quot.mk _ (mapRep U a) else Quot.mk _ (mapRep U a.next)
  have respects {R S : Prespectrum.{0}}
      (U : ∀ n r, GenLoop (Fin r) (R.level n) (R.level n).point →
        GenLoop (Fin r) (S.level n) (S.level n).point)
      (hU : ∀ n r p q, GenLoop.Homotopic p q → GenLoop.Homotopic (U n r p) (U n r q))
      (hUstep : ∀ n r (_hn : n%2=0) p,
        U (n+2) (r+2) (stabilizeLoop R (n+1) (r+1) (stabilizeLoop R n r p)) =
          stabilizeLoop S (n+1) (r+1) (stabilizeLoop S n r (U n r p))) :
      ∀ a b, StableRelation R d a b → φ U a = φ U b := by
    intro a b h
    cases h with
    | homotopy p hp =>
      by_cases he : a.stage%2=0
      · dsimp only [φ]
        rw [if_pos he,if_pos he]
        exact Quot.sound (StableRelation.homotopy (mapRep U a) _ (hU _ _ _ _ hp))
      · have hh := hU _ _ _ _ (stabilizeLoop_homotopic R _ _ _ _ hp)
        dsimp only [φ]
        rw [if_neg he,if_neg he]
        exact Quot.sound (StableRelation.homotopy (mapRep U a.next) _ hh)
    | stabilization =>
      by_cases he : a.stage%2=0
      · have ho : a.next.stage%2≠0 := by change (a.stage+1)%2≠0; omega
        dsimp only [φ]
        rw [if_pos he,if_neg ho]
        have hs : mapRep U a.next.next = (mapRep U a).next.next := by
          cases a with
          | mk n r hd p =>
            dsimp only [mapRep,Representative.next]
            congr 1
            exact hUstep n r he p
        rw [hs]
        exact (Quot.sound (StableRelation.stabilization (mapRep U a))).trans
          (Quot.sound (StableRelation.stabilization (mapRep U a).next))
      · have hz : a.next.stage%2=0 := by change (a.stage+1)%2=0; omega
        dsimp only [φ]
        rw [if_neg he,if_pos hz]
  let F : StableHomotopy P d → StableHomotopy Q d := Quot.lift (φ L) (respects L hL hLstep)
  let G : StableHomotopy Q d → StableHomotopy P d := Quot.lift (φ M) (respects M hM hMstep)
  have hinv {R S : Prespectrum.{0}}
      (U : ∀ n r, GenLoop (Fin r) (R.level n) (R.level n).point →
        GenLoop (Fin r) (S.level n) (S.level n).point)
      (V : ∀ n r, GenLoop (Fin r) (S.level n) (S.level n).point →
        GenLoop (Fin r) (R.level n) (R.level n).point)
      (hVU : ∀ n r p, V n r (U n r p)=p)
      (rU : ∀ a b, StableRelation R d a b → φ U a=φ U b)
      (rV : ∀ a b, StableRelation S d a b → φ V a=φ V b)
      (x : StableHomotopy R d) :
      Quot.lift (φ V) rV (Quot.lift (φ U) rU x)=x := by
    obtain ⟨a,ha,rfl⟩ := stable_even_representative R d x
    change Quot.lift (φ V) rV (φ U a)=Quot.mk _ a
    dsimp only [φ]
    rw [if_pos ha]
    change φ V (mapRep U a)=Quot.mk _ a
    dsimp only [φ]
    rw [if_pos ha]
    congr 1
    cases a with
    | mk n r hd p =>
      dsimp only [mapRep]
      rw [hVU]
  refine ⟨⟨F,G,hinv L M hML _ _,hinv M L hLM _ _⟩,?_⟩
  intro a ha
  change φ L a = _
  exact if_pos ha

private theorem diagonalSmash_stable_swap :
    ∃ e : ∀ (X Y : Prespectrum.{0}) (d : ℤ),
      StableHomotopy (diagonalSmash X Y) d ≃ StableHomotopy (diagonalSmash Y X) d,
      ∀ {X Y X' Y' : Prespectrum.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (d : ℤ) a,
        e X' Y' d (stableHomotopyMap (diagonalSmashMap f g) d a) =
          stableHomotopyMap (diagonalSmashMap g f) d (e X Y d a) := by
  let blocks (n : ℕ) : (Fin 2 ⊕ Fin n) ≃ Fin (n+2) :=
    finSumFinEquiv.trans (finCongr (Nat.add_comm 2 n))
  let pairSwap : (n : ℕ) → Fin n ≃ Fin n :=
    Nat.twoStepInduction (Equiv.refl _) (Equiv.refl _) (fun n ih _ =>
      (blocks n).symm.trans
        ((Equiv.sumCongr (Equiv.swap (0 : Fin 2) 1) ih).trans (blocks n)))
  have blocks_zero (n : ℕ) : blocks n (.inl 0) = 0 := by
    apply Fin.ext
    rfl
  have blocks_one (n : ℕ) : blocks n (.inl 1) = 1 := by
    apply Fin.ext
    rfl
  have blocks_right (n : ℕ) (i : Fin n) : blocks n (.inr i) = i.succ.succ := by
    apply Fin.ext
    simp only [blocks,Equiv.trans_apply,finSumFinEquiv_apply_right,finCongr_apply,Fin.val_cast,Fin.val_natAdd,Fin.val_succ]
    omega
  have sigma_zero (n : ℕ) : pairSwap (n+2) 0 = 1 := by
    rw [← blocks_zero n]
    simp only [pairSwap,Nat.twoStepInduction,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply]
    simp [blocks_one]
  have sigma_one (n : ℕ) : pairSwap (n+2) 1 = 0 := by
    rw [← blocks_one n]
    simp only [pairSwap,Nat.twoStepInduction,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply]
    simp [blocks_zero]
  have sigma_succ_succ (n : ℕ) (i : Fin n) :
      pairSwap (n+2) i.succ.succ = (pairSwap n i).succ.succ := by
    rw [← blocks_right n i]
    simp only [pairSwap,Nat.twoStepInduction,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply]
    exact blocks_right n _
  have sigma_involutive (n : ℕ) : Function.Involutive (pairSwap n) := by
    induction n using Nat.twoStepInduction with
    | zero => intro i; exact Fin.elim0 i
    | one => intro i; rfl
    | more n hn _ =>
      intro i
      obtain ⟨j,rfl⟩ := (blocks n).surjective i
      cases j with
      | inl j =>
        fin_cases j <;> simp [blocks_zero,blocks_one,sigma_zero,sigma_one]
      | inr j =>
        rw [blocks_right,sigma_succ_succ,sigma_succ_succ,hn]
  let S (X Y : Prespectrum.{0}) (n : ℕ) : diagonalLevel X Y n ⟶ diagonalLevel Y X n :=
    Nat.twoStepInduction (motive := fun n => ∀ X Y : Prespectrum.{0},
      diagonalLevel X Y n ⟶ diagonalLevel Y X n)
      (fun X Y => BasedSpace.smashSwap (X.level 0) (Y.level 0))
      (fun X Y => BasedSpace.suspendMap (BasedSpace.smashSwap (X.level 0) (Y.level 0)))
      (fun _ ih _ X Y => ih X.tail Y.tail) n X Y
  have hs (A B : BasedSpace.{0}) (a : A) (b : B) :
      (BasedSpace.smashSwap A B).map (BasedSpace.smashPoint A B a b) =
        BasedSpace.smashPoint B A b a :=
    (BasedSpace.smashCoherence_exists.2 A B).exists.choose_spec a b
  have hinv (X Y : Prespectrum.{0}) (n : ℕ) (a : diagonalLevel X Y n) :
      (S Y X n).map ((S X Y n).map a)=a := by
    induction n using Nat.twoStepInduction generalizing X Y with
    | zero =>
      refine Quot.inductionOn a ?_
      rintro ⟨x,y⟩
      change (BasedSpace.smashSwap _ _).map ((BasedSpace.smashSwap _ _).map
        (BasedSpace.smashPoint _ _ x y)) = _
      rw [hs,hs]
      rfl
    | one =>
      refine Quot.inductionOn a ?_
      rintro ⟨p,t⟩
      refine Quot.inductionOn p ?_
      rintro ⟨x,y⟩
      change BasedSpace.suspensionProjection _
        ((BasedSpace.smashSwap _ _).map ((BasedSpace.smashSwap _ _).map
          (BasedSpace.smashPoint _ _ x y)),t) = _
      rw [hs,hs]
      rfl
    | more n hn _ => exact hn X.tail Y.tail a
  have hnat {X Y X' Y' : Prespectrum.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
      (n : ℕ) (a : diagonalLevel X Y n) :
      (S X' Y' n).map ((diagonalMapLevel f g n).map a) =
        (diagonalMapLevel g f n).map ((S X Y n).map a) := by
    have hm {A B A' B' : BasedSpace.{0}} (f : A ⟶ A') (g : B ⟶ B') (a : A) (b : B) :
        (BasedSpace.smashMap f g).map (BasedSpace.smashPoint _ _ a b) =
          BasedSpace.smashPoint _ _ (f.map a) (g.map b) :=
      (BasedSpace.smashMap_exists f g).exists.choose_spec a b
    induction n using Nat.twoStepInduction generalizing X Y X' Y' with
    | zero =>
      refine Quot.inductionOn a ?_
      rintro ⟨x,y⟩
      change (BasedSpace.smashSwap _ _).map ((BasedSpace.smashMap _ _).map
        (BasedSpace.smashPoint _ _ x y)) =
        (BasedSpace.smashMap _ _).map ((BasedSpace.smashSwap _ _).map
          (BasedSpace.smashPoint _ _ x y))
      rw [hm,hs,hs,hm]
    | one =>
      refine Quot.inductionOn a ?_
      rintro ⟨p,t⟩
      refine Quot.inductionOn p ?_
      rintro ⟨x,y⟩
      change BasedSpace.suspensionProjection _
        ((BasedSpace.smashSwap _ _).map ((BasedSpace.smashMap _ _).map
          (BasedSpace.smashPoint _ _ x y)),t) =
        BasedSpace.suspensionProjection _
          ((BasedSpace.smashMap _ _).map ((BasedSpace.smashSwap _ _).map
            (BasedSpace.smashPoint _ _ x y)),t)
      rw [hm,hs,hs,hm]
    | more n hn _ => exact hn (tailMap f) (tailMap g) a
  have hdouble (X Y : Prespectrum.{0}) (n : ℕ) (hn : n%2=0)
      (a : diagonalLevel X Y n) (s t : I) :
      (S X Y (n+2)).map (diagonalBond X Y (n+1) (diagonalBond X Y n (a,s),t)) =
        diagonalBond Y X (n+1) (diagonalBond Y X n ((S X Y n).map a,t),s) := by
    induction n using Nat.twoStepInduction generalizing X Y with
    | zero =>
      refine Quot.inductionOn a ?_
      rintro ⟨x,y⟩
      have hp (U V : Prespectrum.{0}) (x : U.level 0) (y : V.level 0) (s t : I) :
          pairedBond U V (BasedSpace.suspensionProjection _
            (BasedSpace.smashPoint _ _ x y,s),t) =
            BasedSpace.smashPoint _ _ (U.bond 0 (x,s)) (V.bond 0 (y,t)) :=
        (pairedBond_exists U V).exists.choose_spec.1 x y s t
      change (BasedSpace.smashSwap _ _).map
        (pairedBond X Y (BasedSpace.suspensionProjection _ (BasedSpace.smashPoint _ _ x y,s),t)) =
        pairedBond Y X (BasedSpace.suspensionProjection _
          ((BasedSpace.smashSwap _ _).map (BasedSpace.smashPoint _ _ x y),t),s)
      rw [hp,hs,hs,hp]
    | one => omega
    | more n ih _ => exact ih X.tail Y.tail (by omega) a
  let L (X Y : Prespectrum.{0}) (n r : ℕ)
      (p : GenLoop (Fin r) ((diagonalSmash X Y).level n) ((diagonalSmash X Y).level n).point) :
      GenLoop (Fin r) ((diagonalSmash Y X).level n) ((diagonalSmash Y X).level n).point :=
    ⟨(S X Y n).map.comp ((GenLoop.congr _ (pairSwap r)) p).val,by
      intro t ht
      exact (congrArg (S X Y n).map (((GenLoop.congr _ (pairSwap r)) p).property t ht)).trans
        (S X Y n).point⟩
  have hL (X Y : Prespectrum.{0}) (n r : ℕ) (p q) (h : GenLoop.Homotopic p q) :
      GenLoop.Homotopic (L X Y n r p) (L X Y n r q) := by
    obtain ⟨H⟩ := h
    have hp : GenLoop.Homotopic ((GenLoop.congr _ (pairSwap r)) p) ((GenLoop.congr _ (pairSwap r)) q) := by
      refine ⟨{ toFun := fun t => H (t.1,fun i => t.2 (pairSwap r i))
                continuous_toFun := H.continuous.comp
                  (continuous_fst.prodMk (continuous_pi fun i =>
                    (continuous_apply (pairSwap r i)).comp continuous_snd))
                map_zero_left := ?_
                map_one_left := ?_
                prop' := ?_ }⟩
      · intro t
        exact H.apply_zero _
      · intro t
        exact H.apply_one _
      · intro s t ht
        obtain ⟨i,hi⟩ := ht
        exact H.eq_fst s ⟨(pairSwap r).symm i,by simpa using hi⟩
    exact hp.comp_continuousMap (S X Y n).map
  have hLstep (X Y : Prespectrum.{0}) (n r : ℕ) (hn : n%2=0) (p) :
      L X Y (n+2) (r+2)
        (stabilizeLoop (diagonalSmash X Y) (n+1) (r+1)
          (stabilizeLoop (diagonalSmash X Y) n r p)) =
        stabilizeLoop (diagonalSmash Y X) (n+1) (r+1)
          (stabilizeLoop (diagonalSmash Y X) n r (L X Y n r p)) := by
    apply GenLoop.ext
    intro t
    change (S X Y (n+2)).map (diagonalBond X Y (n+1)
      (diagonalBond X Y n (p (fun i => t (pairSwap (r+2) i.succ.succ)),t (pairSwap (r+2) 1)),t (pairSwap (r+2) 0))) =
        diagonalBond Y X (n+1) (diagonalBond Y X n
          ((S X Y n).map (p (fun i => t (pairSwap r i).succ.succ)),t 1),t 0)
    simp only [sigma_zero,sigma_one,sigma_succ_succ]
    exact hdouble X Y n hn _ _ _
  have hLL (X Y : Prespectrum.{0}) (n r : ℕ) (p) : L Y X n r (L X Y n r p)=p := by
    apply GenLoop.ext
    intro t
    change (S Y X n).map ((S X Y n).map (p (fun i => t (pairSwap r (pairSwap r i)))))=p t
    have hpi : (fun i => t (pairSwap r (pairSwap r i)))=t :=
      funext (fun i => congrArg t (sigma_involutive r i))
    rw [hpi,hinv]
  obtain ⟨e,he⟩ : ∃ e : ∀ (X Y : Prespectrum.{0}) (d : ℤ),
      StableHomotopy (diagonalSmash X Y) d ≃ StableHomotopy (diagonalSmash Y X) d,
      ∀ X Y d (a : Representative (diagonalSmash X Y) d), a.stage%2=0 →
        e X Y d (Quot.mk _ a)=Quot.mk _ ⟨a.stage,a.dimension,a.degree,L X Y _ _ a.loop⟩ := by
    choose e he using fun X Y d => stableHomotopy_equiv_of_even_loops
      (diagonalSmash X Y) (diagonalSmash Y X) (L X Y) (L Y X)
        (hL X Y) (hL Y X) (hLstep X Y) (hLstep Y X) (hLL X Y) (hLL Y X) d
    exact ⟨e,he⟩
  refine ⟨e,?_⟩
  intro X Y X' Y' f g d a
  obtain ⟨a,ha,rfl⟩ := stable_even_representative (diagonalSmash X Y) d a
  change e X' Y' d (Quot.mk _ (a.map (diagonalSmashMap f g))) = _
  rw [he X' Y' d _ ha,he X Y d a ha]
  change Quot.mk _ _ = Quot.mk _ _
  congr 1
  cases a with
  | mk n r hd p =>
    dsimp only [Representative.map]
    congr 1
    apply GenLoop.ext
    intro t
    exact hnat f g n (p (fun i => t (pairSwap r i)))
theorem diagonalSmash_stable_left (Y : Prespectrum.{0}) (hY : Y.IsGood)
    {X X' : Prespectrum.{0}} (f : X ⟶ X') (hf : stableEquivalences f) :
    stableEquivalences (diagonalSmashMap f (𝟙 Y)) := by
  obtain ⟨e,he⟩ := diagonalSmash_stable_swap
  have h := diagonalSmash_stable_right Y hY f hf
  intro d
  constructor
  · intro a b hab
    apply (e X Y d).injective
    apply (h d).injective
    rw [← he f (𝟙 Y) d a,← he f (𝟙 Y) d b,hab]
  · intro b
    obtain ⟨a,ha⟩ := (h d).surjective (e X' Y d b)
    refine ⟨(e X Y d).symm a,?_⟩
    apply (e X' Y d).injective
    rw [he,Equiv.apply_symm_apply,ha]

/-- The zeroth-stage inclusion is the free/evaluation counit. -/
noncomputable def zeroStage (X : Prespectrum.{0}) : suspensionSpectrum (X.level 0) ⟶ X :=
  freeCounit X 0

end Prespectrum
end KIP126.StableHomotopy.Implementation
