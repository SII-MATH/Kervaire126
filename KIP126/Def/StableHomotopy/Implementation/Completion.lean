module

public import KIP126.Def.StableHomotopy.Implementation.Generators
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! A concrete HF₂-local source. Ordinary sequential spectra and stable
weak equivalences are already fixed. An Eilenberg–Mac Lane spectrum is
specified by its actual stable homotopy groups, including loop addition.
Equivalences detected by all its integer cohomology groups define the
HF₂ localization. The auxiliary S[1/2] construction separately defines the
Moore(2)-completeness predicate; no comparison between the two notions of
completion is established here. -/
namespace KIP126.StableHomotopy.Implementation
open CategoryTheory Topology
open scoped unitInterval

namespace BasedSpace

/-- Traverse the suspension coordinate twice. It is deliberately a raw
function: the jump from 1 to 0 is continuous only after reduced suspension. -/
noncomputable def doubleInterval (t : I) : I :=
  if h : (t : ℝ) ≤ 1/2 then
    ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.property.1, t.property.2]⟩
  else
    ⟨2 * (t : ℝ) - 1, by constructor <;> nlinarith [t.property.1, t.property.2]⟩

/-- This is the degree-two pinch/fold map, fixed on quotient representatives.
Its source is a reduced suspension, so the two traversals add in homotopy. -/
theorem doubleSuspension_exists (A : BasedSpace.{0}) :
    ∃! f : A.suspension ⟶ A.suspension, ∀ a t,
      f.map (suspensionProjection A (a,t)) =
        suspensionProjection A (a,doubleInterval t) := by
  classical
  have hzero : doubleInterval 0 = 0 := by
    apply Subtype.ext
    norm_num [doubleInterval]
  have hone : doubleInterval 1 = 1 := by
    apply Subtype.ext
    norm_num [doubleInterval]
  let l (t : I) : I := Set.projIcc 0 1 zero_le_one (2 * (t:ℝ))
  let r (t : I) : I := Set.projIcc 0 1 zero_le_one (2 * (t:ℝ)-1)
  have hl : Continuous l := continuous_projIcc.comp (continuous_const.mul continuous_subtype_val)
  have hr : Continuous r := continuous_projIcc.comp
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)
  have hglue : ∀ p : A × I, (p.2:ℝ) = 1/2 →
      suspensionProjection A (p.1,l p.2) = suspensionProjection A (p.1,r p.2) := by
    intro p hp
    have hpl : l p.2 = 1 := by
      dsimp [l]
      norm_num [hp]
    have hpr : r p.2 = 0 := by
      dsimp [r]
      norm_num [hp]
    rw [hpl,hpr]
    exact (suspensionProjection_collapsed A _ (Or.inr (Or.inr rfl))).trans
      (suspensionProjection_collapsed A _ (Or.inr (Or.inl rfl))).symm
  have hc : Continuous (fun p : A × I => suspensionProjection A (p.1,doubleInterval p.2)) := by
    have heq : (fun p : A × I => suspensionProjection A (p.1,doubleInterval p.2)) =
        (fun p : A × I => if (p.2:ℝ) ≤ 1/2 then
          suspensionProjection A (p.1,l p.2) else suspensionProjection A (p.1,r p.2)) := by
      funext p
      dsimp only [doubleInterval]
      split_ifs with h
      · have hm : 2*(p.2:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
          constructor <;> nlinarith [p.2.property.1,p.2.property.2]
        rw [show l p.2 = ⟨2*(p.2:ℝ),hm⟩ from Set.projIcc_of_mem _ hm]
      · have hm : 2*(p.2:ℝ)-1 ∈ Set.Icc (0:ℝ) 1 := by
          constructor <;> nlinarith [p.2.property.1,p.2.property.2]
        rw [show r p.2 = ⟨2*(p.2:ℝ)-1,hm⟩ from Set.projIcc_of_mem _ hm]
    rw [heq]
    exact continuous_if_le (continuous_subtype_val.comp continuous_snd) continuous_const
      ((suspensionProjection A).continuous.comp
        (continuous_fst.prodMk (hl.comp continuous_snd))).continuousOn
      ((suspensionProjection A).continuous.comp
        (continuous_fst.prodMk (hr.comp continuous_snd))).continuousOn hglue
  let raw : C(A × I,A.suspension) := ⟨_,hc⟩
  have collapsed (p : A × I) (hp : SuspensionCollapsed A p) : raw p = A.suspension.point := by
    apply suspensionProjection_collapsed
    rcases hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by rw [h,hzero]))
    · exact Or.inr (Or.inr (by rw [h,hone]))
  have respects : ∀ p q, SuspensionRelation A p q → raw p = raw q :=
    fun p q hpq => (collapsed p hpq.1).trans (collapsed q hpq.2).symm
  let f : A.suspension ⟶ A.suspension :=
    { map := ⟨Quot.lift raw respects,continuous_quot_lift respects raw.continuous⟩
      point := collapsed (A.point,0) (Or.inl rfl) }
  refine ⟨f,?_,?_⟩
  · intro a t
    rfl
  · intro g hg
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    intro p
    exact hg p.1 p.2

noncomputable def doubleSuspension (A : BasedSpace.{0}) :
    A.suspension ⟶ A.suspension := (doubleSuspension_exists A).exists.choose

end BasedSpace
namespace Prespectrum

/-- The prespectrum with sphere levels and doubled bonding maps. Its stable
homotopy groups are the sequential colimit under multiplication by 2; it is
therefore the ordinary sphere with 2 inverted, not the mod-2 Moore spectrum. -/
noncomputable def sphereInvertTwo : Prespectrum.{0} where
  level := sphereLevel
  bond n := (BasedSpace.doubleSuspension (sphereLevel n)).map.comp (sphere.bond n)
  bond_point n t := by
    change (BasedSpace.doubleSuspension _).map (sphere.bond n (_,t)) = _
    exact (congrArg (BasedSpace.doubleSuspension (sphereLevel n)).map
      (sphere.bond_point n t)).trans (BasedSpace.doubleSuspension _).point
  bond_zero n x := by
    change (BasedSpace.doubleSuspension _).map (sphere.bond n (x,0)) = _
    rw [sphere.bond_zero]
    exact (BasedSpace.doubleSuspension _).point
  bond_one n x := by
    change (BasedSpace.doubleSuspension _).map (sphere.bond n (x,1)) = _
    rw [sphere.bond_one]
    exact (BasedSpace.doubleSuspension _).point

/-- Orthogonality to every shift of S[1/2], expressed in the already defined
ordinary stable localization. Both nonnegative and nonpositive shifts occur. -/
def IsTwoComplete (X : Prespectrum.{0}) : Prop :=
  ∀ n : ℕ,
    Subsingleton (sourceLocalization.obj ((suspension^[n]) sphereInvertTwo) ⟶
      sourceLocalization.obj X) ∧
    Subsingleton (sourceLocalization.obj ((desuspension^[n]) sphereInvertTwo) ⟶
      sourceLocalization.obj X)

end Prespectrum

/-- Exact Eilenberg–Mac Lane characterization in the ordinary source.
The equivalence respects the actual cubical concatenation and zero, so it
is not an arbitrary two-element set identified with F₂. -/
structure SourceHF2Model where
  spectrum : Prespectrum.{0}
  good : ∀ n, (spectrum.level n).IsGood
  pi0 : Prespectrum.StableHomotopy spectrum 0 ≃ ZMod 2
  pi0_zero : pi0 (Prespectrum.loopClass spectrum 0 0 0 (by simp) GenLoop.const) = 0
  pi0_add : ∀ (n : ℕ)
      (p q : GenLoop (Fin (n+1)) (spectrum.level (n+1)) (spectrum.level (n+1)).point),
    pi0 (Prespectrum.loopClass spectrum 0 (n+1) (n+1) (by omega)
        (GenLoop.transAt 0 p q)) =
      pi0 (Prespectrum.loopClass spectrum 0 (n+1) (n+1) (by omega) p) +
      pi0 (Prespectrum.loopClass spectrum 0 (n+1) (n+1) (by omega) q)
  vanishes : ∀ d : ℤ, d ≠ 0 → Subsingleton (Prespectrum.StableHomotopy spectrum d)

set_option maxHeartbeats 2000000 in
theorem sourceHF2Model_exists : Nonempty SourceHF2Model := by
  classical
  -- C1–C4: the reduced fat realization and its compatible level coordinates.
  -- This local construction is the remaining A/T/B/C obligation.
  have layer_data :
      ∃ E : Prespectrum.{0}, (∀ n, (E.level n).IsGood) ∧
        ∃ e : ∀ n, HomotopyGroup (Fin n) (E.level n) (E.level n).point ≃ ZMod 2,
          (∀ n, e n ⟦GenLoop.const⟧ = 0) ∧
          (∀ n (p : GenLoop (Fin n) (E.level n) (E.level n).point),
            e (n + 1) ⟦Prespectrum.stabilizeLoop E n n p⟧ = e n ⟦p⟧) ∧
          (∀ n (p q : GenLoop (Fin (n + 1)) (E.level (n + 1))
              (E.level (n + 1)).point),
            e (n + 1) ⟦GenLoop.transAt 0 p q⟧ =
              e (n + 1) ⟦p⟧ + e (n + 1) ⟦q⟧) ∧
          (∀ n r, r ≠ n →
            Subsingleton (HomotopyGroup (Fin r) (E.level n) (E.level n).point)) := by
    -- A2: normalized cocycles on monotone tuples; repeated vertices have value zero.
    let face (n : ℕ) (i : Fin (n + 2)) : Fin (n + 1) →o Fin (n + 2) :=
      (Fin.succAboveOrderEmb i).toOrderHom
    have normalized_delta_degenerate {n q : ℕ}
        (z : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2)
        (hz : ∀ b : Fin (n + 1) →o Fin (q + 1), ¬ Function.Injective b → z b = 0)
        (a : Fin (n + 2) →o Fin (q + 1)) (ha : ¬ Function.Injective a) :
        ∑ i, z (a.comp (face n i)) = 0 := by
      obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), a j.castSucc = a j.succ := by
        by_contra h
        exact ha ((Fin.orderHom_injective_iff a).2 (fun j hj => h ⟨j, hj⟩))
      have hface : a.comp (face n j.castSucc) = a.comp (face n j.succ) := by
        apply OrderHom.ext
        funext k
        change a (j.castSucc.succAbove k) = a (j.succ.succAbove k)
        rcases lt_trichotomy k j with hk | rfl | hk
        · rw [Fin.succAbove_castSucc_of_lt j k hk,
            Fin.succAbove_succ_of_le j k hk.le]
        · simpa only [Fin.succAbove_castSucc_self, Fin.succAbove_succ_self] using hj.symm
        · rw [Fin.succAbove_castSucc_of_le j k hk.le,
            Fin.succAbove_succ_of_lt j k hk]
      have hrest : ∀ i ∈ (Finset.univ : Finset (Fin (n + 2))),
          i ≠ j.castSucc ∧ i ≠ j.succ → z (a.comp (face n i)) = 0 := by
        intro i _ hi
        apply hz
        intro hinj
        obtain ⟨x, hx⟩ := Fin.exists_succAbove_eq (x := j.castSucc) (y := i) hi.1.symm
        obtain ⟨y, hy⟩ := Fin.exists_succAbove_eq (x := j.succ) (y := i) hi.2.symm
        have hxy : x = y := hinj (by
          change a (i.succAbove x) = a (i.succAbove y)
          rw [hx, hy]
          exact hj)
        apply j.castSucc_lt_succ.ne
        exact hx.symm.trans ((congrArg i.succAbove hxy).trans hy)
      calc
        (∑ i, z (a.comp (face n i))) =
            z (a.comp (face n j.castSucc)) + z (a.comp (face n j.succ)) :=
          Finset.sum_eq_add_of_mem j.castSucc j.succ (Finset.mem_univ _) (Finset.mem_univ _)
            j.castSucc_lt_succ.ne hrest
        _ = 0 := by rw [hface]; exact CharTwo.add_self_eq_zero _
    have normalized_closed_iff_strict {n q : ℕ}
        (z : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2)
        (hz : ∀ b : Fin (n + 1) →o Fin (q + 1), ¬ Function.Injective b → z b = 0) :
        (∀ a : Fin (n + 2) →o Fin (q + 1), ∑ i, z (a.comp (face n i)) = 0) ↔
        (∀ a : Fin (n + 2) →o Fin (q + 1), StrictMono a →
          ∑ i, z (a.comp (face n i)) = 0) := by
      constructor
      · intro h a _; exact h a
      · intro h a
        by_cases ha : Function.Injective a
        · exact h a ((a.monotone.strictMono_iff_injective).2 ha)
        · exact normalized_delta_degenerate z hz a ha
    let delta (n q : ℕ) (z : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2)
        (s : Fin (n + 2) →o Fin (q + 1)) := ∑ i, z (s.comp (face n i))
    have delta_sq (n q : ℕ) (z : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2) :
        delta (n + 1) q (delta n q z) = 0 := by
      funext s
      let f : Fin (n + 3) × Fin (n + 2) → ZMod 2 :=
        fun a => z ((s.comp (face (n + 1) a.1)).comp (face n a.2))
      let pairSwap : Fin (n + 3) × Fin (n + 2) → Fin (n + 3) × Fin (n + 2) :=
        fun a => (a.1.succAbove a.2, a.2.predAbove a.1)
      change (∑ i, ∑ j, f (i, j)) = 0
      rw [← Fintype.sum_prod_type f]
      refine Finset.sum_ninvolution (s := Finset.univ) (f := f) pairSwap ?_ ?_ ?_ ?_
      · intro a
        have h : f (pairSwap a) = f a := by
          apply congrArg z
          apply OrderHom.ext
          funext j
          change s ((a.1.succAbove a.2).succAbove ((a.2.predAbove a.1).succAbove j)) =
            s (a.1.succAbove (a.2.succAbove j))
          exact congrArg s (Fin.succAbove_succAbove_succAbove_predAbove a.1 a.2 j)
        rw [h]
        exact CharTwo.add_self_eq_zero _
      · intro a _ h
        exact Fin.succAbove_ne a.1 a.2 (congrArg Prod.fst h)
      · intro a; exact Finset.mem_univ _
      · intro a
        apply Prod.ext
        · exact Fin.succAbove_succAbove_predAbove _ _
        · exact Fin.predAbove_predAbove_succAbove _ _
    let K (n q : ℕ) :=
      {z : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2 //
        (∀ a : Fin (n + 1) →o Fin (q + 1), ¬ Function.Injective a → z a = 0) ∧
        ∀ a : Fin (n + 2) →o Fin (q + 1), ∑ i, z (a.comp (face n i)) = 0}
    have labels_finite (n q : ℕ) : Finite (K n q) := by
      letI : Finite (Fin (n + 1) →o Fin (q + 1)) :=
        Finite.of_injective (fun a : Fin (n + 1) →o Fin (q + 1) => (a : Fin (n + 1) → Fin (q + 1)))
          DFunLike.coe_injective
      dsimp only [K]
      infer_instance
    let zero (n q : ℕ) : K n q := ⟨fun _ => 0, by
      constructor
      · intros; rfl
      · intro a; simp⟩
    let pull {n p q : ℕ} (a : Fin (p + 1) →o Fin (q + 1)) (z : K n q) : K n p :=
      ⟨fun b => z.1 (a.comp b), by
        constructor
        · intro b hb
          apply z.2.1
          intro h
          apply hb
          intro i j hij
          apply h
          change a (b i) = a (b j)
          rw [hij]
        · intro b
          exact z.2.2 (a.comp b)⟩
    have pull_id (n q : ℕ) (z : K n q) : pull OrderHom.id z = z := by
      apply Subtype.ext
      funext a
      rfl
    have pull_comp {n p q r : ℕ}
        (a : Fin (p + 1) →o Fin (q + 1)) (b : Fin (q + 1) →o Fin (r + 1))
        (z : K n r) : pull a (pull b z) = pull (b.comp a) z := by
      apply Subtype.ext
      funext c
      rfl
    have pull_zero {n p q : ℕ} (a : Fin (p + 1) →o Fin (q + 1)) :
        pull a (zero n q) = zero n p := by
      apply Subtype.ext
      rfl
    have k_subsingleton (n q : ℕ) (hqn : q < n) : Subsingleton (K n q) := by
      constructor
      intro z w
      apply Subtype.ext
      funext s
      have hs : ¬ Function.Injective s := by
        intro hinj
        have hcard := Fintype.card_le_of_injective s hinj
        simp only [Fintype.card_fin] at hcard
        omega
      exact (z.2.1 s hs).trans (w.2.1 s hs).symm
    let constant (q : ℕ) (a : ZMod 2) : K 0 q :=
      ⟨fun _ => a, by
        constructor
        · intro s hs
          exact False.elim (hs (fun i j _ => Fin.ext (by omega)))
        · intro s
          change (∑ _ : Fin 2, a) = 0
          simp only [Fin.sum_univ_two, CharTwo.add_self_eq_zero]⟩
    -- A9: the Alexander–Whitney formula z ∪ δt on ordered vertices.
    let cup (n q : ℕ) (z : K n q) (t : Fin (q + 1) → ZMod 2)
        (s : Fin (n + 2) →o Fin (q + 1)) : ZMod 2 :=
      z.1 (s.comp Fin.castSuccOrderEmb.toOrderHom) *
        (t (s (Fin.last (n + 1))) + t (s (Fin.last n).castSucc))
    have cup_normalized (n q : ℕ) (z : K n q) (t : Fin (q + 1) → ZMod 2)
        (s : Fin (n + 2) →o Fin (q + 1)) (hs : ¬ Function.Injective s) :
        cup n q z t s = 0 := by
      by_cases hp : Function.Injective (s.comp Fin.castSuccOrderEmb.toOrderHom)
      · obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), s i.castSucc = s i.succ := by
          by_contra h
          exact hs ((Fin.orderHom_injective_iff s).2 (fun i hi => h ⟨i, hi⟩))
        have hilast : i = Fin.last n := by
          by_contra hlast
          obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
          have hj : j.castSucc = j.succ := hp (by
            change s j.castSucc.castSucc = s j.succ.castSucc
            simpa only [Fin.succ_castSucc] using hi)
          exact j.castSucc_lt_succ.ne hj
        subst i
        have hh : t (s (Fin.last (n + 1))) = t (s (Fin.last n).castSucc) := by
          simpa only [Fin.succ_last] using (congrArg t hi).symm
        dsimp only [cup]
        rw [hh, CharTwo.add_self_eq_zero, mul_zero]
      · dsimp only [cup]
        rw [z.2.1 _ hp, zero_mul]
    have cup_closed (n q : ℕ) (z : K n q) (t : Fin (q + 1) → ZMod 2)
        (s : Fin (n + 3) →o Fin (q + 1)) :
        ∑ i, cup n q z t (s.comp (face (n + 1) i)) = 0 := by
      let a : Fin (n + 2) →o Fin (q + 1) := s.comp Fin.castSuccOrderEmb.toOrderHom
      let v : Fin (n + 1) →o Fin (q + 1) := a.comp Fin.castSuccOrderEmb.toOrderHom
      let x := t (s (Fin.last (n + 2)))
      let y := t (s (Fin.last (n + 1)).castSucc)
      let w := t (s (Fin.last n).castSucc.castSucc)
      have hsmall (i : Fin (n + 1)) :
          cup n q z t (s.comp (face (n + 1) i.castSucc.castSucc)) =
            z.1 (a.comp (face n i.castSucc)) * (x + y) := by
        have hp : (s.comp (face (n + 1) i.castSucc.castSucc)).comp
            Fin.castSuccOrderEmb.toOrderHom = a.comp (face n i.castSucc) := by
          apply OrderHom.ext
          funext j
          exact congrArg s Fin.castSucc_succAbove_castSucc
        dsimp only [cup]
        rw [hp]
        congr 2
        · change t (s (i.castSucc.castSucc.succAbove (Fin.last (n + 1)))) = x
          simp [x]
        · change t (s (i.castSucc.castSucc.succAbove (Fin.last n).castSucc)) = y
          simp [y]
      have hmid : cup n q z t
          (s.comp (face (n + 1) (Fin.last (n + 1)).castSucc)) =
          z.1 v * (x + w) := by
        have hp : (s.comp (face (n + 1) (Fin.last (n + 1)).castSucc)).comp
            Fin.castSuccOrderEmb.toOrderHom = v := by
          apply OrderHom.ext
          funext j
          change s (((Fin.last (n + 1)).castSucc).succAbove j.castSucc) =
            s j.castSucc.castSucc
          simp
        dsimp only [cup]
        rw [hp]
        congr 2
        · change t (s ((Fin.last (n + 1)).castSucc.succAbove (Fin.last (n + 1)))) = x
          simp [x]
        · change t (s ((Fin.last (n + 1)).castSucc.succAbove (Fin.last n).castSucc)) = w
          simp [w]
      have hlast : cup n q z t (s.comp (face (n + 1) (Fin.last (n + 2)))) =
          z.1 v * (y + w) := by
        have hp : face (n + 1) (Fin.last (n + 2)) =
            Fin.castSuccOrderEmb.toOrderHom := by
          apply OrderHom.ext
          funext j
          simp [face]
        rw [hp]
        rfl
      have hz : (∑ i : Fin (n + 1), z.1 (a.comp (face n i.castSucc))) = z.1 v := by
        have hz := z.2.2 a
        rw [Fin.sum_univ_castSucc] at hz
        have hface : a.comp (face n (Fin.last (n + 1))) = v := by
          apply OrderHom.ext
          funext j
          simp [face, v]
        rw [hface] at hz
        have hh := congrArg (· + z.1 v) hz
        simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using hh
      rw [Fin.sum_univ_castSucc]
      rw [Fin.sum_univ_castSucc]
      simp_rw [hsmall]
      rw [← Finset.sum_mul, hz, hmid, hlast]
      simp only [mul_add]
      linear_combination (z.1 v) * (CharTwo.add_self_eq_zero x) +
        (z.1 v) * (CharTwo.add_self_eq_zero y) +
        (z.1 v) * (CharTwo.add_self_eq_zero w)
    let bondLabel (n q : ℕ) (z : K n q) (t : Fin (q + 1) →o Fin 2) : K (n + 1) q :=
      ⟨cup n q z (fun i => (t i).val),
        ⟨cup_normalized n q z (fun i => ((t i).val : ZMod 2)),
          cup_closed n q z (fun i => ((t i).val : ZMod 2))⟩⟩
    have bondLabel_natural {n p q : ℕ} (a : Fin (p + 1) →o Fin (q + 1))
        (z : K n q) (t : Fin (q + 1) →o Fin 2) :
        pull a (bondLabel n q z t) = bondLabel n p (pull a z) (t.comp a) := by
      apply Subtype.ext
      funext s
      rfl
    have bondLabel_zero (n q : ℕ) (t : Fin (q + 1) →o Fin 2) :
        bondLabel n q (zero n q) t = zero (n + 1) q := by
      apply Subtype.ext
      funext s
      exact zero_mul _
    have bondLabel_constant (n q : ℕ) (z : K n q) (c : Fin 2) :
        bondLabel n q z (⟨fun _ => c, monotone_const⟩) = zero (n + 1) q := by
      apply Subtype.ext
      funext s
      change _ * ((c.val : ZMod 2) + c.val) = 0
      rw [CharTwo.add_self_eq_zero, mul_zero]
    -- T1: standard simplex coordinates and their affine face maps.
    let Simplex (q : ℕ) :=
      {t : Fin (q + 1) → ℝ // (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1}
    let vertex (q : ℕ) (i : Fin (q + 1)) : Simplex q :=
      ⟨fun j => if j = i then 1 else 0, by
        constructor
        · intro j; dsimp only; split_ifs <;> norm_num
        · simp⟩
    let simplexMap {p q : ℕ} (a : Fin (p + 1) →o Fin (q + 1))
        (t : Simplex p) : Simplex q :=
      ⟨fun j => ∑ i, if a i = j then t.1 i else 0, by
        constructor
        · intro j
          exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp_all [t.2.1])
        · rw [Finset.sum_comm]
          simpa using t.2.2⟩
    have simplexMap_continuous {p q : ℕ} (a : Fin (p + 1) →o Fin (q + 1)) :
        Continuous (simplexMap a) := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro j
      apply continuous_finsetSum
      intro i _
      split_ifs
      · exact (continuous_apply i).comp continuous_subtype_val
      · exact continuous_const
    have simplexMap_apply_image {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (t : Simplex p) (i : Fin (p + 1)) :
        (simplexMap a.toOrderHom t).1 (a i) = t.1 i := by
      change (∑ j, if a j = a i then t.1 j else 0) = t.1 i
      simp [a.injective.eq_iff]
    have simplexMap_apply_outside {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (t : Simplex p) (j : Fin (q + 1)) (hj : j ∉ Set.range a) :
        (simplexMap a.toOrderHom t).1 j = 0 := by
      change (∑ i, if a i = j then t.1 i else 0) = 0
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun h => hj ⟨i, h⟩)
    have simplex_support (q : ℕ) (t : Simplex q) :
        ∃ p, ∃ a : Fin (p + 1) ↪o Fin (q + 1), ∃ u : Simplex p,
          (∀ i, 0 < u.1 i) ∧ simplexMap a.toOrderHom u = t := by
      let S : Finset (Fin (q + 1)) := Finset.univ.filter (fun i => 0 < t.1 i)
      have hS : S.Nonempty := by
        by_contra hempty
        have ht : ∀ i, t.1 i = 0 := by
          intro i
          have hi : ¬ 0 < t.1 i := by
            intro hi
            exact hempty ⟨i, by simp [S, hi]⟩
          exact le_antisymm (le_of_not_gt hi) (t.2.1 i)
        have hh := t.2.2
        simp [ht] at hh
      let p := S.card - 1
      have hcard : S.card = p + 1 := by
        have := Finset.card_pos.mpr hS
        dsimp only [p]
        omega
      let a : Fin (p + 1) ↪o Fin (q + 1) := S.orderEmbOfFin hcard
      have hmem (i : Fin (p + 1)) : a i ∈ S := Finset.orderEmbOfFin_mem S hcard i
      have hpos (i : Fin (p + 1)) : 0 < t.1 (a i) := (Finset.mem_filter.mp (hmem i)).2
      have hsum : ∑ i, t.1 (a i) = 1 := by
        calc
          (∑ i, t.1 (a i)) = ∑ j ∈ S, t.1 j := by
            rw [← Finset.image_orderEmbOfFin_univ S hcard]
            exact (Finset.sum_image (fun i _ j _ h => a.injective h)).symm
          _ = ∑ j, t.1 j := by
            apply Finset.sum_subset (Finset.subset_univ _)
            intro j _ hj
            have hj' : ¬ 0 < t.1 j := by simpa [S] using hj
            exact le_antisymm (le_of_not_gt hj') (t.2.1 j)
          _ = 1 := t.2.2
      let u : Simplex p := ⟨fun i => t.1 (a i), ⟨fun i => (hpos i).le, hsum⟩⟩
      refine ⟨p, a, u, hpos, ?_⟩
      apply Subtype.ext
      funext j
      by_cases hj : j ∈ Set.range a
      · obtain ⟨i, rfl⟩ := hj
        exact simplexMap_apply_image a u i
      · rw [simplexMap_apply_outside a u j hj]
        have hj' : j ∉ S := by
          intro hj'
          apply hj
          rw [show Set.range a = (S : Set (Fin (q + 1))) from
            Finset.range_orderEmbOfFin S hcard]
          exact hj'
        have hj'' : ¬ 0 < t.1 j := by simpa [S] using hj'
        exact (le_antisymm (le_of_not_gt hj'') (t.2.1 j)).symm
    have simplex_support_boundary (q : ℕ) (t : Simplex q) (ht : ∃ j, t.1 j = 0) :
        ∃ p, p < q ∧ ∃ a : Fin (p + 1) ↪o Fin (q + 1), ∃ u : Simplex p,
          (∀ i, 0 < u.1 i) ∧ simplexMap a.toOrderHom u = t := by
      obtain ⟨j, hj⟩ := ht
      obtain ⟨p, a, u, hu, hmap⟩ := simplex_support q t
      have hjout : j ∉ Set.range a := by
        rintro ⟨i, rfl⟩
        have hi := simplexMap_apply_image a u i
        rw [hmap, hj] at hi
        exact (ne_of_gt (hu i)) hi.symm
      have hcard := Fintype.card_lt_of_injective_of_notMem a a.injective hjout
      simp only [Fintype.card_fin] at hcard
      exact ⟨p, by omega, a, u, hu, hmap⟩
    have embedding_factor {m p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (b : Fin (m + 1) ↪o Fin (q + 1)) (hb : ∀ i, b i ∈ Set.range a) :
        ∃ c : Fin (m + 1) ↪o Fin (p + 1), c.comp a = b := by
      have hex : ∀ i, ∃ j, a j = b i := hb
      choose c hc using hex
      let c' : Fin (m + 1) ↪o Fin (p + 1) :=
        OrderEmbedding.ofStrictMono c (by
          intro i j hij
          apply a.lt_iff_lt.mp
          rw [hc i, hc j]
          exact b.strictMono hij)
      refine ⟨c', ?_⟩
      apply DFunLike.ext
      intro i
      exact hc i
    -- T2: finite polynomial coordinates on each original fat simplex.
    let moment (n m : ℕ) (label : K n m) (k : Option (Fin (m + 1)))
        (q : ℕ) (z : K n q) (t : Simplex q) : ℝ :=
      ∑ b : Fin (m + 1) ↪o Fin (q + 1),
        if pull b.toOrderHom z = label then
          (∏ i, t.1 (b i)) * k.elim 1 (fun i => t.1 (b i)) else 0
    have moment_face (n m : ℕ) (label : K n m) (k : Option (Fin (m + 1)))
        {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) (z : K n q) (t : Simplex p) :
        moment n m label k p (pull a.toOrderHom z) t =
          moment n m label k q z (simplexMap a.toOrderHom t) := by
      dsimp only [moment]
      refine Fintype.sum_of_injective
        (fun c : Fin (m + 1) ↪o Fin (p + 1) => c.comp a) ?_ _ _ ?_ ?_
      · intro c d h
        apply DFunLike.ext
        intro i
        apply a.injective
        exact congrArg (fun e : Fin (m + 1) ↪o Fin (q + 1) => e i) h
      · intro b hb
        have hout : ∃ i, b i ∉ Set.range a := by
          by_contra h
          push Not at h
          exact hb (embedding_factor a b h)
        obtain ⟨i, hi⟩ := hout
        have hprod : (∏ j, (simplexMap a.toOrderHom t).1 (b j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (simplexMap_apply_outside a t (b i) hi)
        split_ifs
        · rw [hprod, zero_mul]
        · rfl
      · intro c
        have hlabel : pull c.toOrderHom (pull a.toOrderHom z) =
            pull (c.comp a).toOrderHom z := pull_comp c.toOrderHom a.toOrderHom z
        have hcoord : ∀ i, (simplexMap a.toOrderHom t).1 ((c.comp a) i) = t.1 (c i) := by
          intro i
          exact simplexMap_apply_image a t (c i)
        cases k <;> simp only [Option.elim, hlabel, hcoord]
    have moment_zero (n m : ℕ) (label : K n m) (hlabel : label ≠ zero n m)
        (k : Option (Fin (m + 1))) (q : ℕ) (t : Simplex q) :
        moment n m label k q (zero n q) t = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      rw [pull_zero]
      exact if_neg (Ne.symm hlabel)
    have moment_continuous (n m : ℕ) (label : K n m) (k : Option (Fin (m + 1)))
        (q : ℕ) (z : K n q) : Continuous (moment n m label k q z) := by
      apply continuous_finsetSum
      intro b _
      split_ifs
      · apply Continuous.mul
        · apply continuous_finsetProd
          intro i _
          exact (continuous_apply (b i)).comp continuous_subtype_val
        · cases k with
          | none => exact continuous_const
          | some i => exact (continuous_apply (b i)).comp continuous_subtype_val
      · exact continuous_const
    have moment_lower (n m q : ℕ) (hm : q < m) (label : K n m)
        (k : Option (Fin (m + 1))) (z : K n q) (t : Simplex q) :
        moment n m label k q z t = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      have hh := Fintype.card_le_of_injective b b.injective
      simp only [Fintype.card_fin] at hh
      omega
    have self_embedding (q : ℕ) (b : Fin (q + 1) ↪o Fin (q + 1)) :
        b = OrderEmbedding.id _ := by
      apply OrderEmbedding.range_inj.mp
      rw [Set.range_eq_univ.mpr (Finite.surjective_of_injective b.injective)]
      exact (Set.range_id).symm
    have moment_top (n q : ℕ) (label z : K n q) (k : Option (Fin (q + 1)))
        (t : Simplex q) : moment n q label k q z t =
          if z = label then (∏ i, t.1 i) * k.elim 1 (fun i => t.1 i) else 0 := by
      dsimp only [moment]
      rw [Finset.sum_eq_single_of_mem (OrderEmbedding.id _) (Finset.mem_univ _)
        (by intro b _ hb; exact False.elim (hb (self_embedding q b)))]
      change (if pull OrderHom.id z = label then _ else 0) = _
      rw [pull_id]
      rfl
    -- T3: a characteristic map needs a homeomorphism only on the open cell.
    -- Successive interval coordinates give such a parametrization of the same simplex.
    have simplex_le_one (q : ℕ) (t : Simplex q) (i : Fin (q + 1)) : t.1 i ≤ 1 := by
      calc
        t.1 i ≤ ∑ j, t.1 j := Finset.single_le_sum (fun j _ => t.2.1 j) (Finset.mem_univ i)
        _ = 1 := t.2.2
    let stick : (q : ℕ) → (Fin q → I) → Simplex q :=
      fun q => Nat.rec (fun _ => vertex 0 0) (fun q f u =>
        ⟨Fin.cons (u 0 : ℝ) (fun i => (1 - (u 0 : ℝ)) * (f (fun j => u j.succ)).1 i), by
          constructor
          · intro i
            refine Fin.cases (u 0).2.1 (fun j => ?_) i
            exact mul_nonneg (sub_nonneg.mpr (u 0).2.2) ((f (fun j => u j.succ)).2.1 j)
          · rw [Fin.sum_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [← Finset.mul_sum, (f (fun j => u j.succ)).2.2]
            ring⟩) q
    have stick_head (q : ℕ) (u : Fin (q + 1) → I) : (stick (q + 1) u).1 0 = (u 0 : ℝ) := rfl
    have stick_tail (q : ℕ) (u : Fin (q + 1) → I) (i : Fin (q + 1)) :
        (stick (q + 1) u).1 i.succ =
          (1 - (u 0 : ℝ)) * (stick q (fun j => u j.succ)).1 i := rfl
    have stick_continuous (q : ℕ) : Continuous (stick q) := by
      induction q with
      | zero => exact continuous_const
      | succ q ih =>
        have hhead : Continuous (fun u : Fin (q + 1) → I => (u 0 : ℝ)) :=
          continuous_subtype_val.comp (continuous_apply 0)
        have htail : Continuous (fun u : Fin (q + 1) → I => stick q (fun j => u j.succ)) :=
          ih.comp (continuous_pi (fun j => continuous_apply j.succ))
        apply Continuous.subtype_mk
        apply continuous_pi
        intro i
        refine Fin.cases hhead (fun j => ?_) i
        exact (continuous_const.sub hhead).mul
          ((continuous_apply j).comp (continuous_subtype_val.comp htail))
    have stick_surjective (q : ℕ) : Function.Surjective (stick q) := by
      induction q with
      | zero =>
        intro t
        refine ⟨fun i => Fin.elim0 i, ?_⟩
        apply Subtype.ext
        funext i
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        have ht := t.2.2
        simpa [stick, vertex] using ht.symm
      | succ q ih =>
        intro t
        let h : I := ⟨t.1 0, ⟨t.2.1 0, simplex_le_one (q + 1) t 0⟩⟩
        have hsum : ∑ i : Fin (q + 1), t.1 i.succ = 1 - t.1 0 := by
          have ht := t.2.2
          rw [Fin.sum_univ_succ] at ht
          linarith
        by_cases he : t.1 0 = 1
        · have hz : ∀ i : Fin (q + 1), t.1 i.succ = 0 := by
            intro i
            have hle : t.1 i.succ ≤ ∑ j : Fin (q + 1), t.1 j.succ :=
              Finset.single_le_sum (fun j _ => t.2.1 j.succ) (Finset.mem_univ i)
            rw [hsum, he] at hle
            exact le_antisymm (by linarith) (t.2.1 i.succ)
          refine ⟨Fin.cons h (fun _ => 0), ?_⟩
          apply Subtype.ext
          funext i
          refine Fin.cases (by rfl) (fun j => ?_) i
          rw [stick_tail]
          change (1 - t.1 0) * _ = t.1 j.succ
          rw [he, sub_self, zero_mul, hz]
        · have hp : 0 < 1 - t.1 0 := sub_pos.mpr
            (lt_of_le_of_ne (simplex_le_one (q + 1) t 0) he)
          let v : Simplex q := ⟨fun i => t.1 i.succ / (1 - t.1 0), by
            constructor
            · intro i; exact div_nonneg (t.2.1 i.succ) hp.le
            · simp_rw [div_eq_mul_inv]
              rw [← Finset.sum_mul, hsum, mul_inv_cancel₀ hp.ne']⟩
          obtain ⟨u, hu⟩ := ih v
          refine ⟨Fin.cons h u, ?_⟩
          apply Subtype.ext
          funext i
          refine Fin.cases (by rfl) (fun j => ?_) i
          rw [stick_tail]
          change (1 - t.1 0) * (stick q u).1 j = t.1 j.succ
          rw [hu]
          exact mul_div_cancel₀ _ hp.ne'
    have stick_positive (q : ℕ) (u : Fin q → I) :
        (∀ i, 0 < (stick q u).1 i) ↔ ∀ j, (0 : ℝ) < u j ∧ (u j : ℝ) < 1 := by
      induction q with
      | zero =>
        constructor
        · intro _ j; exact Fin.elim0 j
        · intro _ i
          have hi : i = 0 := Fin.ext (by omega)
          subst i
          norm_num [stick, vertex]
      | succ q ih =>
        constructor
        · intro h
          have hp : 0 < (u 0 : ℝ) := h 0
          have hl : (u 0 : ℝ) < 1 := by
            have hh := h (Fin.succ (0 : Fin (q + 1)))
            rw [stick_tail] at hh
            by_contra hn
            have he : (u 0 : ℝ) = 1 := le_antisymm (u 0).2.2 (le_of_not_gt hn)
            rw [he, sub_self, zero_mul] at hh
            exact (lt_irrefl 0) hh
          have ht : ∀ i, 0 < (stick q (fun j => u j.succ)).1 i := by
            intro i
            have hh := h i.succ
            rw [stick_tail] at hh
            exact (mul_pos_iff_of_pos_left (sub_pos.mpr hl)).mp hh
          intro j
          refine Fin.cases ⟨hp, hl⟩ (fun i => ?_) j
          exact ih (fun j => u j.succ) |>.mp ht i
        · intro h
          have ht := (ih (fun j => u j.succ)).mpr (fun j => h j.succ)
          intro i
          refine Fin.cases (h 0).1 (fun j => ?_) i
          rw [stick_tail]
          exact mul_pos (sub_pos.mpr (h 0).2) (ht j)
    have stick_injective_interior (q : ℕ) : Set.InjOn (stick q)
        {u | ∀ j, (0 : ℝ) < u j ∧ (u j : ℝ) < 1} := by
      induction q with
      | zero => intro u _ v _ _; funext i; exact Fin.elim0 i
      | succ q ih =>
        intro u hu v hv h
        have he : u 0 = v 0 := Subtype.ext (congrArg (fun t => t.1 0) h)
        have ht : stick q (fun j => u j.succ) = stick q (fun j => v j.succ) := by
          apply Subtype.ext
          funext i
          have hh := congrArg (fun t : Simplex (q + 1) => t.1 i.succ) h
          rw [stick_tail, stick_tail, he] at hh
          exact mul_left_cancel₀ (sub_pos.mpr (hv 0).2).ne' hh
        have ht' : (fun j : Fin q => u j.succ) = fun j => v j.succ :=
          ih (fun j => hu j.succ) (fun j => hv j.succ) ht
        funext i
        exact Fin.cases he (fun j => congrFun ht' j) i
    have simplex_positive_isOpen (q : ℕ) : IsOpen {t : Simplex q | ∀ i, 0 < t.1 i} := by
      rw [Set.setOf_forall]
      apply isOpen_iInter_of_finite
      intro i
      exact isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)
    have stick_interior_equiv (q : ℕ) :
        ∃ e : {u : Fin q → I // ∀ i, (0 : ℝ) < u i ∧ (u i : ℝ) < 1} ≃ₜ
          {t : Simplex q // ∀ i, 0 < t.1 i}, ∀ u, (e u).1 = stick q u.1 := by
      let P : Set (Simplex q) := {t | ∀ i, 0 < t.1 i}
      have hQ : IsQuotientMap (stick q) :=
        IsQuotientMap.of_surjective_continuous (stick_surjective q) (stick_continuous q)
      have hQR := hQ.restrictPreimage_isOpen (simplex_positive_isOpen q)
      let e : (stick q ⁻¹' P) ≃ P := Equiv.ofBijective (P.restrictPreimage (stick q))
        ⟨by
          intro u v huv
          apply Subtype.ext
          apply stick_injective_interior q
          · exact (stick_positive q u.1).mp u.2
          · exact (stick_positive q v.1).mp v.2
          · exact congrArg Subtype.val huv,
          hQR.surjective⟩
      let eTop : (stick q ⁻¹' P) ≃ₜ P :=
        e.toHomeomorph (fun _ => hQR.isCoinducing.isOpen_preimage)
      have hP : {u : Fin q → I | ∀ i, (0 : ℝ) < u i ∧ (u i : ℝ) < 1} = stick q ⁻¹' P := by
        ext u
        exact (stick_positive q u).symm
      exact ⟨(Homeomorph.setCongr hP).trans eTop, fun _ => rfl⟩
    have closedBall_coords (q : ℕ) (x : Fin q → ℝ) :
        x ∈ Metric.closedBall 0 1 ↔ ∀ i, -1 ≤ x i ∧ x i ≤ 1 := by
      rw [closedBall_pi _ (by norm_num : (0 : ℝ) ≤ 1)]
      simp [Real.closedBall_eq_Icc, Pi.le_def, forall_and]
    have ball_coords (q : ℕ) (x : Fin q → ℝ) :
        x ∈ Metric.ball 0 1 ↔ ∀ i, -1 < x i ∧ x i < 1 := by
      rw [ball_pi _ (by norm_num : (0 : ℝ) < 1)]
      simp only [Set.mem_pi, Set.mem_univ, forall_const, Real.ball_eq_Ioo,
        Pi.zero_apply, zero_sub, zero_add, Set.mem_Ioo]
    let ballCube (q : ℕ) : (Metric.closedBall (0 : Fin q → ℝ) 1) ≃ₜ (Fin q → I) := {
      toFun := fun x i => ⟨(x.1 i + 1) / 2, by
        have h := (closedBall_coords q x.1).mp x.2 i
        constructor <;> linarith⟩
      invFun := fun t => ⟨fun i => 2 * (t i : ℝ) - 1, by
        apply (closedBall_coords q _).mpr
        intro i
        constructor <;> linarith [(t i).2.1, (t i).2.2]⟩
      left_inv := by intro x; apply Subtype.ext; funext i; dsimp; ring
      right_inv := by intro t; funext i; apply Subtype.ext; dsimp; ring
      continuous_toFun := by
        apply continuous_pi
        intro i
        apply Continuous.subtype_mk
        exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply continuous_pi
        intro i
        exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const }
    have ballCube_interior (q : ℕ) (x : Metric.closedBall (0 : Fin q → ℝ) 1) :
        x.1 ∈ Metric.ball 0 1 ↔
          ∀ i, (0 : ℝ) < ballCube q x i ∧ (ballCube q x i : ℝ) < 1 := by
      rw [ball_coords]
      constructor
      · intro h i
        have hi := h i
        change 0 < (x.1 i + 1) / 2 ∧ (x.1 i + 1) / 2 < 1
        constructor <;> linarith
      · intro h i
        have hi := h i
        change 0 < (x.1 i + 1) / 2 ∧ (x.1 i + 1) / 2 < 1 at hi
        constructor <;> linarith
    let ballCubeInterior (q : ℕ) : (Metric.ball (0 : Fin q → ℝ) 1) ≃ₜ
        {u : Fin q → I // ∀ i, (0 : ℝ) < u i ∧ (u i : ℝ) < 1} := {
      toFun := fun x => ⟨ballCube q ⟨x.1, Metric.ball_subset_closedBall x.2⟩,
        (ballCube_interior q _).mp x.2⟩
      invFun := fun u => ⟨((ballCube q).symm u.1).1,
        (ballCube_interior q _).mpr (by simpa only [(ballCube q).apply_symm_apply] using u.2)⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact congrArg (fun a : Metric.closedBall (0 : Fin q → ℝ) 1 => a.1)
          ((ballCube q).symm_apply_apply ⟨x.1, Metric.ball_subset_closedBall x.2⟩)
      right_inv := by
        intro u
        apply Subtype.ext
        exact (ballCube q).apply_symm_apply _
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (ballCube q).continuous.comp (Continuous.subtype_mk continuous_subtype_val _)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp ((ballCube q).symm.continuous.comp continuous_subtype_val) }
    have ball_simplex_data (q : ℕ) :
        ∃ f : C(Metric.closedBall (0 : Fin q → ℝ) 1, Simplex q), Function.Surjective f ∧
          ∃ e : (Metric.ball (0 : Fin q → ℝ) 1) ≃ₜ {t : Simplex q // ∀ i, 0 < t.1 i},
            (∀ x, f ⟨x.1, Metric.ball_subset_closedBall x.2⟩ = (e x).1) ∧
            (∀ x : Metric.closedBall (0 : Fin q → ℝ) 1,
              x.1 ∈ Metric.sphere 0 1 ↔ ∃ i, (f x).1 i = 0) := by
      obtain ⟨e, he⟩ := stick_interior_equiv q
      let f : C(Metric.closedBall (0 : Fin q → ℝ) 1, Simplex q) :=
        ⟨fun x => stick q (ballCube q x), (stick_continuous q).comp (ballCube q).continuous⟩
      refine ⟨f, (stick_surjective q).comp (ballCube q).surjective,
        (ballCubeInterior q).trans e, ?_, ?_⟩
      · intro x
        exact (he (ballCubeInterior q x)).symm
      · intro x
        have hpos : (∀ i, 0 < (f x).1 i) ↔ x.1 ∈ Metric.ball 0 1 :=
          (stick_positive q (ballCube q x)).trans (ballCube_interior q x).symm
        rw [← Metric.closedBall_sdiff_ball]
        constructor
        · intro hx
          by_contra h
          apply hx.2
          apply hpos.mp
          intro i
          have hne : (f x).1 i ≠ 0 := fun hi => h ⟨i, hi⟩
          exact lt_of_le_of_ne ((f x).2.1 i) (Ne.symm hne)
        · rintro ⟨i, hi⟩
          refine ⟨x.2, ?_⟩
          intro hx
          have hh := hpos.mpr hx i
          rw [hi] at hh
          exact (lt_irrefl 0) hh
    let Raw (n : ℕ) := Σ q : ℕ, Σ z : K n q, Simplex q
    let faceRelation (n : ℕ) (x y : Raw n) : Prop :=
      ∃ p q, ∃ a : Fin (p + 1) →o Fin (q + 1), Function.Injective a ∧
        ∃ (z : K n q) (t : Simplex p),
          x = ⟨p, pull a z, t⟩ ∧ y = ⟨q, z, simplexMap a t⟩
    -- Taking both generating relations at once is X(K_n)/X(0).
    let relation (n : ℕ) (x y : Raw n) : Prop :=
      faceRelation n x y ∨ (x.2.1 = zero n x.1 ∧ y.2.1 = zero n y.1)
    let level (n : ℕ) : BasedSpace.{0} := {
      space := TopCat.of (Quot (relation n))
      point := Quot.mk _ ⟨0, zero n 0, vertex 0 0⟩ }
    let projection (n q : ℕ) (z : K n q) (t : Simplex q) : level n :=
      Quot.mk _ ⟨q, z, t⟩
    have projection_continuous (n q : ℕ) (z : K n q) :
        Continuous (projection n q z) :=
      continuous_quot_mk.comp (continuous_sigmaMk.comp continuous_sigmaMk)
    have projection_face {n p q : ℕ} (a : Fin (p + 1) →o Fin (q + 1))
        (ha : Function.Injective a) (z : K n q) (t : Simplex p) :
        projection n p (pull a z) t = projection n q z (simplexMap a t) :=
      Quot.sound (Or.inl ⟨p, q, a, ha, z, t, rfl, rfl⟩)
    have projection_zero (n q : ℕ) (t : Simplex q) :
        projection n q (zero n q) t = (level n).point :=
      Quot.sound (Or.inr ⟨rfl, rfl⟩)
    let momentMap (n m : ℕ) (label : K n m) (hlabel : label ≠ zero n m)
        (k : Option (Fin (m + 1))) : C(level n, ℝ) := by
      let f : Raw n → ℝ := fun x => moment n m label k x.1 x.2.1 x.2.2
      have hf : ∀ x y, relation n x y → f x = f y := by
        intro x y h
        rcases h with h | ⟨hx, hy⟩
        · obtain ⟨p, q, a, ha, z, t, rfl, rfl⟩ := h
          let a' := OrderEmbedding.ofStrictMono a ((a.monotone.strictMono_iff_injective).2 ha)
          exact moment_face n m label k a' z t
        · dsimp only [f]
          rw [hx, hy, moment_zero n m label hlabel, moment_zero n m label hlabel]
      exact ⟨Quot.lift f hf, continuous_quot_lift hf
        (continuous_sigma (fun q => continuous_sigma (fun z =>
          moment_continuous n m label k q z)))⟩
    have momentMap_projection (n m : ℕ) (label : K n m) (hlabel : label ≠ zero n m)
        (k : Option (Fin (m + 1))) (q : ℕ) (z : K n q) (t : Simplex q) :
        momentMap n m label hlabel k (projection n q z t) = moment n m label k q z t := rfl
    have momentMap_point (n m : ℕ) (label : K n m) (hlabel : label ≠ zero n m)
        (k : Option (Fin (m + 1))) :
        momentMap n m label hlabel k (level n).point = 0 :=
      moment_zero n m label hlabel k 0 (vertex 0 0)
    have positive_rep (n : ℕ) (x : level n) :
        x = (level n).point ∨ ∃ q, ∃ z : K n q, ∃ t : Simplex q,
          z ≠ zero n q ∧ (∀ i, 0 < t.1 i) ∧ projection n q z t = x := by
      induction x using Quot.inductionOn with | h r
      obtain ⟨q, z, t⟩ := r
      obtain ⟨p, a, u, hu, ht⟩ := simplex_support q t
      have he : projection n p (pull a.toOrderHom z) u = projection n q z t := by
        rw [projection_face a.toOrderHom a.injective, ht]
      by_cases hz : pull a.toOrderHom z = zero n p
      · left
        exact he.symm.trans (hz ▸ projection_zero n p u)
      · exact Or.inr ⟨p, pull a.toOrderHom z, u, hz, hu, he⟩
    have moment_separates (n : ℕ) (x y : level n)
        (h : ∀ m (label : K n m) (hlabel : label ≠ zero n m) k,
          momentMap n m label hlabel k x = momentMap n m label hlabel k y) : x = y := by
      rcases positive_rep n x with rfl | ⟨p, z, s, hz, hs, rfl⟩
      · rcases positive_rep n y with rfl | ⟨q, w, t, hw, ht, rfl⟩
        · rfl
        · have hh := h q w hw none
          simp only [momentMap_point, momentMap_projection, moment_top, ite_true] at hh
          have hp : 0 < ∏ i, t.1 i := Finset.prod_pos (fun i _ => ht i)
          simp only [Option.elim_none, mul_one] at hh
          linarith
      · rcases positive_rep n y with rfl | ⟨q, w, t, hw, ht, rfl⟩
        · have hh := h p z hz none
          simp only [momentMap_point, momentMap_projection, moment_top, ite_true] at hh
          have hp : 0 < ∏ i, s.1 i := Finset.prod_pos (fun i _ => hs i)
          simp only [Option.elim_none, mul_one] at hh
          linarith
        · have hp : 0 < ∏ i, s.1 i := Finset.prod_pos (fun i _ => hs i)
          have hq : 0 < ∏ i, t.1 i := Finset.prod_pos (fun i _ => ht i)
          have hpq : p = q := by
            rcases lt_trichotomy p q with hl | he | hl
            · have hh := h q w hw none
              simp only [momentMap_projection, moment_lower n q p hl,
                moment_top, ite_true] at hh
              simp only [Option.elim_none, mul_one] at hh
              linarith
            · exact he
            · have hh := h p z hz none
              simp only [momentMap_projection, moment_top, ite_true,
                moment_lower n p q hl] at hh
              simp only [Option.elim_none, mul_one] at hh
              linarith
          subst q
          have hzw : z = w := by
            by_contra hne
            have hh := h p z hz none
            simp only [momentMap_projection, moment_top,
              ite_true, if_neg (Ne.symm hne)] at hh
            simp only [Option.elim_none, mul_one] at hh
            linarith
          subst w
          have hprod : (∏ i, s.1 i) = ∏ i, t.1 i := by
            have hh := h p z hz none
            simpa only [momentMap_projection, moment_top, ite_true,
              Option.elim_none, mul_one] using hh
          have hst : s = t := by
            apply Subtype.ext
            funext i
            have hh := h p z hz (some i)
            simp only [momentMap_projection, moment_top, ite_true, Option.elim_some] at hh
            rw [← hprod] at hh
            exact mul_left_cancel₀ hp.ne' hh
          rw [hst]
    have level_t2 (n : ℕ) : T2Space (level n) := by
      constructor
      intro x y hxy
      have hex : ∃ m, ∃ label : K n m, ∃ hlabel : label ≠ zero n m, ∃ k,
          momentMap n m label hlabel k x ≠ momentMap n m label hlabel k y := by
        by_contra hh
        apply hxy
        apply moment_separates n x y
        intro m label hlabel k
        by_contra he
        exact hh ⟨m, label, hlabel, k, he⟩
      obtain ⟨m, label, hlabel, k, hk⟩ := hex
      exact separated_by_continuous (momentMap n m label hlabel k).continuous hk
    have projection_positive_embedding (n q : ℕ) (z : K n q) (hz : z ≠ zero n q) :
        IsEmbedding (fun t : {s : Simplex q // ∀ i, 0 < s.1 i} => projection n q z t.1) := by
      let P := {s : Simplex q // ∀ i, 0 < s.1 i}
      let U := {x : level n // momentMap n q z hz none x ≠ 0}
      let f : P → U := fun t => ⟨projection n q z t.1, by
        have hp : 0 < ∏ i, t.1.1 i := Finset.prod_pos (fun i _ => t.2 i)
        simpa only [momentMap_projection, moment_top, ite_true, Option.elim_none, mul_one]
          using hp.ne'⟩
      let g : U → (Fin (q + 1) → ℝ) := fun x i =>
        momentMap n q z hz (some i) x.1 / momentMap n q z hz none x.1
      have hf : Continuous f :=
        Continuous.subtype_mk ((projection_continuous n q z).comp continuous_subtype_val) _
      have hg : Continuous g := by
        apply continuous_pi
        intro i
        exact ((momentMap n q z hz (some i)).continuous.comp continuous_subtype_val).div
          ((momentMap n q z hz none).continuous.comp continuous_subtype_val) (fun x => x.2)
      have hcomp : (g ∘ f) = fun t : P => t.1.1 := by
        funext t i
        change momentMap n q z hz (some i) (projection n q z t.1) /
          momentMap n q z hz none (projection n q z t.1) = t.1.1 i
        simp only [momentMap_projection, moment_top, ite_true, Option.elim_none,
          Option.elim_some, mul_one]
        exact mul_div_cancel_left₀ _ (Finset.prod_pos (fun j _ => t.2 j)).ne'
      have he : IsEmbedding f := IsEmbedding.of_comp hf hg (by
        rw [hcomp]
        exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
      exact IsEmbedding.subtypeVal.comp he
    have positive_not_point (n q : ℕ) (z : K n q) (hz : z ≠ zero n q)
        (t : Simplex q) (ht : ∀ i, 0 < t.1 i) : projection n q z t ≠ (level n).point := by
      intro he
      have hh := congrArg (momentMap n q z hz none) he
      simp only [momentMap_projection, momentMap_point, moment_top, ite_true,
        Option.elim_none, mul_one] at hh
      exact (Finset.prod_pos (fun i _ => ht i)).ne' hh
    have positive_label_unique (n p q : ℕ) (z : K n p) (w : K n q)
        (hz : z ≠ zero n p) (hw : w ≠ zero n q)
        (s : Simplex p) (t : Simplex q) (hs : ∀ i, 0 < s.1 i) (ht : ∀ i, 0 < t.1 i)
        (he : projection n p z s = projection n q w t) :
        (⟨p, z⟩ : Σ r, K n r) = ⟨q, w⟩ := by
      have hp : 0 < ∏ i, s.1 i := Finset.prod_pos (fun i _ => hs i)
      have hq : 0 < ∏ i, t.1 i := Finset.prod_pos (fun i _ => ht i)
      have hpq : p = q := by
        rcases lt_trichotomy p q with hl | hh | hl
        · have hh := congrArg (momentMap n q w hw none) he
          simp only [momentMap_projection, moment_lower n q p hl, moment_top,
            ite_true, Option.elim_none, mul_one] at hh
          linarith
        · exact hh
        · have hh := congrArg (momentMap n p z hz none) he
          simp only [momentMap_projection, moment_lower n p q hl, moment_top,
            ite_true, Option.elim_none, mul_one] at hh
          linarith
      subst q
      have hzw : z = w := by
        by_contra hne
        have hh := congrArg (momentMap n p z hz none) he
        simp only [momentMap_projection, moment_top, ite_true, if_neg (Ne.symm hne),
          Option.elim_none, mul_one] at hh
        linarith
      subst w
      rfl
    have characteristic_data (n q : ℕ) (z : K n q) (hz : z ≠ zero n q) :
        ∃ c : PartialEquiv (Fin q → ℝ) (level n),
          c.source = Metric.ball 0 1 ∧
          ContinuousOn c (Metric.closedBall 0 1) ∧
          ContinuousOn c.symm c.target ∧
          c '' Metric.closedBall 0 1 = Set.range (projection n q z) ∧
          c '' Metric.ball 0 1 = projection n q z '' {t | ∀ i, 0 < t.1 i} ∧
          (∀ x ∈ Metric.sphere 0 1, ∃ t : Simplex q,
            (∃ i, t.1 i = 0) ∧ c x = projection n q z t) := by
      obtain ⟨f, hf, e, he, hb⟩ := ball_simplex_data q
      let g : (Fin q → ℝ) → level n := fun x =>
        if h : x ∈ Metric.closedBall 0 1 then projection n q z (f ⟨x, h⟩) else (level n).point
      have hg (x : Metric.closedBall (0 : Fin q → ℝ) 1) :
          g x.1 = projection n q z (f x) := dif_pos x.2
      have hge (x : Metric.ball (0 : Fin q → ℝ) 1) :
          g x.1 = projection n q z (e x).1 := by
        exact (hg ⟨x.1, Metric.ball_subset_closedBall x.2⟩).trans
          (congrArg (projection n q z) (he x))
      have hgcont : ContinuousOn g (Metric.closedBall 0 1) := by
        rw [continuousOn_iff_continuous_restrict]
        exact ((projection_continuous n q z).comp f.continuous).congr (fun x => (hg x).symm)
      have hgemb : IsEmbedding (fun x : Metric.ball (0 : Fin q → ℝ) 1 => g x.1) := by
        have h := (projection_positive_embedding n q z hz).comp e.isEmbedding
        have hfun : (fun x : Metric.ball (0 : Fin q → ℝ) 1 => g x.1) =
            (fun t : {s : Simplex q // ∀ i, 0 < s.1 i} => projection n q z t.1) ∘ e := by
          funext x
          exact hge x
        rw [hfun]
        exact h
      have hginj : Set.InjOn g (Metric.ball 0 1) := by
        intro x hx y hy hxy
        exact congrArg Subtype.val (hgemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
      let c : PartialEquiv (Fin q → ℝ) (level n) := hginj.toPartialEquiv g (Metric.ball 0 1)
      have hcclosed : c '' Metric.closedBall 0 1 = Set.range (projection n q z) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨f ⟨x, hx⟩, (hg ⟨x, hx⟩).symm⟩
        · rintro ⟨t, rfl⟩
          obtain ⟨x, hx⟩ := hf t
          exact ⟨x.1, x.2, (hg x).trans (congrArg (projection n q z) hx)⟩
      have hcopen : c '' Metric.ball 0 1 = projection n q z '' {t | ∀ i, 0 < t.1 i} := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨(e ⟨x, hx⟩).1, (e ⟨x, hx⟩).2, (hge ⟨x, hx⟩).symm⟩
        · rintro ⟨t, ht, rfl⟩
          obtain ⟨x, hx⟩ := e.surjective ⟨t, ht⟩
          exact ⟨x.1, x.2, (hge x).trans (congrArg (fun t => projection n q z t.1) hx)⟩
      refine ⟨c, rfl, hgcont, ?_, hcclosed, hcopen, ?_⟩
      · rw [continuousOn_iff_continuous_restrict]
        have hinv : Continuous (fun y : c.target =>
            (⟨c.symm y.1, c.map_target y.2⟩ : Metric.ball (0 : Fin q → ℝ) 1)) := by
          apply hgemb.isInducing.continuous_iff.mpr
          exact continuous_subtype_val.congr (fun y => (c.right_inv y.2).symm)
        exact continuous_subtype_val.comp hinv
      · intro x hx
        let x' : Metric.closedBall (0 : Fin q → ℝ) 1 := ⟨x, Metric.sphere_subset_closedBall hx⟩
        exact ⟨f x', (hb x').mp hx, hg x'⟩
    have level_cw (n : ℕ) : ∃ c : CWComplex (Set.univ : Set (level n)),
        ∃ i : c.cell 0, c.map 0 i 0 = (level n).point := by
      choose ch hsource hcont hinv hclosed hopen hbound using characteristic_data n
      let Cell (q : ℕ) := {z : K n q // z ≠ zero n q} ⊕ PLift (q = 0)
      letI (q : ℕ) : Finite (K n q) := labels_finite n q
      letI (q : ℕ) : Fintype (Cell q) := by
        dsimp only [Cell]
        letI : Fintype {z : K n q // z ≠ zero n q} := Fintype.ofFinite _
        infer_instance
      have hb_inj : Set.InjOn (fun _ : Fin 0 → ℝ => (level n).point) (Metric.ball 0 1) := by
        intro x _ y _ _
        funext i
        exact Fin.elim0 i
      let base : PartialEquiv (Fin 0 → ℝ) (level n) :=
        hb_inj.toPartialEquiv (fun _ => (level n).point) (Metric.ball 0 1)
      let m (q : ℕ) (i : Cell q) : PartialEquiv (Fin q → ℝ) (level n) := by
        cases i with
        | inl z => exact ch q z.1 z.2
        | inr h => cases h.down; exact base
      have ms (q : ℕ) (i : Cell q) : (m q i).source = Metric.ball 0 1 := by
        cases i with
        | inl z => exact hsource q z.1 z.2
        | inr h => cases h.down; rfl
      have mc (q : ℕ) (i : Cell q) : ContinuousOn (m q i) (Metric.closedBall 0 1) := by
        cases i with
        | inl z => exact hcont q z.1 z.2
        | inr h => cases h.down; exact continuous_const.continuousOn
      have mi (q : ℕ) (i : Cell q) : ContinuousOn (m q i).symm (m q i).target := by
        cases i with
        | inl z => exact hinv q z.1 z.2
        | inr h =>
          cases h.down
          rw [continuousOn_iff_continuous_restrict]
          apply continuous_pi
          intro i
          exact Fin.elim0 i
      let c : CWComplex (Set.univ : Set (level n)) := {
        cell := Cell
        map := m
        source_eq := ms
        continuousOn := mc
        continuousOn_symm := mi
        pairwiseDisjoint' := by
          intro a _ b _ hab
          obtain ⟨p, a⟩ := a
          obtain ⟨q, b⟩ := b
          apply Set.disjoint_left.mpr
          intro x ha hb
          cases a with
          | inl z =>
            change x ∈ ch p z.1 z.2 '' Metric.ball 0 1 at ha
            rw [hopen p z.1 z.2] at ha
            obtain ⟨s, hs, hsx⟩ := ha
            cases b with
            | inl w =>
              change x ∈ ch q w.1 w.2 '' Metric.ball 0 1 at hb
              rw [hopen q w.1 w.2] at hb
              obtain ⟨t, ht, htx⟩ := hb
              have he := positive_label_unique n p q z.1 w.1 z.2 w.2 s t hs ht (hsx.trans htx.symm)
              apply hab
              have hpq : p = q := congrArg Sigma.fst he
              subst q
              have hzw : z.1 = w.1 := by
                exact eq_of_heq (Sigma.mk.inj he).2
              have hzw' : z = w := Subtype.ext hzw
              subst w
              rfl
            | inr h =>
              cases h.down
              obtain ⟨y, hy, hye⟩ := hb
              exact positive_not_point n p z.1 z.2 s hs (hsx.trans hye.symm)
          | inr h =>
            cases h.down
            obtain ⟨y, hy, hye⟩ := ha
            cases b with
            | inl w =>
              change x ∈ ch q w.1 w.2 '' Metric.ball 0 1 at hb
              rw [hopen q w.1 w.2] at hb
              obtain ⟨t, ht, htx⟩ := hb
              exact positive_not_point n q w.1 w.2 t ht (htx.trans hye.symm)
            | inr h => cases h.down; apply hab; congr 2 <;> exact Subsingleton.elim _ _
        mapsTo' := by
          intro q i
          refine ⟨fun _ => Finset.univ, ?_⟩
          intro x hx
          cases i with
          | inl z =>
            obtain ⟨t, ht, hxt⟩ := hbound q z.1 z.2 x hx
            obtain ⟨r, hr, a, u, hu, hmap⟩ := simplex_support_boundary q t ht
            have he : projection n r (pull a.toOrderHom z.1) u = m q (Sum.inl z) x := by
              exact (projection_face a.toOrderHom a.injective z.1 u).trans
                ((congrArg (projection n q z.1) hmap).trans hxt.symm)
            by_cases hz : pull a.toOrderHom z.1 = zero n r
            · have hepoint : m q (Sum.inl z) x = (level n).point := by
                rw [hz, projection_zero] at he
                exact he.symm
              simp only [Set.mem_iUnion, Set.mem_image]
              refine ⟨0, by omega, Sum.inr ⟨rfl⟩, Finset.mem_univ _, 0, by simp, ?_⟩
              exact hepoint.symm
            · have hmem : m q (Sum.inl z) x ∈
                  m r (Sum.inl ⟨pull a.toOrderHom z.1, hz⟩) '' Metric.closedBall 0 1 := by
                change m q (Sum.inl z) x ∈ ch r (pull a.toOrderHom z.1) hz '' Metric.closedBall 0 1
                rw [hclosed]
                exact ⟨u, he⟩
              exact Set.mem_iUnion_of_mem r (Set.mem_iUnion_of_mem hr
                (Set.mem_iUnion_of_mem (Sum.inl ⟨pull a.toOrderHom z.1, hz⟩)
                  (Set.mem_iUnion_of_mem (Finset.mem_univ _) hmem)))
          | inr h =>
            cases h.down
            have hx0 : x = 0 := by funext i; exact Fin.elim0 i
            have hh := Metric.mem_sphere.mp hx
            rw [hx0, dist_self] at hh
            norm_num at hh
        closed' := by
          intro A _ hA
          apply isQuotientMap_quot_mk.isCoinducing.isClosed_preimage.mp
          apply isClosed_sigma_iff.mpr
          intro q
          apply isClosed_sigma_iff.mpr
          intro z
          change IsClosed ((projection n q z) ⁻¹' A)
          by_cases hz : z = zero n q
          · subst z
            have hf : projection n q (zero n q) = fun _ => (level n).point :=
              funext (projection_zero n q)
            rw [hf]
            by_cases hp : (level n).point ∈ A <;> simp [hp]
          · have hc : IsClosed (A ∩ Set.range (projection n q z)) := by
              have hc := hA q (Sum.inl ⟨z, hz⟩)
              change IsClosed (A ∩ ch q z hz '' Metric.closedBall 0 1) at hc
              rwa [hclosed] at hc
            have hh := hc.preimage (projection_continuous n q z)
            simpa only [Set.preimage_inter, Set.preimage_range, Set.inter_univ] using hh
        union' := by
          apply Set.eq_univ_of_forall
          intro x
          induction x using Quot.inductionOn with | h r
          obtain ⟨q, z, t⟩ := r
          change projection n q z t ∈ _
          by_cases hz : z = zero n q
          · subst z
            rw [projection_zero]
            apply Set.mem_iUnion_of_mem 0
            apply Set.mem_iUnion_of_mem (Sum.inr ⟨rfl⟩)
            exact ⟨0, by simp, rfl⟩
          · apply Set.mem_iUnion_of_mem q
            apply Set.mem_iUnion_of_mem (Sum.inl ⟨z, hz⟩)
            change projection n q z t ∈ ch q z hz '' Metric.closedBall 0 1
            rw [hclosed]
            exact ⟨t, rfl⟩ }
      exact ⟨c, Sum.inr ⟨rfl⟩, rfl⟩
    -- T4: each simplex is metrizable; disjoint sums and final quotients are compactly generated.
    have level_cg (n : ℕ) : UCompactlyGeneratedSpace.{0} (level n) := by
      letI (q : ℕ) : UCompactlyGeneratedSpace.{0} (Simplex q) := inferInstance
      letI : UCompactlyGeneratedSpace.{0} (Raw n) := inferInstance
      exact uCompactlyGeneratedSpace_of_coinduced continuous_quot_mk rfl
    have cw_vertex_wellBased (X : BasedSpace.{0}) [T2Space X]
        [CWComplex (Set.univ : Set X)] (i : RelCWComplex.cell (Set.univ : Set X) 0) :
        let Y : BasedSpace.{0} := ⟨X.space,RelCWComplex.map 0 i 0⟩
        Y.IsWellBased := open Set Metric in by
      clear * - X i
      have cube_boundary_retraction (n : ℕ) :
          ∃ r : C((Fin n → I) × I,(Fin n → I) × I),
            (∀ x, r (x,0)=(x,0)) ∧
            (∀ x, x ∈ Cube.boundary (Fin n) → ∀ t, r (x,t)=(x,t)) ∧
            (∀ q, (r q).2=0 ∨ (r q).1 ∈ Cube.boundary (Fin n)) := by
        let v (x : Fin n → I) (i : Fin n) : ℝ := (x i:ℝ)-1/2
        let m (q : (Fin n → I) × I) : ℝ := max ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
        have hb (x : Fin n → I) : 2*‖v x‖ ≤ 1 := by
          have hh : ‖v x‖ ≤ (1/2:ℝ) := by
            apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
            intro i
            rw [Real.norm_eq_abs]
            apply abs_le.mpr
            constructor <;> dsimp [v] <;> linarith [(x i).property.1,(x i).property.2]
          linarith
        have hm (q : (Fin n → I) × I) : 0 < m q ∧ m q ≤ 1 := by
          constructor
          · have h := le_max_left ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
            change 0 < max _ _
            linarith [q.2.property.2]
          · exact max_le (by linarith [q.2.property.1]) (hb q.1)
        have hcoord (q : (Fin n → I) × I) (i : Fin n) : 2*|(q.1 i:ℝ)-1/2| ≤ m q := by
          have h := norm_le_pi_norm (v q.1) i
          rw [Real.norm_eq_abs] at h
          have he := le_max_right ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
          change 2*‖v q.1‖ ≤ m q at he
          dsimp [v] at h
          linarith
        have hx (q : (Fin n → I) × I) (i : Fin n) :
            1/2+((q.1 i:ℝ)-1/2)/m q ∈ Set.Icc (0:ℝ) 1 := by
          have hl : -(1/2:ℝ) ≤ ((q.1 i:ℝ)-1/2)/m q := by
            apply (le_div_iff₀ (hm q).1).mpr
            linarith [hcoord q i,neg_abs_le ((q.1 i:ℝ)-1/2)]
          have hu : ((q.1 i:ℝ)-1/2)/m q ≤ (1/2:ℝ) := by
            apply (div_le_iff₀ (hm q).1).mpr
            linarith [hcoord q i,le_abs_self ((q.1 i:ℝ)-1/2)]
          constructor <;> linarith
        have hy (q : (Fin n → I) × I) : 2+((q.2:ℝ)-2)/m q ∈ Set.Icc (0:ℝ) 1 := by
          have hl : -(2:ℝ) ≤ ((q.2:ℝ)-2)/m q := by
            apply (le_div_iff₀ (hm q).1).mpr
            have h := le_max_left ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
            change (2-(q.2:ℝ))/2 ≤ m q at h
            linarith
          have hu : ((q.2:ℝ)-2)/m q ≤ (q.2:ℝ)-2 := by
            apply (div_le_iff₀ (hm q).1).mpr
            nlinarith [(hm q).2,q.2.property.2]
          constructor <;> linarith [q.2.property.2]
        have hv : Continuous v := continuous_pi fun i =>
          (continuous_subtype_val.comp (continuous_apply i)).sub continuous_const
        have hmcont : Continuous m :=
          ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).div_const 2).max
            (continuous_const.mul (hv.comp continuous_fst).norm)
        let r : C((Fin n → I) × I,(Fin n → I) × I) := ⟨fun q => (fun i => ⟨_,hx q i⟩,⟨_,hy q⟩),
          (continuous_pi fun i => (continuous_const.add
            (((continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)).sub continuous_const).div hmcont
              (fun q => ne_of_gt (hm q).1))).subtype_mk _).prodMk
            ((continuous_const.add
              (((continuous_subtype_val.comp continuous_snd).sub continuous_const).div hmcont
                (fun q => ne_of_gt (hm q).1))).subtype_mk _)⟩
        have hmzero (x : Fin n → I) : m (x,0)=1 := by
          dsimp [m]
          norm_num only [show ((0:I):ℝ)=0 from rfl,sub_zero,show (2:ℝ)/2=1 by norm_num]
          exact max_eq_left (hb x)
        have hmbound (x : Fin n → I) (hx : x ∈ Cube.boundary (Fin n)) (t : I) : m (x,t)=1 := by
          obtain ⟨i,hi⟩ := hx
          have h : 1 ≤ m (x,t) := by
            have hh := hcoord (x,t) i
            change 2*|(x i:ℝ)-1/2| ≤ m (x,t) at hh
            rcases hi with hi | hi <;> rw [hi] at hh <;> norm_num at hh ⊢ <;> linarith
          exact le_antisymm (hm (x,t)).2 h
        refine ⟨r,?_,?_,?_⟩
        · intro x
          apply Prod.ext
          · funext i
            apply Subtype.ext
            simp [r,hmzero]
          · apply Subtype.ext
            simp [r,hmzero]
        · intro x hx t
          apply Prod.ext
          · funext i
            apply Subtype.ext
            simp [r,hmbound x hx t]
          · apply Subtype.ext
            simp [r,hmbound x hx t]
        · intro q
          by_cases h : 2*‖v q.1‖ ≤ (2-(q.2:ℝ))/2
          · left
            apply Subtype.ext
            change 2+((q.2:ℝ)-2)/m q = 0
            have hd : ((q.2:ℝ)-2)/m q = -2 := by
              apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
              dsimp [m]
              rw [max_eq_left h]
              ring
            rw [hd]
            norm_num
          · have hmax : m q=2*‖v q.1‖ := max_eq_right (le_of_not_ge h)
            have hn : Nonempty (Fin n) := by
              by_contra he
              haveI : IsEmpty (Fin n) := not_nonempty_iff.mp he
              have hv0 : v q.1=0 := Subsingleton.elim _ _
              have := (hm q).1
              rw [hmax,hv0,norm_zero,mul_zero] at this
              exact (lt_irrefl _ this)
            letI := hn
            obtain ⟨i,hi⟩ := (IsGreatest.pi_norm (v q.1)).1
            change ‖v q.1 i‖=‖v q.1‖ at hi
            rw [Real.norm_eq_abs] at hi
            have hmax' : m q=2*|(q.1 i:ℝ)-1/2| := by
              rw [hmax,← hi]
            right
            refine ⟨i,?_⟩
            by_cases ht : 0 ≤ (q.1 i:ℝ)-1/2
            · right
              apply Subtype.ext
              change 1/2+((q.1 i:ℝ)-1/2)/m q = 1
              have hd : ((q.1 i:ℝ)-1/2)/m q = 1/2 := by
                apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
                rw [hmax',abs_of_nonneg ht]
                ring
              rw [hd]
              norm_num
            · left
              apply Subtype.ext
              change 1/2+((q.1 i:ℝ)-1/2)/m q = 0
              have hd : ((q.1 i:ℝ)-1/2)/m q = -(1/2) := by
                apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
                rw [hmax',abs_of_neg (lt_of_not_ge ht)]
                ring
              rw [hd]
              norm_num
      have cube_boundary_hep_general (n : ℕ) {Y : Type} [TopologicalSpace Y]
          (f : C((Fin n → I),Y))
          (g : C((Cube.boundary (Fin n)) × I,Y))
          (hg : ∀ x : Cube.boundary (Fin n), g (x,0)=f x.1) :
          ∃ H : C((Fin n → I) × I,Y), (∀ x, H (x,0)=f x) ∧
            (∀ (x : Cube.boundary (Fin n)) t, H (x.1,t)=g (x,t)) := by
        classical
        obtain ⟨r,hzero,hboundary,hr⟩ := cube_boundary_retraction n
        have hc : IsClosed (Cube.boundary (Fin n)) := by
          have he : Cube.boundary (Fin n)=⋃ i : Fin n, {x : Fin n → I | x i=0 ∨ x i=1} := by
            ext x
            simp [Cube.boundary]
          rw [he]
          apply isClosed_iUnion_of_finite
          intro i
          exact (isClosed_eq (continuous_apply i) continuous_const).union
            (isClosed_eq (continuous_apply i) continuous_const)
        let U : Set ((Fin n → I) × I) := {q | (r q).2=0}
        let V : Set ((Fin n → I) × I) := {q | (r q).1 ∈ Cube.boundary (Fin n)}
        have hU : IsClosed U := isClosed_eq r.continuous.snd continuous_const
        have hV : IsClosed V := hc.preimage r.continuous.fst
        have hUV : U ∪ V=Set.univ := by ext q; exact iff_true_intro (hr q)
        let F (q : (Fin n → I) × I) :=
          if h : (r q).1 ∈ Cube.boundary (Fin n) then g (⟨(r q).1,h⟩,(r q).2) else f (r q).1
        have hu : ContinuousOn F U := (f.continuous.comp r.continuous.fst).continuousOn.congr (by
          intro q hq
          dsimp only [F]
          split_ifs with hb
          · change g (⟨(r q).1,hb⟩,(r q).2)=f (r q).1
            rw [show (r q).2=0 from hq,hg]
          · rfl)
        have hv : ContinuousOn F V := by
          apply continuousOn_iff_continuous_restrict.mpr
          let h : V → (Cube.boundary (Fin n)) × I := fun q =>
            (⟨(r q.1).1,q.property⟩,(r q.1).2)
          have hh : Continuous h :=
            ((r.continuous.comp continuous_subtype_val).fst.subtype_mk _).prodMk
              (r.continuous.comp continuous_subtype_val).snd
          apply (g.continuous.comp hh).congr
          intro q
          change g (⟨(r q.1).1,q.property⟩,(r q.1).2)=F q.1
          dsimp only [F]
          rw [dif_pos (show (r q.1).1 ∈ Cube.boundary (Fin n) from q.property)]
        have hF : Continuous F := continuousOn_univ.mp (hUV ▸ hu.union_of_isClosed hv hU hV)
        refine ⟨⟨F,hF⟩,?_,?_⟩
        · intro x
          change F (x,0)=f x
          dsimp only [F]
          simp only [hzero]
          split_ifs with hx
          · exact hg ⟨x,hx⟩
          · rfl
        · intro x t
          change F (x.1,t)=g (x,t)
          dsimp only [F]
          simp only [hboundary x.1 x.property t,dif_pos x.property]
      have closedBall_boundary_hep (n : ℕ) {Y : Type} [TopologicalSpace Y]
          (f : C(Metric.closedBall (0 : Fin n → ℝ) 1,Y))
          (g : C((Metric.sphere (0 : Fin n → ℝ) 1) × I,Y))
          (hg : ∀ x : Metric.sphere (0 : Fin n → ℝ) 1,
            g (x,0)=f ⟨x.1,Metric.sphere_subset_closedBall x.2⟩) :
          ∃ H : C((Metric.closedBall (0 : Fin n → ℝ) 1) × I,Y),
            (∀ x, H (x,0)=f x) ∧
            (∀ (x : Metric.sphere (0 : Fin n → ℝ) 1) t,
              H (⟨x.1,Metric.sphere_subset_closedBall x.2⟩,t)=g (x,t)) := by
        have hc (z : Fin n → ℝ) : z ∈ Metric.closedBall 0 1 ↔
            ∀ i, -1≤z i ∧ z i≤1 := by
          rw [closedBall_pi _ (by norm_num : (0:ℝ)≤1)]
          simp [Real.closedBall_eq_Icc,Pi.le_def,forall_and]
        have hb (z : Fin n → ℝ) : z ∈ Metric.ball 0 1 ↔ ∀ i, -1<z i ∧ z i<1 := by
          rw [ball_pi _ (by norm_num : (0:ℝ)<1)]
          simp only [Set.mem_pi,Set.mem_univ,forall_const,Real.ball_eq_Ioo,Pi.zero_apply,
            zero_sub,zero_add,Set.mem_Ioo]
        let E : (Metric.closedBall (0 : Fin n → ℝ) 1) ≃ₜ (Fin n → I) :=
          { toFun := fun z i => ⟨(z.1 i+1)/2,by
              have h := (hc _).mp z.2 i
              constructor <;> linarith⟩
            invFun := fun t => ⟨fun i => 2*(t i:ℝ)-1,by
              apply (hc _).mpr
              intro i
              constructor <;> linarith [(t i).property.1,(t i).property.2]⟩
            left_inv := by intro z; apply Subtype.ext; funext i; dsimp; ring
            right_inv := by intro t; funext i; apply Subtype.ext; dsimp; ring
            continuous_toFun := by
              apply continuous_pi
              intro i
              apply Continuous.subtype_mk
              exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2
            continuous_invFun := by
              apply Continuous.subtype_mk
              apply continuous_pi
              intro i
              exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const }
        have hEb (z : Metric.closedBall (0 : Fin n → ℝ) 1) :
            z.1 ∈ Metric.sphere 0 1 ↔ E z ∈ Cube.boundary (Fin n) := by
          constructor
          · intro hz
            by_contra hn
            have hzball : z.1 ∈ Metric.ball 0 1 := by
              apply (hb _).mpr
              intro i
              have h0 : E z i≠0 := fun h => hn ⟨i,Or.inl h⟩
              have h1 : E z i≠1 := fun h => hn ⟨i,Or.inr h⟩
              have hi := (hc _).mp z.2 i
              constructor
              · apply lt_of_le_of_ne hi.1
                intro h
                apply h0
                apply Subtype.ext
                change (z.1 i+1)/2=0
                rw [← h]
                norm_num
              · apply lt_of_le_of_ne hi.2
                intro h
                apply h1
                apply Subtype.ext
                change (z.1 i+1)/2=1
                rw [h]
                norm_num
            exact Metric.sphere_disjoint_ball.le_bot ⟨hz,hzball⟩
          · rintro ⟨i,hi⟩
            rw [← Metric.closedBall_sdiff_ball]
            refine ⟨z.2,?_⟩
            intro hz
            have hzi := (hb _).mp hz i
            rcases hi with hi | hi
            · have hh := congrArg Subtype.val hi
              change (z.1 i+1)/2=0 at hh
              linarith
            · have hh := congrArg Subtype.val hi
              change (z.1 i+1)/2=1 at hh
              linarith
        let f' : C((Fin n → I),Y) := f.comp ⟨E.symm,E.symm.continuous⟩
        let g' : C((Cube.boundary (Fin n)) × I,Y) :=
          ⟨fun p => g (⟨(E.symm p.1.1).1,(hEb _).mpr (by simpa only [E.apply_symm_apply] using p.1.2)⟩,p.2),
            g.continuous.comp
              (((continuous_subtype_val.comp (E.symm.continuous.comp
                (continuous_subtype_val.comp continuous_fst))).subtype_mk _).prodMk continuous_snd)⟩
        obtain ⟨F,hF0,hFb⟩ := cube_boundary_hep_general n f' g' (by
          intro x
          exact hg ⟨(E.symm x.1).1,(hEb _).mpr (by simpa only [E.apply_symm_apply] using x.2)⟩)
        refine ⟨F.comp ⟨fun p => (E p.1,p.2),(E.continuous.comp continuous_fst).prodMk continuous_snd⟩,
          ?_,?_⟩
        · intro x
          change F (E x,0)=f x
          rw [hF0]
          change f (E.symm (E x))=f x
          rw [E.symm_apply_apply]
        · intro x t
          let z : Metric.closedBall (0 : Fin n → ℝ) 1 := ⟨x.1,Metric.sphere_subset_closedBall x.2⟩
          change F (E z,t)=g (x,t)
          rw [hFb ⟨E z,(hEb z).mp x.2⟩]
          change g (⟨(E.symm (E z)).1,_⟩,t)=g (x,t)
          simp only [E.symm_apply_apply]
          rfl
      have cw_boundary_continuous (X : Type) [TopologicalSpace X] [T2Space X]
          [CWComplex (Set.univ : Set X)] (Z : Type) [TopologicalSpace Z]
          (F : X × I → Z) (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
          (hF : ∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
            Continuous (fun p : (closedBall (0 : Fin m → ℝ) 1) × I =>
              F (RelCWComplex.map m j p.1,p.2))) :
          Continuous (fun p : (sphere (0 : Fin n → ℝ) 1) × I =>
            F (RelCWComplex.map n i p.1,p.2)) := by
        classical
        have hcell (m : ℕ) (hm : m < n) (j : RelCWComplex.cell (Set.univ : Set X) m) :
            ContinuousOn F ((RelCWComplex.closedCell m j) ×ˢ (Set.univ : Set I)) := by
          let c : C(closedBall (0 : Fin m → ℝ) 1,RelCWComplex.closedCell m j) :=
            ⟨fun z => ⟨RelCWComplex.map m j z,⟨z,z.property,rfl⟩⟩,
              (RelCWComplex.continuousOn m j).restrict.subtype_mk _⟩
          have hc : IsQuotientMap c := IsQuotientMap.of_surjective_continuous (by
            rintro ⟨x,z,hz,rfl⟩
            exact ⟨⟨z,hz⟩,rfl⟩) c.continuous
          have h : Continuous (fun p : (RelCWComplex.closedCell m j) × I => F (p.1,p.2)) :=
            hc.continuous_lift_prod_left (hF m hm j)
          apply continuousOn_iff_continuous_restrict.mpr
          exact h.comp (((continuous_fst.comp continuous_subtype_val).subtype_mk
            (fun p => p.2.1)).prodMk (continuous_snd.comp continuous_subtype_val))
        obtain ⟨J,hJ⟩ := CWComplex.mapsTo (C := (Set.univ : Set X)) n i
        let A := Σ m : Fin n, ↥(J m)
        let S (a : A) : Set (X × I) := (RelCWComplex.closedCell a.1 a.2.1) ×ˢ Set.univ
        have hS : ∀ a, IsClosed (S a) := fun _ =>
          RelCWComplex.isClosed_closedCell.prod isClosed_univ
        have hcont : ContinuousOn F (⋃ a : A, S a) :=
          (locallyFinite_of_finite S).continuousOn_iUnion hS (fun a => hcell a.1 a.1.2 a.2.1)
        let g : (sphere (0 : Fin n → ℝ) 1) × I → X × I :=
          fun p => (RelCWComplex.map n i p.1,p.2)
        have hg : Continuous g :=
          (((RelCWComplex.continuousOn n i).mono sphere_subset_closedBall).restrict.comp
            continuous_fst).prodMk continuous_snd
        have hmap : MapsTo g Set.univ (⋃ a : A, S a) := by
          intro p _
          have h := hJ p.1.2
          simp only [Set.mem_iUnion,exists_prop] at h
          obtain ⟨m,hm,j,hj,hx⟩ := h
          exact Set.mem_iUnion.mpr ⟨⟨⟨m,hm⟩,⟨j,hj⟩⟩,hx,trivial⟩
        exact continuousOn_univ.mp (hcont.comp hg.continuousOn hmap)
      have cw_extend_dimension
          (X : Type) [TopologicalSpace X] [T2Space X]
          [CWComplex (Set.univ : Set X)] (Z : Type) [TopologicalSpace Z]
          (f : C(X,Z)) (n : ℕ) (F : X × I → Z)
          (hF0 : ∀ x, F (x,0)=f x)
          (hF : ∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
            Continuous (fun p : (closedBall (0 : Fin m → ℝ) 1) × I =>
              F (RelCWComplex.map m j p.1,p.2))) :
          ∃ G : X × I → Z,
            (∀ x, G (x,0)=f x) ∧
            (∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
              ∀ x ∈ RelCWComplex.closedCell m j, ∀ t, G (x,t)=F (x,t)) ∧
            (∀ i : RelCWComplex.cell (Set.univ : Set X) n,
              Continuous (fun p : (closedBall (0 : Fin n → ℝ) 1) × I =>
                G (RelCWComplex.map n i p.1,p.2))) := by
        classical
        have hExt (i : RelCWComplex.cell (Set.univ : Set X) n) :
            ∃ E : C((closedBall (0 : Fin n → ℝ) 1) × I,Z),
              (∀ z, E (z,0)=f (RelCWComplex.map n i z)) ∧
              (∀ (z : sphere (0 : Fin n → ℝ) 1) t,
                E (⟨z.1,sphere_subset_closedBall z.2⟩,t)=F (RelCWComplex.map n i z,t)) := by
          apply closedBall_boundary_hep n
            ⟨fun z => f (RelCWComplex.map n i z),
              f.continuous.comp (RelCWComplex.continuousOn n i).restrict⟩
            ⟨fun p => F (RelCWComplex.map n i p.1,p.2),cw_boundary_continuous X Z F n i hF⟩
          exact fun z => hF0 _
        choose E hE0 hEb using hExt
        let New (x : X) := ∃ i : RelCWComplex.cell (Set.univ : Set X) n,
          x ∈ RelCWComplex.openCell n i
        have hinv (i : RelCWComplex.cell (Set.univ : Set X) n) {x : X}
            (hx : x ∈ RelCWComplex.openCell n i) :
            (RelCWComplex.map n i).symm x ∈ closedBall (0 : Fin n → ℝ) 1 := by
          have ht : x ∈ (RelCWComplex.map n i).target := by
            rw [← PartialEquiv.image_source_eq_target,RelCWComplex.source_eq]
            exact hx
          have hs := (RelCWComplex.map n i).map_target ht
          rw [RelCWComplex.source_eq] at hs
          exact ball_subset_closedBall hs
        let G : X × I → Z := fun p => if h : New p.1 then
          E (Classical.choose h) (⟨(RelCWComplex.map n (Classical.choose h)).symm p.1,
            hinv _ (Classical.choose_spec h)⟩,p.2) else F p
        have hopen {x : X} (i : RelCWComplex.cell (Set.univ : Set X) n)
            (hx : x ∈ RelCWComplex.openCell n i) (t : I) :
            G (x,t)=E i (⟨(RelCWComplex.map n i).symm x,hinv i hx⟩,t) := by
          have hnew : New x := ⟨i,hx⟩
          have hi : Classical.choose hnew=i := by
            by_contra h
            have hd := RelCWComplex.disjoint_openCell_of_ne
              (C := (Set.univ : Set X)) (n := n) (m := n)
              (i := Classical.choose hnew) (j := i) (by simpa using h)
            exact hd.le_bot ⟨Classical.choose_spec hnew,hx⟩
          dsimp only [G]
          rw [dif_pos hnew]
          subst hi
          rfl
        have hnone {x : X} (hx : x ∈ RelCWComplex.skeletonLT (Set.univ : Set X) n) :
            ¬New x := by
          rintro ⟨i,hi⟩
          exact (RelCWComplex.disjoint_skeletonLT_openCell (C := (Set.univ : Set X))
            (j := i) (le_refl (n : ℕ∞))).le_bot ⟨hx,hi⟩
        refine ⟨G,?_,?_,?_⟩
        · intro x
          by_cases hx : New x
          · rw [hopen (Classical.choose hx) (Classical.choose_spec hx) 0,hE0]
            have ht : x ∈ (RelCWComplex.map n (Classical.choose hx)).target := by
              rw [← PartialEquiv.image_source_eq_target,RelCWComplex.source_eq]
              exact Classical.choose_spec hx
            rw [PartialEquiv.right_inv _ ht]
          · simp only [G,dif_neg hx,hF0]
        · intro m hm j x hx t
          have hn : ¬New x := by
            rintro ⟨i,hi⟩
            exact (RelCWComplex.disjoint_skeleton_openCell (C := (Set.univ : Set X))
              (j := i) (ENat.coe_lt_coe.mpr hm)).le_bot
              ⟨RelCWComplex.closedCell_subset_skeleton m j hx,hi⟩
          exact dif_neg hn
        · intro i
          apply (E i).continuous.congr
          intro p
          by_cases hp : p.1.1 ∈ ball (0 : Fin n → ℝ) 1
          · have hx : RelCWComplex.map n i p.1 ∈ RelCWComplex.openCell n i :=
              ⟨p.1,hp,rfl⟩
            rw [hopen i hx p.2]
            have he : (RelCWComplex.map n i).symm (RelCWComplex.map n i p.1)=p.1 :=
              (RelCWComplex.map n i).left_inv (by rw [RelCWComplex.source_eq]; exact hp)
            exact congrArg (fun z : closedBall (0 : Fin n → ℝ) 1 => E i (z,p.2))
              (Subtype.ext he.symm)
          · have hs : p.1.1 ∈ sphere (0 : Fin n → ℝ) 1 := by
              rw [← closedBall_sdiff_ball]
              exact ⟨p.1.2,hp⟩
            have hx : RelCWComplex.map n i p.1 ∈
                RelCWComplex.skeletonLT (Set.univ : Set X) n :=
              RelCWComplex.cellFrontier_subset_skeletonLT n i ⟨p.1,hs,rfl⟩
            change E i p = G (RelCWComplex.map n i p.1,p.2)
            rw [show G (RelCWComplex.map n i p.1,p.2)=F (RelCWComplex.map n i p.1,p.2)
              from dif_neg (hnone hx)]
            exact hEb i ⟨p.1,hs⟩ p.2
      have cw_cylinder_closed (X : Type) [TopologicalSpace X] [T2Space X]
          [CWComplex (Set.univ : Set X)] (F : Set (X × I))
          (hF : ∀ n (i : RelCWComplex.cell (Set.univ : Set X) n),
            IsClosed ((fun p : (closedBall (0 : Fin n → ℝ) 1) × I =>
              (RelCWComplex.map n i p.1,p.2)) ⁻¹' F)) : IsClosed F := by
        let A := Σ n : ℕ, Σ i : RelCWComplex.cell (Set.univ : Set X) n,
          closedBall (0 : Fin n → ℝ) 1
        let π : A → X := fun a => RelCWComplex.map a.1 a.2.1 a.2.2
        have hπcont : Continuous π := by
          apply continuous_sigma
          intro n
          apply continuous_sigma
          intro i
          exact (RelCWComplex.continuousOn n i).restrict
        have hπsurj : Function.Surjective π := by
          intro x
          have h : x ∈ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
              RelCWComplex.closedCell n i := by rw [CWComplex.union]; trivial
          obtain ⟨n,i,z,hz,hx⟩ := by simpa only [Set.mem_iUnion,RelCWComplex.closedCell,Set.mem_image] using h
          exact ⟨⟨n,i,z,hz⟩,hx⟩
        have hπ : IsQuotientMap π := by
          apply isQuotientMap_iff_isClosed.mpr
          refine ⟨hπsurj,fun S => ⟨fun hS => hS.preimage hπcont,?_⟩⟩
          intro hS
          apply (CWComplex.closed (Set.univ : Set X) S (Set.subset_univ S)).mpr
          intro n i
          let c : C(closedBall (0 : Fin n → ℝ) 1,X) :=
            ⟨fun z => RelCWComplex.map n i z,(RelCWComplex.continuousOn n i).restrict⟩
          have hc : IsClosed (c ⁻¹' S) := by
            exact hS.preimage (continuous_sigmaMk.comp continuous_sigmaMk)
          have him : c '' (c ⁻¹' S)=S ∩ RelCWComplex.closedCell n i := by
            ext x
            constructor
            · rintro ⟨z,hz,rfl⟩
              exact ⟨hz,⟨z,z.property,rfl⟩⟩
            · rintro ⟨hx,z,hz,rfl⟩
              exact ⟨⟨z,hz⟩,hx,rfl⟩
          rw [← him]
          exact (hc.isCompact.image c.continuous).isClosed
        have hprod : IsClosed ((fun p : A × I => (π p.1,p.2)) ⁻¹' F) := by
          let e : A × I ≃ₜ Σ n : ℕ,
              (Σ i : RelCWComplex.cell (Set.univ : Set X) n,
                closedBall (0 : Fin n → ℝ) 1) × I := Homeomorph.sigmaProdDistrib
          apply e.symm.isQuotientMap.isCoinducing.isClosed_preimage.mp
          apply isClosed_sigma_iff.mpr
          intro n
          let e' : (Σ i : RelCWComplex.cell (Set.univ : Set X) n,
              closedBall (0 : Fin n → ℝ) 1) × I ≃ₜ
              Σ i : RelCWComplex.cell (Set.univ : Set X) n,
                (closedBall (0 : Fin n → ℝ) 1) × I := Homeomorph.sigmaProdDistrib
          apply e'.symm.isQuotientMap.isCoinducing.isClosed_preimage.mp
          apply isClosed_sigma_iff.mpr
          intro i
          exact hF n i
        let liftπ : A × I → ULift.{0} (X × I) := fun p => ⟨π p.1,p.2⟩
        letI : TopologicalSpace (ULift.{0} (X × I)) := TopologicalSpace.coinduced liftπ inferInstance
        have hs : IsClosed {q : ULift.{0} (X × I) | q.down ∈ F} := by
          rw [isClosed_coinduced]
          exact hprod
        have hc : Continuous (fun p : X × I => (⟨p⟩ : ULift.{0} (X × I))) := by
          apply hπ.continuous_lift_prod_left
          exact continuous_coinduced_rng
        exact hs.preimage hc
      have cw_vertex_hep
          (X : Type) [TopologicalSpace X] [T2Space X]
          [CWComplex (Set.univ : Set X)] (Z : Type) [TopologicalSpace Z]
          (i₀ : RelCWComplex.cell (Set.univ : Set X) 0)
          (f : C(X,Z)) (p : C(I,Z)) (hp : p 0=f (RelCWComplex.map 0 i₀ 0)) :
          ∃ H : C(X × I,Z), (∀ x, H (x,0)=f x) ∧
            (∀ t, H (RelCWComplex.map 0 i₀ 0,t)=p t) := by
        classical
        let v : X := RelCWComplex.map 0 i₀ 0
        let Pack (n : ℕ) := {F : X × I → Z //
          (∀ x, F (x,0)=f x) ∧ (∀ t, F (v,t)=p t) ∧
          (∀ m ≤ n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
            Continuous (fun q : (closedBall (0 : Fin m → ℝ) 1) × I =>
              F (RelCWComplex.map m j q.1,q.2)))}
        let F0 : X × I → Z := fun q => if q.1=v then p q.2 else f q.1
        have hzero : ∀ z : Fin 0 → ℝ, z=0 := fun _ => Subsingleton.elim _ _
        have hF00 : ∀ x, F0 (x,0)=f x := by
          intro x
          dsimp only [F0]
          split_ifs with h
          · subst x; exact hp
          · rfl
        have hF0v : ∀ t, F0 (v,t)=p t := by intro t; exact if_pos rfl
        have hF0c (i : RelCWComplex.cell (Set.univ : Set X) 0) :
            Continuous (fun q : (closedBall (0 : Fin 0 → ℝ) 1) × I =>
              F0 (RelCWComplex.map 0 i q.1,q.2)) := by
          by_cases h : RelCWComplex.map 0 i 0=v
          · apply (p.continuous.comp continuous_snd).congr
            intro q
            dsimp only [F0]
            rw [hzero q.1,h,if_pos rfl]
            rfl
          · apply continuous_const.congr
            intro q
            dsimp only [F0]
            rw [hzero q.1,if_neg h]
        let init : Pack 0 := ⟨F0,hF00,hF0v,by
          intro m hm i
          have hm0 : m=0 := Nat.eq_zero_of_le_zero hm
          subst m
          exact hF0c i⟩
        have hstep (n : ℕ) (P : Pack n) : ∃ Q : Pack (n+1),
            ∀ m ≤ n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
              ∀ x ∈ RelCWComplex.closedCell m j, ∀ t, Q.1 (x,t)=P.1 (x,t) := by
          obtain ⟨G,hG0,hGold,hGc⟩ := cw_extend_dimension X Z f (n+1) P.1 P.2.1
            (fun m hm j => P.2.2.2 m (Nat.le_of_lt_succ hm) j)
          have hv : v ∈ RelCWComplex.closedCell 0 i₀ :=
            ⟨0,by simp,rfl⟩
          refine ⟨⟨G,hG0,?_,?_⟩,?_⟩
          · intro t
            exact (hGold 0 (Nat.zero_lt_succ n) i₀ v hv t).trans (P.2.2.1 t)
          · intro m hm j
            rcases Nat.lt_or_eq_of_le hm with hm | rfl
            · apply (P.2.2.2 m (Nat.le_of_lt_succ hm) j).congr
              intro q
              exact (hGold m hm j _ ⟨q.1,q.1.2,rfl⟩ q.2).symm
            · exact hGc j
          · intro m hm j x hx t
            exact hGold m (Nat.lt_succ_of_le hm) j x hx t
        let next (n : ℕ) (P : Pack n) : Pack (n+1) := Classical.choose (hstep n P)
        have hnext (n : ℕ) (P : Pack n) :
            ∀ m ≤ n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
              ∀ x ∈ RelCWComplex.closedCell m j, ∀ t, (next n P).1 (x,t)=P.1 (x,t) :=
          Classical.choose_spec (hstep n P)
        let seq : (n : ℕ) → Pack n := fun n => Nat.rec init (fun n P => next n P) n
        have hseq (n : ℕ) : seq (n+1)=next n (seq n) := rfl
        have hstable (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) m)
            (x : X) (hx : x ∈ RelCWComplex.closedCell m i) (t : I)
            (a b : ℕ) (hma : m ≤ a) (hab : a ≤ b) : (seq b).1 (x,t)=(seq a).1 (x,t) := by
          induction b,hab using Nat.le_induction with
          | base => rfl
          | succ b hab ih =>
            rw [hseq]
            exact (hnext b (seq b) m (hma.trans hab) i x hx t).trans ih
        have hcover (x : X) : ∃ n : ℕ, ∃ i : RelCWComplex.cell (Set.univ : Set X) n,
            x ∈ RelCWComplex.closedCell n i := by
          have hx : x ∈ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
              RelCWComplex.closedCell n i := by rw [CWComplex.union]; trivial
          simpa only [mem_iUnion] using hx
        choose dim cell hcell using hcover
        let H : X × I → Z := fun q => (seq (dim q.1)).1 q
        have hHcell (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) m)
            (x : X) (hx : x ∈ RelCWComplex.closedCell m i) (t : I) :
            H (x,t)=(seq m).1 (x,t) := by
          rcases le_total m (dim x) with h | h
          · exact hstable m i x hx t m (dim x) (le_refl _) h
          · exact (hstable (dim x) (cell x) x (hcell x) t (dim x) m (le_refl _) h).symm
        have hH : Continuous H := by
          apply continuous_iff_isClosed.mpr
          intro S hS
          apply cw_cylinder_closed X
          intro n i
          have hc : Continuous (fun q : (closedBall (0 : Fin n → ℝ) 1) × I =>
              H (RelCWComplex.map n i q.1,q.2)) := by
            apply ((seq n).2.2.2 n (le_refl _) i).congr
            intro q
            exact (hHcell n i _ ⟨q.1,q.1.2,rfl⟩ q.2).symm
          exact hS.preimage hc
        exact ⟨⟨H,hH⟩,fun x => (seq (dim x)).2.1 x,fun t => (seq (dim v)).2.2.1 t⟩
      refine ⟨isClosed_singleton,?_⟩
      intro Z f p hp
      exact cw_vertex_hep X Z i f p hp
    have level_good : ∀ n, (level n).IsGood := by
      intro n
      letI : T2Space (level n) := level_t2 n
      obtain ⟨c, i, hi⟩ := level_cw n
      letI : CWComplex (Set.univ : Set (level n)) := c
      have hwb : (level n).IsWellBased := by
        have hw := cw_vertex_wellBased (level n) i
        change ({ space := (level n).space, point := c.map 0 i 0 } : BasedSpace).IsWellBased at hw
        rw [hi] at hw
        exact hw
      refine ⟨level_cg n, hwb, level n, inferInstance, ⟨c⟩, hwb, 𝟙 _, 𝟙 _, ?_, ?_⟩
      all_goals exact ContinuousMap.HomotopicRel.refl _
    -- C2, degree zero: identify the components without a positive-dimensional approximation.
    have k0_constant (q : ℕ) (z : K 0 q) :
        z = constant q (z.1 ⟨fun _ => 0, monotone_const⟩) := by
      apply Subtype.ext
      funext a
      let b : Fin 2 →o Fin (q + 1) := ⟨fun i => if i = 0 then 0 else a 0, by
        intro i j hij
        dsimp only
        by_cases hi : i = 0
        · simp only [hi, ↓reduceIte]
          exact Fin.zero_le _
        · have hj : j ≠ 0 := by
            intro hj
            apply hi
            exact le_antisymm (hj ▸ hij) (Fin.zero_le _)
          simp only [hi, hj, ↓reduceIte, le_refl]⟩
      have hz := z.2.2 b
      have h0 : b.comp (face 0 (0 : Fin 2)) = a := by
        apply OrderHom.ext
        funext i
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        rfl
      have h1 : b.comp (face 0 (1 : Fin 2)) = ⟨fun _ => 0, monotone_const⟩ := by
        apply OrderHom.ext
        funext i
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        rfl
      change (∑ i : Fin 2, z.1 (b.comp (face 0 i))) = 0 at hz
      simp only [Fin.sum_univ_two, h0, h1] at hz
      change z.1 a = z.1 ⟨fun _ => 0, monotone_const⟩
      have hh := congrArg (· + z.1 ⟨fun _ => 0, monotone_const⟩) hz
      simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using hh
    let segment (q : ℕ) (a b : Simplex q) : C(I, Simplex q) :=
      ⟨fun t => ⟨fun i => (1 - (t : ℝ)) * a.1 i + (t : ℝ) * b.1 i, by
        constructor
        · intro i
          exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (a.2.1 i))
            (mul_nonneg t.2.1 (b.2.1 i))
        · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, a.2.2, b.2.2]
          ring⟩, by
        apply Continuous.subtype_mk
        apply continuous_pi
        intro i
        fun_prop⟩
    have segment_zero (q : ℕ) (a b : Simplex q) : segment q a b 0 = a := by
      apply Subtype.ext
      funext i
      simp [segment]
    have segment_one (q : ℕ) (a b : Simplex q) : segment q a b 1 = b := by
      apply Subtype.ext
      funext i
      simp [segment]
    have projection_vertex (n q : ℕ) (z : K n q) (i : Fin (q + 1)) :
        projection n q z (vertex q i) =
          projection n 0 (pull ⟨fun _ => i, monotone_const⟩ z) (vertex 0 0) := by
      let a : Fin 1 →o Fin (q + 1) := ⟨fun _ => i, monotone_const⟩
      have ha : Function.Injective a := fun _ _ _ => Subsingleton.elim _ _
      have hv : simplexMap a (vertex 0 0) = vertex q i := by
        apply Subtype.ext
        funext j
        simp [simplexMap, vertex, a, eq_comm]
      rw [← hv]
      exact (projection_face a ha z (vertex 0 0)).symm
    have projection_vertex_pos (n q : ℕ) (hn : 0 < n) (z : K n q)
        (i : Fin (q + 1)) : projection n q z (vertex q i) = (level n).point := by
      rw [projection_vertex]
      have he : pull ⟨fun _ => i, monotone_const⟩ z = zero n 0 :=
        (k_subsingleton n 0 hn).elim _ _
      rw [he, projection_zero]
    have point_joined (n : ℕ) (hn : 0 < n) (x : level n) : Joined x (level n).point := by
      induction x using Quot.inductionOn with | h r
      obtain ⟨q, z, t⟩ := r
      refine ⟨{ toFun := fun s => projection n q z (segment q t (vertex q 0) s)
                continuous_toFun := (projection_continuous n q z).comp (segment q t (vertex q 0)).continuous
                source' := ?_
                target' := ?_ }⟩
      · rw [segment_zero]
      · rw [segment_one, projection_vertex_pos n q hn]
    have pi0_vanish (n : ℕ) (hn : 0 < n) :
        Subsingleton (HomotopyGroup (Fin 0) (level n) (level n).point) := by
      letI : PathConnectedSpace (level n) :=
        ⟨⟨(level n).point⟩, fun x y => (point_joined n hn x).trans (point_joined n hn y).symm⟩
      constructor
      intro a b
      apply (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) (level n).point).injective
      exact Subsingleton.elim _ _
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    let componentValue : C(level 0, ZMod 2) := by
      let f : Raw 0 → ZMod 2 := fun x => x.2.1.1 ⟨fun _ => 0, monotone_const⟩
      have hf : ∀ x y, relation 0 x y → f x = f y := by
        intro x y h
        rcases h with h | ⟨hx, hy⟩
        · obtain ⟨p, q, a, ha, z, t, rfl, rfl⟩ := h
          change (pull a z).1 _ = z.1 _
          rw [k0_constant q z]
        · dsimp only [f]
          rw [hx, hy]
      exact ⟨Quot.lift f hf, continuous_quot_lift hf
        (continuous_sigma (fun q => continuous_sigma (fun z => by
          change Continuous (fun _ : Simplex q => z.1 ⟨fun _ => 0, monotone_const⟩)
          exact continuous_const)))⟩
    have componentValue_projection (q : ℕ) (z : K 0 q) (t : Simplex q) :
        componentValue (projection 0 q z t) = z.1 ⟨fun _ => 0, monotone_const⟩ := rfl
    have componentValue_point : componentValue (level 0).point = 0 := rfl
    have componentValue_path {x y : level 0} (p : Path x y) :
        componentValue x = componentValue y := by
      have h : componentValue (p 0) = componentValue (p 1) :=
        PreconnectedSpace.constant (inferInstance : PreconnectedSpace I)
          (componentValue.continuous.comp p.continuous)
      simpa only [p.source, p.target] using h
    let componentVertex (a : ZMod 2) : level 0 := projection 0 0 (constant 0 a) (vertex 0 0)
    have componentValue_vertex (a : ZMod 2) : componentValue (componentVertex a) = a := rfl
    have component_joined (x : level 0) : Joined x (componentVertex (componentValue x)) := by
      induction x using Quot.inductionOn with | h r
      obtain ⟨q, z, t⟩ := r
      refine ⟨{ toFun := fun s => projection 0 q z (segment q t (vertex q 0) s)
                continuous_toFun := (projection_continuous 0 q z).comp (segment q t (vertex q 0)).continuous
                source' := ?_
                target' := ?_ }⟩
      · rw [segment_zero]
      · rw [segment_one, projection_vertex]
        change projection 0 0 (pull ⟨fun _ => 0, monotone_const⟩ z) (vertex 0 0) =
          projection 0 0 (constant 0 (z.1 ⟨fun _ => 0, monotone_const⟩)) (vertex 0 0)
        rw [k0_constant q z]
    let componentClass : ZerothHomotopy (level 0) → ZMod 2 :=
      ZerothHomotopy.lift componentValue (fun {_ _} p => componentValue_path p)
    have componentClass_bijective : Function.Bijective componentClass := by
      constructor
      · intro a b hab
        obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective a
        obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective b
        change componentValue x = componentValue y at hab
        apply Quotient.sound
        exact (component_joined x).trans (hab ▸ (component_joined y).symm)
      · intro a
        exact ⟨ZerothHomotopy.mk (componentVertex a), rfl⟩
    let pi0Coordinates : HomotopyGroup (Fin 0) (level 0) (level 0).point ≃ ZMod 2 :=
      (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) (level 0).point).trans
        (Equiv.ofBijective componentClass componentClass_bijective)
    have pi0Coordinates_zero : pi0Coordinates ⟦GenLoop.const⟧ = 0 := rfl
    -- T10: one ambient simplex for all staircase pieces, with interleaved vertices.
    let prismDim (q : ℕ) := 2 * q + 1
    let prismVertex (q : ℕ) : Fin (q + 1) × Fin 2 ≃ Fin (prismDim q + 1) := {
      toFun := fun x => ⟨2 * x.1.val + x.2.val, by
        have hi := x.1.isLt
        have he := x.2.isLt
        dsimp [prismDim]
        omega⟩
      invFun := fun k =>
        (⟨k.val / 2, by have hk := k.isLt; dsimp [prismDim] at hk; omega⟩,
         ⟨k.val % 2, by omega⟩)
      left_inv := by
        rintro ⟨i, e⟩
        apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
      right_inv := by
        intro k
        apply Fin.ext
        dsimp
        omega }
    let prismSpace (q : ℕ) : Fin (prismDim q + 1) →o Fin (q + 1) :=
      ⟨fun k => ((prismVertex q).symm k).1, by
        intro i j hij
        change i.val ≤ j.val at hij
        change i.val / 2 ≤ j.val / 2
        omega⟩
    let prismTime (q : ℕ) : Fin (prismDim q + 1) → ZMod 2 :=
      fun k => (((prismVertex q).symm k).2.val : ZMod 2)
    let cupLabel (n q : ℕ) (z : K n q) (t : Fin (q + 1) → ZMod 2) : K (n + 1) q :=
      ⟨cup n q z t, cup_normalized n q z t, cup_closed n q z t⟩
    have cupLabel_natural {n p q : ℕ} (a : Fin (p + 1) →o Fin (q + 1))
        (z : K n q) (t : Fin (q + 1) → ZMod 2) :
        pull a (cupLabel n q z t) = cupLabel n p (pull a z) (fun i => t (a i)) := by
      apply Subtype.ext
      funext s
      rfl
    have cupLabel_zero (n q : ℕ) (t : Fin (q + 1) → ZMod 2) :
        cupLabel n q (zero n q) t = zero (n + 1) q := by
      apply Subtype.ext
      funext s
      exact zero_mul _
    have cupLabel_constant (n q : ℕ) (z : K n q) (c : ZMod 2) :
        cupLabel n q z (fun _ => c) = zero (n + 1) q := by
      apply Subtype.ext
      funext s
      change _ * (c + c) = 0
      rw [CharTwo.add_self_eq_zero, mul_zero]
    let prismLabel (n q : ℕ) (z : K n q) : K (n + 1) (prismDim q) :=
      cupLabel n (prismDim q) (pull (prismSpace q) z) (prismTime q)
    let tail (q : ℕ) (u : Simplex q) (i : Fin (q + 1)) : ℝ :=
      ∑ k, if i ≤ k then u.1 k else 0
    have tail_bounds (q : ℕ) (u : Simplex q) (i : Fin (q + 1)) :
        u.1 i ≤ tail q u i ∧ tail q u i ≤ 1 := by
      constructor
      · have h := Finset.single_le_sum (s := Finset.univ)
          (f := fun k => if i ≤ k then u.1 k else 0)
          (fun k _ => by split_ifs; exact u.2.1 k; exact le_rfl) (Finset.mem_univ i)
        simpa only [le_refl, ↓reduceIte] using h
      · calc
          tail q u i ≤ ∑ k, u.1 k := Finset.sum_le_sum (fun k _ => by
            split_ifs; exact le_rfl; exact u.2.1 k)
          _ = 1 := u.2.2
    have tail_continuous (q : ℕ) (i : Fin (q + 1)) : Continuous (fun u : Simplex q => tail q u i) := by
      apply continuous_finsetSum
      intro k _
      split_ifs
      · exact (continuous_apply k).comp continuous_subtype_val
      · exact continuous_const
    have tail_face {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (u : Simplex p) (i : Fin (p + 1)) :
        tail q (simplexMap a.toOrderHom u) (a i) = tail p u i := by
      dsimp only [tail]
      symm
      refine Fintype.sum_of_injective a a.injective _ _ ?_ ?_
      · intro j hj
        rw [simplexMap_apply_outside a u j hj]
        split_ifs <;> rfl
      · intro j
        simp only [simplexMap_apply_image a u j, a.le_iff_le]
    let bottomWeight (q : ℕ) (u : Simplex q) (t : I) (i : Fin (q + 1)) : ℝ :=
      min (u.1 i) (max 0 (tail q u i - (t : ℝ)))
    have bottomWeight_bounds (q : ℕ) (u : Simplex q) (t : I) (i : Fin (q + 1)) :
        0 ≤ bottomWeight q u t i ∧ bottomWeight q u t i ≤ u.1 i :=
      ⟨le_min (u.2.1 i) (le_max_left _ _), min_le_left _ _⟩
    let prismWeights (q : ℕ) (u : Simplex q) (t : I) : Simplex (prismDim q) :=
      ⟨fun k => let v := (prismVertex q).symm k
        if v.2 = 0 then bottomWeight q u t v.1 else u.1 v.1 - bottomWeight q u t v.1, by
        constructor
        · intro k
          dsimp only
          split_ifs
          · exact (bottomWeight_bounds q u t _).1
          · exact sub_nonneg.mpr (bottomWeight_bounds q u t _).2
        · rw [← (prismVertex q).sum_comp]
          simp only [Equiv.symm_apply_apply]
          rw [Fintype.sum_prod_type]
          simp only [Fin.sum_univ_two, show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte]
          convert u.2.2 using 1
          apply Finset.sum_congr rfl
          intro i _
          ring⟩
    have prismWeights_continuous (q : ℕ) :
        Continuous (fun v : Simplex q × I => prismWeights q v.1 v.2) := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro k
      dsimp only [prismWeights]
      split_ifs
      · exact (((continuous_apply _).comp continuous_subtype_val).comp continuous_fst).min
          (continuous_const.max (((tail_continuous q _).comp continuous_fst).sub
            (continuous_subtype_val.comp continuous_snd)))
      · exact (((continuous_apply _).comp continuous_subtype_val).comp continuous_fst).sub
          ((((continuous_apply _).comp continuous_subtype_val).comp continuous_fst).min
            (continuous_const.max (((tail_continuous q _).comp continuous_fst).sub
              (continuous_subtype_val.comp continuous_snd))))
    let doubledFace {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) :
        Fin (prismDim p + 1) ↪o Fin (prismDim q + 1) :=
      OrderEmbedding.ofStrictMono (fun k => prismVertex q
        (a ((prismVertex p).symm k).1, ((prismVertex p).symm k).2)) (by
        intro i j hij
        have hij' : i.val < j.val := hij
        have hdiv : i.val / 2 ≤ j.val / 2 := by omega
        by_cases he : ((prismVertex p).symm i).1 = ((prismVertex p).symm j).1
        · have he' : i.val / 2 = j.val / 2 := congrArg Fin.val he
          change 2 * (a _).val + i.val % 2 < 2 * (a _).val + j.val % 2
          rw [he]
          omega
        · have hl : ((prismVertex p).symm i).1 < ((prismVertex p).symm j).1 := by
            change i.val / 2 < j.val / 2
            have hn : i.val / 2 ≠ j.val / 2 := by
              intro h
              exact he (Fin.ext h)
            omega
          have ha := a.strictMono hl
          change (a _).val < (a _).val at ha
          change 2 * (a _).val + i.val % 2 < 2 * (a _).val + j.val % 2
          omega)
    have doubledFace_pair {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (i : Fin (p + 1)) (e : Fin 2) :
        doubledFace a (prismVertex p (i, e)) = prismVertex q (a i, e) := by
      change prismVertex q (a ((prismVertex p).symm (prismVertex p (i, e))).1,
        ((prismVertex p).symm (prismVertex p (i, e))).2) = _
      rw [(prismVertex p).symm_apply_apply]
    have doubledFace_space {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) :
        (prismSpace q).comp (doubledFace a).toOrderHom =
          a.toOrderHom.comp (prismSpace p) := by
      apply OrderHom.ext
      funext i
      change ((prismVertex q).symm (prismVertex q
        (a ((prismVertex p).symm i).1, ((prismVertex p).symm i).2))).1 = _
      rw [(prismVertex q).symm_apply_apply]
      rfl
    have doubledFace_time {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) :
        (fun i => prismTime q ((doubledFace a).toOrderHom i)) = prismTime p := by
      funext i
      change (((prismVertex q).symm (prismVertex q
        (a ((prismVertex p).symm i).1, ((prismVertex p).symm i).2))).2.val : ZMod 2) = _
      rw [(prismVertex q).symm_apply_apply]
    have prismLabel_face {n p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) (z : K n q) :
        pull (doubledFace a).toOrderHom (prismLabel n q z) =
          prismLabel n p (pull a.toOrderHom z) := by
      dsimp only [prismLabel]
      rw [cupLabel_natural, pull_comp, doubledFace_space, doubledFace_time, ← pull_comp]
    have prismWeights_pair (q : ℕ) (u : Simplex q) (t : I)
        (i : Fin (q + 1)) (e : Fin 2) :
        (prismWeights q u t).1 (prismVertex q (i, e)) =
          if e = 0 then bottomWeight q u t i else u.1 i - bottomWeight q u t i := by
      change (if ((prismVertex q).symm (prismVertex q (i, e))).2 = 0 then _ else _) = _
      rw [(prismVertex q).symm_apply_apply]
    have prismWeights_face {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (u : Simplex p) (t : I) :
        prismWeights q (simplexMap a.toOrderHom u) t =
          simplexMap (doubledFace a).toOrderHom (prismWeights p u t) := by
      apply Subtype.ext
      funext k
      obtain ⟨⟨i, e⟩, rfl⟩ := (prismVertex q).surjective k
      by_cases hi : i ∈ Set.range a
      · obtain ⟨j, rfl⟩ := hi
        rw [← doubledFace_pair a j e, simplexMap_apply_image]
        rw [doubledFace_pair, prismWeights_pair, prismWeights_pair]
        dsimp only [bottomWeight]
        rw [simplexMap_apply_image, tail_face]
      · have hn : prismVertex q (i, e) ∉ Set.range (doubledFace a) := by
          rintro ⟨j, hj⟩
          have he := congrArg (fun k => ((prismVertex q).symm k).1) hj
          change ((prismVertex q).symm (prismVertex q
            (a ((prismVertex p).symm j).1, ((prismVertex p).symm j).2))).1 = _ at he
          rw [(prismVertex q).symm_apply_apply, (prismVertex q).symm_apply_apply] at he
          exact hi ⟨((prismVertex p).symm j).1, he⟩
        rw [simplexMap_apply_outside (doubledFace a) _ _ hn, prismWeights_pair]
        have hz : bottomWeight q (simplexMap a.toOrderHom u) t i = 0 := by
          apply le_antisymm
          · exact (bottomWeight_bounds q _ t i).2.trans_eq (simplexMap_apply_outside a u i hi)
          · exact (bottomWeight_bounds q _ t i).1
        rw [hz, simplexMap_apply_outside a u i hi]
        split_ifs <;> ring
    let prismEnd (q : ℕ) (e : Fin 2) : Fin (q + 1) ↪o Fin (prismDim q + 1) :=
      OrderEmbedding.ofStrictMono (fun i => prismVertex q (i, e)) (by
        intro i j hij
        change i.val < j.val at hij
        change 2 * i.val + e.val < 2 * j.val + e.val
        omega)
    have prismEnd_space (q : ℕ) (e : Fin 2) :
        (prismSpace q).comp (prismEnd q e).toOrderHom = OrderHom.id := by
      apply OrderHom.ext
      funext i
      change ((prismVertex q).symm (prismVertex q (i, e))).1 = i
      rw [(prismVertex q).symm_apply_apply]
    have prismEnd_time (q : ℕ) (e : Fin 2) :
        (fun i => prismTime q ((prismEnd q e).toOrderHom i)) = fun _ => (e.val : ZMod 2) := by
      funext i
      change (((prismVertex q).symm (prismVertex q (i, e))).2.val : ZMod 2) = _
      rw [(prismVertex q).symm_apply_apply]
    have prismLabel_end (n q : ℕ) (z : K n q) (e : Fin 2) :
        pull (prismEnd q e).toOrderHom (prismLabel n q z) = zero (n + 1) q := by
      dsimp only [prismLabel]
      rw [cupLabel_natural, pull_comp, prismEnd_space, prismEnd_time, pull_id, cupLabel_constant]
    have simplexMap_prismEnd (q : ℕ) (e : Fin 2) (u : Simplex q)
        (i : Fin (q + 1)) (d : Fin 2) :
        (simplexMap (prismEnd q e).toOrderHom u).1 (prismVertex q (i, d)) =
          if d = e then u.1 i else 0 := by
      by_cases hd : d = e
      · subst d
        exact (simplexMap_apply_image (prismEnd q e) u i).trans (if_pos rfl).symm
      · rw [if_neg hd]
        apply simplexMap_apply_outside
        rintro ⟨j, hj⟩
        have hh : (j, e) = (i, d) := (prismVertex q).injective hj
        exact hd (congrArg Prod.snd hh).symm
    have bottomWeight_zero (q : ℕ) (u : Simplex q) (i : Fin (q + 1)) :
        bottomWeight q u 0 i = u.1 i := by
      dsimp only [bottomWeight]
      change min (u.1 i) (max 0 (tail q u i - 0)) = _
      rw [sub_zero, max_eq_right ((u.2.1 i).trans (tail_bounds q u i).1),
        min_eq_left (tail_bounds q u i).1]
    have bottomWeight_one (q : ℕ) (u : Simplex q) (i : Fin (q + 1)) :
        bottomWeight q u 1 i = 0 := by
      dsimp only [bottomWeight]
      change min (u.1 i) (max 0 (tail q u i - 1)) = _
      rw [max_eq_left (sub_nonpos.mpr (tail_bounds q u i).2), min_eq_right (u.2.1 i)]
    have prismWeights_zero (q : ℕ) (u : Simplex q) :
        prismWeights q u 0 = simplexMap (prismEnd q 0).toOrderHom u := by
      apply Subtype.ext
      funext k
      obtain ⟨⟨i, e⟩, rfl⟩ := (prismVertex q).surjective k
      rw [prismWeights_pair, bottomWeight_zero, simplexMap_prismEnd]
      split_ifs <;> simp only [sub_self]
    have prismWeights_one (q : ℕ) (u : Simplex q) :
        prismWeights q u 1 = simplexMap (prismEnd q 1).toOrderHom u := by
      apply Subtype.ext
      funext k
      obtain ⟨⟨i, e⟩, rfl⟩ := (prismVertex q).surjective k
      rw [prismWeights_pair, bottomWeight_one, simplexMap_prismEnd]
      fin_cases e <;> simp
    let rawBond (n : ℕ) (x : Raw n) (t : I) : level (n + 1) :=
      projection (n + 1) (prismDim x.1) (prismLabel n x.1 x.2.1) (prismWeights x.1 x.2.2 t)
    have rawBond_zero_label (n q : ℕ) (u : Simplex q) (t : I) :
        rawBond n ⟨q, zero n q, u⟩ t = (level (n + 1)).point := by
      dsimp only [rawBond, prismLabel]
      rw [pull_zero, cupLabel_zero, projection_zero]
    have rawBond_zero_time (n : ℕ) (x : Raw n) :
        rawBond n x 0 = (level (n + 1)).point := by
      obtain ⟨q, z, u⟩ := x
      dsimp only [rawBond]
      rw [prismWeights_zero, ← projection_face (prismEnd q 0).toOrderHom (prismEnd q 0).injective,
        prismLabel_end, projection_zero]
    have rawBond_one_time (n : ℕ) (x : Raw n) :
        rawBond n x 1 = (level (n + 1)).point := by
      obtain ⟨q, z, u⟩ := x
      dsimp only [rawBond]
      rw [prismWeights_one, ← projection_face (prismEnd q 1).toOrderHom (prismEnd q 1).injective,
        prismLabel_end, projection_zero]
    have rawBond_face (n : ℕ) (x y : Raw n) (h : relation n x y) : rawBond n x = rawBond n y := by
      funext t
      rcases h with h | ⟨hx, hy⟩
      · obtain ⟨p, q, a, ha, z, u, rfl, rfl⟩ := h
        let a' := OrderEmbedding.ofStrictMono a ((a.monotone.strictMono_iff_injective).2 ha)
        change projection (n + 1) (prismDim p) (prismLabel n p (pull a'.toOrderHom z))
            (prismWeights p u t) =
          projection (n + 1) (prismDim q) (prismLabel n q z) (prismWeights q (simplexMap a'.toOrderHom u) t)
        rw [prismWeights_face, ← projection_face (doubledFace a').toOrderHom (doubledFace a').injective,
          prismLabel_face]
      · dsimp only [rawBond, prismLabel]
        rw [hx, hy, pull_zero, pull_zero, cupLabel_zero, cupLabel_zero, projection_zero, projection_zero]
    have rawBond_continuous (n : ℕ) :
        Continuous (fun p : Raw n × I => rawBond n p.1 p.2) := by
      let e : Raw n × I ≃ₜ Σ q : ℕ, (Σ z : K n q, Simplex q) × I :=
        Homeomorph.sigmaProdDistrib
      apply e.symm.isQuotientMap.continuous_iff.mpr
      apply continuous_sigma
      intro q
      let e' : (Σ z : K n q, Simplex q) × I ≃ₜ Σ z : K n q, Simplex q × I :=
        Homeomorph.sigmaProdDistrib
      apply e'.symm.isQuotientMap.continuous_iff.mpr
      apply continuous_sigma
      intro z
      exact (projection_continuous (n + 1) (prismDim q) (prismLabel n q z)).comp
        (prismWeights_continuous q)
    let bonding (n : ℕ) : C(level n × I, level (n + 1)) :=
      ⟨fun p => Quot.lift (rawBond n) (rawBond_face n) p.1 p.2, by
        exact (isQuotientMap_quot_mk (r := relation n)).continuous_lift_prod_left
          (rawBond_continuous n)⟩
    have bonding_projection (n q : ℕ) (z : K n q) (u : Simplex q) (t : I) :
        bonding n (projection n q z u, t) = rawBond n ⟨q, z, u⟩ t := rfl
    have bonding_point (n : ℕ) (t : I) :
        bonding n ((level n).point, t) = (level (n + 1)).point :=
      rawBond_zero_label n 0 (vertex 0 0) t
    have bonding_zero (n : ℕ) (x : level n) :
        bonding n (x, 0) = (level (n + 1)).point := by
      induction x using Quot.inductionOn with | h r
      exact rawBond_zero_time n r
    have bonding_one (n : ℕ) (x : level n) :
        bonding n (x, 1) = (level (n + 1)).point := by
      induction x using Quot.inductionOn with | h r
      exact rawBond_one_time n r
    let cocycleSpectrum : Prespectrum.{0} := {
      level := level
      bond := bonding
      bond_point := bonding_point
      bond_zero := bonding_zero
      bond_one := bonding_one }
    -- A6 and C3: evaluation on the staircase fundamental chain.
    let stairTime (q : ℕ) (j : Fin (q + 1)) : Fin (q + 2) →o Fin 2 :=
      ⟨fun k => ⟨if k.val ≤ j.val then 0 else 1, by split_ifs <;> omega⟩, by
        intro k l hkl
        change k.val ≤ l.val at hkl
        change (if k.val ≤ j.val then 0 else 1) ≤ (if l.val ≤ j.val then 0 else 1)
        split_ifs <;> omega⟩
    let stairFace (q : ℕ) (j : Fin (q + 1)) :
        Fin (q + 2) ↪o Fin (prismDim q + 1) :=
      OrderEmbedding.ofStrictMono
        (fun k => prismVertex q (j.predAbove k, stairTime q j k)) (by
          intro k l hkl
          change k.val < l.val at hkl
          change 2 * (j.predAbove k).val + (if k.val ≤ j.val then 0 else 1) <
            2 * (j.predAbove l).val + (if l.val ≤ j.val then 0 else 1)
          simp only [Fin.predAbove, Fin.lt_def, Fin.val_castSucc,
            apply_dite Fin.val, Fin.val_pred, Fin.coe_castPred, dite_eq_ite]
          split_ifs <;> omega)
    have stair_space (q : ℕ) (j : Fin (q + 1)) :
        (prismSpace q).comp (stairFace q j).toOrderHom = Fin.predAboveOrderHom j := by
      apply OrderHom.ext
      funext k
      change ((prismVertex q).symm (prismVertex q (j.predAbove k, stairTime q j k))).1 = j.predAbove k
      rw [(prismVertex q).symm_apply_apply]
    have stair_time (q : ℕ) (j : Fin (q + 1)) (k : Fin (q + 2)) :
        prismTime q (stairFace q j k) = ((stairTime q j k).val : ZMod 2) := by
      change (((prismVertex q).symm (prismVertex q (j.predAbove k, stairTime q j k))).2.val : ZMod 2) = _
      rw [(prismVertex q).symm_apply_apply]
    have stair_time_last (q : ℕ) (j : Fin (q + 1)) :
        stairTime q j (Fin.last (q + 1)) = 1 := by
      apply Fin.ext
      change (if q + 1 ≤ j.val then 0 else 1) = 1
      have hj := j.isLt
      rw [if_neg (by omega)]
    have stair_time_penultimate (q : ℕ) (j : Fin (q + 1)) :
        stairTime q j (Fin.last q).castSucc = if j = Fin.last q then 0 else 1 := by
      by_cases hj : j = Fin.last q
      · subst j
        apply Fin.ext
        simp [stairTime]
      · rw [if_neg hj]
        apply Fin.ext
        change (if q ≤ j.val then 0 else 1) = 1
        have hjbound := j.isLt
        have hjne : j.val ≠ q := by
          intro he
          apply hj
          exact Fin.ext he
        rw [if_neg (by omega)]
    have prismLabel_stair (n q : ℕ) (z : K n q) (j : Fin (q + 1)) :
        pull (stairFace q j).toOrderHom (prismLabel n q z) =
          bondLabel n (q + 1) (pull (Fin.predAboveOrderHom j) z) (stairTime q j) := by
      dsimp only [prismLabel]
      rw [cupLabel_natural, pull_comp, stair_space]
      apply Subtype.ext
      funext s
      change _ * (prismTime q (stairFace q j (s (Fin.last (n + 1)))) +
        prismTime q (stairFace q j (s (Fin.last n).castSucc))) = _
      rw [stair_time, stair_time]
    have prismLabel_top (n : ℕ) (z : K n n) (j : Fin (n + 1)) :
        (prismLabel n n z).1 (stairFace n j).toOrderHom =
          if j = Fin.last n then z.1 OrderHom.id else 0 := by
      have hfront : (prismSpace n).comp
          ((stairFace n j).toOrderHom.comp Fin.castSuccOrderEmb.toOrderHom) =
          (Fin.predAboveOrderHom j).comp Fin.castSuccOrderEmb.toOrderHom :=
        congrArg (fun a : Fin (n + 2) →o Fin (n + 1) =>
          a.comp Fin.castSuccOrderEmb.toOrderHom) (stair_space n j)
      change z.1 ((prismSpace n).comp
          ((stairFace n j).toOrderHom.comp Fin.castSuccOrderEmb.toOrderHom)) *
          (prismTime n (stairFace n j (Fin.last (n + 1))) +
            prismTime n (stairFace n j (Fin.last n).castSucc)) = _
      rw [hfront, stair_time, stair_time, stair_time_last, stair_time_penultimate]
      by_cases hj : j = Fin.last n
      · subst j
        have hf : (Fin.predAboveOrderHom (Fin.last n)).comp
            Fin.castSuccOrderEmb.toOrderHom = OrderHom.id := by
          apply OrderHom.ext
          funext i
          exact Fin.predAbove_last_castSucc
        rw [hf]
        norm_num
      · simp only [if_neg hj]
        change _ * ((1 : ZMod 2) + 1) = 0
        rw [CharTwo.add_self_eq_zero, mul_zero]
    have prismLabel_sum (n : ℕ) (z : K n n) :
        ∑ j : Fin (n + 1), (prismLabel n n z).1 (stairFace n j).toOrderHom = z.1 OrderHom.id := by
      simp_rw [prismLabel_top]
      simp
    have tail_gap (q : ℕ) (u : Simplex q) (i j : Fin (q + 1)) (hij : i < j) :
        u.1 i + tail q u j ≤ tail q u i := by
      have h : (∑ k : Fin (q + 1),
          ((if k = i then u.1 k else 0) + (if j ≤ k then u.1 k else 0))) ≤ tail q u i := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : k = i
        · subst k
          simp only [↓reduceIte, not_le.mpr hij, le_refl, add_zero]
        · simp only [if_neg hk, zero_add]
          by_cases hj : j ≤ k
          · simp only [hj, hij.le.trans hj, ↓reduceIte, le_refl]
          · simp only [if_neg hj]
            split_ifs
            · exact u.2.1 k
            · exact le_rfl
      simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, tail] using h
    have bottomWeight_stair (q : ℕ) (u : Simplex q) (t : I) (j : Fin (q + 1))
        (ht : tail q u j - u.1 j ≤ (t : ℝ) ∧ (t : ℝ) ≤ tail q u j) :
        (∀ i < j, bottomWeight q u t i = u.1 i) ∧
        bottomWeight q u t j = tail q u j - (t : ℝ) ∧
        (∀ i, j < i → bottomWeight q u t i = 0) := by
      refine ⟨?_, ?_, ?_⟩
      · intro i hij
        dsimp only [bottomWeight]
        apply min_eq_left
        have h := tail_gap q u i j hij
        exact (by linarith : u.1 i ≤ tail q u i - (t : ℝ)).trans (le_max_right _ _)
      · dsimp only [bottomWeight]
        rw [max_eq_right (sub_nonneg.mpr ht.2)]
        exact min_eq_right (by linarith [ht.1])
      · intro i hij
        dsimp only [bottomWeight]
        have h := tail_gap q u j i hij
        rw [max_eq_left (by linarith [ht.1]), min_eq_right (u.2.1 i)]
    have stairFace_bottom (q : ℕ) (j i : Fin (q + 1)) (hi : i ≤ j) :
        stairFace q j i.castSucc = prismVertex q (i, 0) := by
      change prismVertex q (j.predAbove i.castSucc, stairTime q j i.castSucc) = _
      rw [Fin.predAbove_castSucc_of_le j i hi]
      have ht : stairTime q j i.castSucc = 0 := by
        apply Fin.ext
        change (if i.val ≤ j.val then 0 else 1) = 0
        exact if_pos hi
      rw [ht]
    have stairFace_top (q : ℕ) (j i : Fin (q + 1)) (hi : j ≤ i) :
        stairFace q j i.succ = prismVertex q (i, 1) := by
      change prismVertex q (j.predAbove i.succ, stairTime q j i.succ) = _
      rw [Fin.predAbove_succ_of_le j i hi]
      have ht : stairTime q j i.succ = 1 := by
        apply Fin.ext
        change (if i.val + 1 ≤ j.val then 0 else 1) = 1
        exact if_neg (by change j.val ≤ i.val at hi; omega)
      rw [ht]
    have prismWeights_stair_support (q : ℕ) (u : Simplex q) (t : I)
        (j : Fin (q + 1)) (ht : tail q u j - u.1 j ≤ (t : ℝ) ∧ (t : ℝ) ≤ tail q u j)
        (k : Fin (prismDim q + 1)) (hk : k ∉ Set.range (stairFace q j)) :
        (prismWeights q u t).1 k = 0 := by
      obtain ⟨⟨i, e⟩, rfl⟩ := (prismVertex q).surjective k
      rw [prismWeights_pair]
      by_cases he : e = 0
      · rw [if_pos he]
        have hi : j < i := by
          by_contra h
          have hij : i ≤ j := le_of_not_gt h
          apply hk
          exact ⟨i.castSucc, (stairFace_bottom q j i hij).trans (congrArg (fun e => prismVertex q (i, e)) he.symm)⟩
        exact (bottomWeight_stair q u t j ht).2.2 i hi
      · rw [if_neg he]
        have he1 : e = 1 := by
          apply Fin.ext
          have h := e.isLt
          have hn : e.val ≠ 0 := by simpa using he
          change e.val = 1
          omega
        have hi : i < j := by
          by_contra h
          have hji : j ≤ i := le_of_not_gt h
          apply hk
          exact ⟨i.succ, (stairFace_top q j i hji).trans (congrArg (fun e => prismVertex q (i, e)) he1.symm)⟩
        rw [(bottomWeight_stair q u t j ht).1 i hi, sub_self]
    have prism_stair_factor (q : ℕ) (u : Simplex q) (t : I) (j : Fin (q + 1))
        (ht : tail q u j - u.1 j ≤ (t : ℝ) ∧ (t : ℝ) ≤ tail q u j) :
        ∃ v : Simplex (q + 1),
          (∀ k, v.1 k = (prismWeights q u t).1 (stairFace q j k)) ∧
          simplexMap (stairFace q j).toOrderHom v = prismWeights q u t := by
      let v : Simplex (q + 1) := ⟨fun k => (prismWeights q u t).1 (stairFace q j k), by
        constructor
        · intro k
          exact (prismWeights q u t).2.1 _
        · calc
            _ = ∑ k, (prismWeights q u t).1 k :=
              Fintype.sum_of_injective (stairFace q j) (stairFace q j).injective _ _
                (fun k hk => prismWeights_stair_support q u t j ht k hk) (fun _ => rfl)
            _ = 1 := (prismWeights q u t).2.2⟩
      refine ⟨v, fun _ => rfl, ?_⟩
      apply Subtype.ext
      funext k
      by_cases hk : k ∈ Set.range (stairFace q j)
      · obtain ⟨l, rfl⟩ := hk
        exact simplexMap_apply_image (stairFace q j) v l
      · rw [simplexMap_apply_outside (stairFace q j) v k hk,
          prismWeights_stair_support q u t j ht k hk]
    have bonding_stair (n q : ℕ) (z : K n q) (u : Simplex q) (t : I)
        (j : Fin (q + 1)) (ht : tail q u j - u.1 j ≤ (t : ℝ) ∧ (t : ℝ) ≤ tail q u j) :
        ∃ v : Simplex (q + 1),
          bonding n (projection n q z u, t) =
            projection (n + 1) (q + 1)
              (bondLabel n (q + 1) (pull (Fin.predAboveOrderHom j) z) (stairTime q j)) v := by
      obtain ⟨v, hv, he⟩ := prism_stair_factor q u t j ht
      refine ⟨v, ?_⟩
      rw [bonding_projection]
      dsimp only [rawBond]
      rw [← he, ← projection_face (stairFace q j).toOrderHom (stairFace q j).injective,
        prismLabel_stair]
    have tail_zero (q : ℕ) (u : Simplex q) : tail q u 0 = 1 := by
      dsimp only [tail]
      simpa only [Fin.zero_le, ↓reduceIte] using u.2.2
    have tail_last (q : ℕ) (u : Simplex q) : tail q u (Fin.last q) = u.1 (Fin.last q) := by
      dsimp only [tail]
      rw [Finset.sum_eq_single (Fin.last q)]
      · simp
      · intro k _ hk
        exact if_neg (by intro h; apply hk; exact le_antisymm (Fin.le_last _) h)
      · simp
    have tail_succ (q : ℕ) (u : Simplex q) (i : Fin q) :
        tail q u i.castSucc = u.1 i.castSucc + tail q u i.succ := by
      have h : tail q u i.castSucc = ∑ k : Fin (q + 1),
          ((if k = i.castSucc then u.1 k else 0) + (if i.succ ≤ k then u.1 k else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = i.castSucc
        · subst k
          simp only [le_refl, ↓reduceIte, not_le.mpr i.castSucc_lt_succ, add_zero]
        · have he : i.castSucc ≤ k ↔ i.succ ≤ k := by
            change i.val ≤ k.val ↔ i.val + 1 ≤ k.val
            have hn : k.val ≠ i.val := by intro h; exact hk (Fin.ext h)
            omega
          simp only [if_neg hk, zero_add, he]
      simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, tail] using h
    have prism_stair_cover (q : ℕ) (u : Simplex q) (t : I) :
        ∃ j : Fin (q + 1), tail q u j - u.1 j ≤ (t : ℝ) ∧ (t : ℝ) ≤ tail q u j := by
      let S : Finset (Fin (q + 1)) := Finset.univ.filter (fun j => (t : ℝ) ≤ tail q u j)
      have hS : S.Nonempty := ⟨0, by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, tail_zero]
        exact t.2.2⟩
      let j := S.max' hS
      have hj : j ∈ S := Finset.max'_mem S hS
      have ht : (t : ℝ) ≤ tail q u j := (Finset.mem_filter.mp hj).2
      refine ⟨j, ?_, ht⟩
      by_cases hjlast : j = Fin.last q
      · rw [hjlast, tail_last, sub_self]
        exact t.2.1
      · obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hjlast
        have hh : ¬ (t : ℝ) ≤ tail q u i.succ := by
          intro h
          have hm : i.succ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
          have hle : i.succ ≤ j := Finset.le_max' S _ hm
          rw [← hi] at hle
          exact not_le.mpr i.castSucc_lt_succ hle
        rw [← hi, tail_succ]
        linarith [lt_of_not_ge hh]
    have bonding_stair_cover (n q : ℕ) (z : K n q) (u : Simplex q) (t : I) :
        ∃ j : Fin (q + 1), ∃ v : Simplex (q + 1),
          bonding n (projection n q z u, t) =
            projection (n + 1) (q + 1)
              (bondLabel n (q + 1) (pull (Fin.predAboveOrderHom j) z) (stairTime q j)) v := by
      obtain ⟨j, ht⟩ := prism_stair_cover q u t
      obtain ⟨v, hv⟩ := bonding_stair n q z u t j ht
      exact ⟨j, v, hv⟩
    -- C4: a pointed bijection from a two-element group preserves the group table.
    have two_element_group_add (G : Type) [Group G] (e : G ≃ ZMod 2) (he : e 1 = 0)
        (a b : G) : e (a * b) = e a + e b := by
      clear * - G e he a b
      have hcases (x : ZMod 2) : x = 0 ∨ x = 1 := by
        fin_cases x
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hone (x : G) (hx : x ≠ 1) : e x = 1 := by
        rcases hcases (e x) with h | h
        · exact False.elim (hx (e.injective (h.trans he.symm)))
        · exact h
      by_cases ha : a = 1
      · subst a
        simp only [one_mul, he, zero_add]
      by_cases hb : b = 1
      · subst b
        simp only [mul_one, he, add_zero]
      have hab : a * b = 1 := by
        by_contra hab
        have h : a * b = a := e.injective ((hone (a * b) hab).trans (hone a ha).symm)
        exact hb (mul_left_cancel (h.trans (mul_one a).symm))
      rw [hab, he, hone a ha, hone b hb, CharTwo.add_self_eq_zero]
    have coordinates_add (n : ℕ)
        (e : HomotopyGroup (Fin (n + 1)) (level (n + 1)) (level (n + 1)).point ≃ ZMod 2)
        (he : e ⟦GenLoop.const⟧ = 0)
        (p q : GenLoop (Fin (n + 1)) (level (n + 1)) (level (n + 1)).point) :
        e ⟦GenLoop.transAt 0 p q⟧ = e ⟦p⟧ + e ⟦q⟧ := by
      rw [← HomotopyGroup.mul_spec (i := (0 : Fin (n + 1))) (p := q) (q := p)]
      rw [two_element_group_add _ e (by rw [HomotopyGroup.one_def]; exact he)]
      exact add_comm _ _
    -- A3: the explicit cone contraction gives a normalized primitive on a simplex.
    let prependZero (n q : ℕ) (a : Fin (n + 1) →o Fin (q + 1)) :
        Fin (n + 2) →o Fin (q + 1) :=
      ⟨Fin.cons 0 a, by
        intro i j hij
        cases i using Fin.cases with
        | zero =>
          change (0 : Fin (q + 1)) ≤ _
          exact Fin.zero_le _
        | succ i =>
          cases j using Fin.cases with
          | zero => exact False.elim ((not_le.mpr (Fin.succ_pos i)) hij)
          | succ j =>
            change a i ≤ a j
            exact a.monotone (Fin.succ_le_succ_iff.mp hij)⟩
    have prependZero_face_zero (n q : ℕ) (a : Fin (n + 1) →o Fin (q + 1)) :
        (prependZero n q a).comp (face n 0) = a := by
      apply OrderHom.ext
      funext k
      change Fin.cons (α := fun _ => Fin (q + 1)) (0 : Fin (q + 1)) a ((0 : Fin (n + 2)).succAbove k) = a k
      rw [Fin.zero_succAbove, Fin.cons_succ]
    have prependZero_face_succ (n q : ℕ) (a : Fin (n + 2) →o Fin (q + 1)) (i : Fin (n + 2)) :
        (prependZero (n + 1) q a).comp (face (n + 1) i.succ) =
          prependZero n q (a.comp (face n i)) := by
      apply OrderHom.ext
      funext k
      cases k using Fin.cases with
      | zero =>
        change Fin.cons (α := fun _ => Fin (q + 1)) (0 : Fin (q + 1)) a (i.succ.succAbove 0) = 0
        rw [Fin.succ_succAbove_zero, Fin.cons_zero]
      | succ k =>
        change Fin.cons (α := fun _ => Fin (q + 1)) (0 : Fin (q + 1)) a (i.succ.succAbove k.succ) =
          Fin.cons (α := fun _ => Fin (q + 1)) (0 : Fin (q + 1)) (a.comp (face n i)) k.succ
        rw [Fin.succ_succAbove_succ, Fin.cons_succ, Fin.cons_succ]
        rfl
    have simplex_cocycle_primitive (n q : ℕ) (z : K (n + 1) q) :
        ∃ b : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2,
          (∀ a : Fin (n + 1) →o Fin (q + 1), ¬ Function.Injective a → b a = 0) ∧ delta n q b = z.1 := by
      let b : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2 := fun a => z.1 (prependZero n q a)
      refine ⟨b, ?_, ?_⟩
      · intro a ha
        change z.1 (prependZero n q a) = 0
        apply z.2.1
        intro hinj
        change Function.Injective (Fin.cons (α := fun _ => Fin (q + 1)) (0 : Fin (q + 1)) a) at hinj
        exact ha (Fin.cons_injective_iff.mp hinj).2
      · funext a
        have hc := z.2.2 (prependZero (n + 1) q a)
        rw [Fin.sum_univ_succ, prependZero_face_zero] at hc
        simp_rw [prependZero_face_succ] at hc
        change z.1 a + delta n q b a = 0 at hc
        exact add_left_cancel (hc.trans (CharTwo.add_self_eq_zero (z.1 a)).symm)
    -- T1, T2, T6: keep the unreduced fat space and its actual zero subspace.
    let fatLevel (n : ℕ) : BasedSpace.{0} := {
      space := TopCat.of (Quot (faceRelation n))
      point := Quot.mk _ ⟨0, zero n 0, vertex 0 0⟩ }
    let fatProjection (n q : ℕ) (z : K n q) (u : Simplex q) : fatLevel n :=
      Quot.mk _ ⟨q, z, u⟩
    have fatProjection_continuous (n q : ℕ) (z : K n q) :
        Continuous (fatProjection n q z) :=
      continuous_quot_mk.comp (continuous_sigmaMk.comp continuous_sigmaMk)
    have fatProjection_face {n p q : ℕ} (a : Fin (p + 1) →o Fin (q + 1))
        (ha : Function.Injective a) (z : K n q) (u : Simplex p) :
        fatProjection n p (pull a z) u = fatProjection n q z (simplexMap a u) :=
      Quot.sound ⟨p, q, a, ha, z, u, rfl, rfl⟩
    let fatMomentMap (n m : ℕ) (label : K n m) (k : Option (Fin (m + 1))) :
        C(fatLevel n, ℝ) := by
      let f : Raw n → ℝ := fun x => moment n m label k x.1 x.2.1 x.2.2
      have hf : ∀ x y, faceRelation n x y → f x = f y := by
        rintro x y ⟨p, q, a, ha, z, u, rfl, rfl⟩
        exact moment_face n m label k
          (OrderEmbedding.ofStrictMono a ((a.monotone.strictMono_iff_injective).2 ha)) z u
      exact ⟨Quot.lift f hf, continuous_quot_lift hf
        (continuous_sigma (fun q => continuous_sigma (fun z =>
          moment_continuous n m label k q z)))⟩
    have fatMomentMap_projection (n m : ℕ) (label : K n m) (k : Option (Fin (m + 1)))
        (q : ℕ) (z : K n q) (u : Simplex q) :
        fatMomentMap n m label k (fatProjection n q z u) = moment n m label k q z u := rfl
    have fat_positive_rep (n : ℕ) (x : fatLevel n) :
        ∃ q, ∃ z : K n q, ∃ u : Simplex q,
          (∀ i, 0 < u.1 i) ∧ fatProjection n q z u = x := by
      induction x using Quot.inductionOn with | h r
      obtain ⟨q, z, u⟩ := r
      obtain ⟨p, a, v, hv, hu⟩ := simplex_support q u
      refine ⟨p, pull a.toOrderHom z, v, hv, ?_⟩
      rw [fatProjection_face a.toOrderHom a.injective, hu]
    have fat_moment_separates (n : ℕ) (x y : fatLevel n)
        (h : ∀ m (label : K n m) k, fatMomentMap n m label k x = fatMomentMap n m label k y) :
        x = y := by
      obtain ⟨p, z, s, hs, rfl⟩ := fat_positive_rep n x
      obtain ⟨q, w, t, ht, rfl⟩ := fat_positive_rep n y
      have hp : 0 < ∏ i, s.1 i := Finset.prod_pos (fun i _ => hs i)
      have hq : 0 < ∏ i, t.1 i := Finset.prod_pos (fun i _ => ht i)
      have hpq : p = q := by
        rcases lt_trichotomy p q with hl | he | hl
        · have hh := h q w none
          simp only [fatMomentMap_projection, moment_lower n q p hl,
            moment_top, ite_true, Option.elim_none, mul_one] at hh
          linarith
        · exact he
        · have hh := h p z none
          simp only [fatMomentMap_projection, moment_top, ite_true,
            moment_lower n p q hl, Option.elim_none, mul_one] at hh
          linarith
      subst q
      have hzw : z = w := by
        by_contra hne
        have hh := h p z none
        simp only [fatMomentMap_projection, moment_top,
          ite_true, if_neg (Ne.symm hne), Option.elim_none, mul_one] at hh
        linarith
      subst w
      have hprod : (∏ i, s.1 i) = ∏ i, t.1 i := by
        have hh := h p z none
        simpa only [fatMomentMap_projection, moment_top, ite_true,
          Option.elim_none, mul_one] using hh
      have hst : s = t := by
        apply Subtype.ext
        funext i
        have hh := h p z (some i)
        simp only [fatMomentMap_projection, moment_top, ite_true, Option.elim_some] at hh
        rw [← hprod] at hh
        exact mul_left_cancel₀ hp.ne' hh
      rw [hst]
    have fat_t2 (n : ℕ) : T2Space (fatLevel n) := by
      constructor
      intro x y hxy
      have hex : ∃ m, ∃ label : K n m, ∃ k,
          fatMomentMap n m label k x ≠ fatMomentMap n m label k y := by
        by_contra hh
        apply hxy
        apply fat_moment_separates n x y
        intro m label k
        by_contra he
        exact hh ⟨m, label, k, he⟩
      obtain ⟨m, label, k, hk⟩ := hex
      exact separated_by_continuous (fatMomentMap n m label k).continuous hk
    let collapse (n : ℕ) : C(fatLevel n, level n) := by
      let f : Raw n → level n := fun x => projection n x.1 x.2.1 x.2.2
      have hf : ∀ x y, faceRelation n x y → f x = f y :=
        fun x y h => Quot.sound (Or.inl h)
      exact ⟨Quot.lift f hf, continuous_quot_lift hf continuous_quot_mk⟩
    have collapse_projection (n q : ℕ) (z : K n q) (u : Simplex q) :
        collapse n (fatProjection n q z u) = projection n q z u := rfl
    let zeroRaw := Σ q : ℕ, Simplex q
    let zeroRelation (x y : zeroRaw) : Prop :=
      ∃ p q, ∃ a : Fin (p + 1) →o Fin (q + 1), Function.Injective a ∧
        ∃ u : Simplex p, x = ⟨p, u⟩ ∧ y = ⟨q, simplexMap a u⟩
    let zeroFat := Quot zeroRelation
    let zeroProjection (q : ℕ) (u : Simplex q) : zeroFat := Quot.mk _ ⟨q, u⟩
    have zeroProjection_continuous (q : ℕ) : Continuous (zeroProjection q) :=
      continuous_quot_mk.comp continuous_sigmaMk
    have zeroProjection_face {p q : ℕ} (a : Fin (p + 1) →o Fin (q + 1))
        (ha : Function.Injective a) (u : Simplex p) :
        zeroProjection p u = zeroProjection q (simplexMap a u) :=
      Quot.sound ⟨p, q, a, ha, u, rfl, rfl⟩
    let zeroIncl (n : ℕ) : C(zeroFat, fatLevel n) := by
      let f : zeroRaw → fatLevel n := fun x => fatProjection n x.1 (zero n x.1) x.2
      have hf : ∀ x y, zeroRelation x y → f x = f y := by
        rintro x y ⟨p, q, a, ha, u, rfl, rfl⟩
        exact (congrArg (fun z => fatProjection n p z u) (pull_zero a)).symm.trans
          (fatProjection_face a ha (zero n q) u)
      exact ⟨Quot.lift f hf, continuous_quot_lift hf
        (continuous_sigma (fun q => fatProjection_continuous n q (zero n q)))⟩
    let forgetLabel (n : ℕ) : C(fatLevel n, zeroFat) := by
      let f : Raw n → zeroFat := fun x => zeroProjection x.1 x.2.2
      have hf : ∀ x y, faceRelation n x y → f x = f y := by
        rintro x y ⟨p, q, a, ha, z, u, rfl, rfl⟩
        exact zeroProjection_face a ha u
      exact ⟨Quot.lift f hf, continuous_quot_lift hf
        (continuous_sigma (fun q => continuous_sigma (fun _ => zeroProjection_continuous q)))⟩
    have zeroIncl_closed (n : ℕ) : IsClosedEmbedding (zeroIncl n) := by
      letI := fat_t2 n
      apply Function.LeftInverse.isClosedEmbedding (f := forgetLabel n)
        (hf := (forgetLabel n).continuous) (hg := (zeroIncl n).continuous)
      intro x
      induction x using Quot.inductionOn with | h r
      rfl
    have collapse_zero (n : ℕ) (x : zeroFat) : collapse n (zeroIncl n x) = (level n).point := by
      induction x using Quot.inductionOn with | h r
      exact projection_zero n r.1 r.2
    have collapse_fiber (n : ℕ) (x : fatLevel n) :
        collapse n x = (level n).point ↔ x ∈ Set.range (zeroIncl n) := by
      constructor
      · intro hx
        obtain ⟨q, z, u, hu, rfl⟩ := fat_positive_rep n x
        have hz : z = zero n q := by
          by_contra hz
          exact positive_not_point n q z hz u hu hx
        subst z
        exact ⟨zeroProjection q u, rfl⟩
      · rintro ⟨y, rfl⟩
        exact collapse_zero n y
    have collapse_isQuotientMap (n : ℕ) : IsQuotientMap (collapse n) := by
      exact (isQuotientMap_quot_mk (r := faceRelation n)).of_comp_isQuotientMap
        (isQuotientMap_quot_mk (r := relation n))
    -- T6: all zero simplices remain present during the contraction.
    let coneSimplex (q : ℕ) (u : Simplex q) (t : I) : Simplex (q + 1) :=
      ⟨Fin.cons (t : ℝ) (fun i => (1 - (t : ℝ)) * u.1 i), by
        constructor
        · intro i
          refine Fin.cases t.2.1 (fun j => ?_) i
          exact mul_nonneg (sub_nonneg.mpr t.2.2) (u.2.1 j)
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← Finset.mul_sum, u.2.2]
          ring⟩
    have coneSimplex_continuous (q : ℕ) :
        Continuous (fun p : Simplex q × I => coneSimplex q p.1 p.2) := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro i
      refine Fin.cases (continuous_subtype_val.comp continuous_snd) (fun j => ?_) i
      exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst))
    let coneFace {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) :
        Fin (p + 2) ↪o Fin (q + 2) :=
      OrderEmbedding.ofStrictMono (Fin.cons 0 (fun i => (a i).succ)) (by
        intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact False.elim ((lt_irrefl _) hij)
          | succ j => exact Fin.succ_pos _
        | succ i =>
          cases j using Fin.cases with
          | zero => exact False.elim (Fin.not_lt_zero _ hij)
          | succ j => exact Fin.succ_lt_succ_iff.mpr (a.strictMono (Fin.succ_lt_succ_iff.mp hij)))
    have coneSimplex_face {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (u : Simplex p) (t : I) :
        coneSimplex q (simplexMap a.toOrderHom u) t =
          simplexMap (coneFace a).toOrderHom (coneSimplex p u t) := by
      apply Subtype.ext
      funext i
      cases i using Fin.cases with
      | zero =>
        change (t : ℝ) = ∑ j, if coneFace a j = 0 then (coneSimplex p u t).1 j else 0
        rw [Fin.sum_univ_succ]
        simp [coneFace, coneSimplex]
      | succ i =>
        change (1 - (t : ℝ)) * (∑ j, if a j = i then u.1 j else 0) =
          ∑ j, if coneFace a j = i.succ then (coneSimplex p u t).1 j else 0
        conv_rhs => rw [Fin.sum_univ_succ]
        simp only [coneFace, OrderEmbedding.coe_ofStrictMono, Fin.cons_zero,
          Fin.cons_succ, Ne.symm (Fin.succ_ne_zero i), ↓reduceIte, zero_add, Fin.succ_inj, coneSimplex]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
    have coneSimplex_zero (q : ℕ) (u : Simplex q) :
        coneSimplex q u 0 = simplexMap (Fin.succOrderEmb (q + 1)).toOrderHom u := by
      apply Subtype.ext
      funext i
      cases i using Fin.cases with
      | zero => simp [coneSimplex, simplexMap]
      | succ i =>
        change (1 - ((0 : I) : ℝ)) * u.1 i =
          (simplexMap (Fin.succOrderEmb (q + 1)).toOrderHom u).1 ((Fin.succOrderEmb (q + 1)) i)
        rw [simplexMap_apply_image]
        norm_num
    have coneSimplex_one (q : ℕ) (u : Simplex q) :
        coneSimplex q u 1 = vertex (q + 1) 0 := by
      apply Subtype.ext
      funext i
      cases i using Fin.cases <;> simp [coneSimplex, vertex]
    have zeroCone_respects (x y : zeroRaw) (h : zeroRelation x y) (t : I) :
        zeroProjection (x.1 + 1) (coneSimplex x.1 x.2 t) =
          zeroProjection (y.1 + 1) (coneSimplex y.1 y.2 t) := by
      obtain ⟨p, q, a, ha, u, rfl, rfl⟩ := h
      let a' := OrderEmbedding.ofStrictMono a ((a.monotone.strictMono_iff_injective).2 ha)
      change zeroProjection (p + 1) (coneSimplex p u t) =
        zeroProjection (q + 1) (coneSimplex q (simplexMap a'.toOrderHom u) t)
      rw [coneSimplex_face a']
      exact zeroProjection_face (coneFace a').toOrderHom (coneFace a').injective _
    let zeroContraction : C(zeroFat × I, zeroFat) := by
      let f : zeroFat × I → zeroFat := fun p =>
        Quot.lift (fun x : zeroRaw => zeroProjection (x.1 + 1) (coneSimplex x.1 x.2 p.2))
          (fun x y h => zeroCone_respects x y h p.2) p.1
      refine ⟨f, ?_⟩
      apply (isQuotientMap_quot_mk (r := zeroRelation)).continuous_lift_prod_left
      let e : zeroRaw × I ≃ₜ Σ q : ℕ, Simplex q × I := Homeomorph.sigmaProdDistrib
      apply e.symm.isQuotientMap.continuous_iff.mpr
      apply continuous_sigma
      intro q
      exact (zeroProjection_continuous (q + 1)).comp (coneSimplex_continuous q)
    have zeroContraction_zero (x : zeroFat) : zeroContraction (x, 0) = x := by
      induction x using Quot.inductionOn with | h r
      obtain ⟨q, u⟩ := r
      change zeroProjection (q + 1) (coneSimplex q u 0) = zeroProjection q u
      rw [coneSimplex_zero]
      exact (zeroProjection_face (Fin.succOrderEmb (q + 1)).toOrderHom
        (Fin.succOrderEmb (q + 1)).injective u).symm
    have zeroContraction_one (x : zeroFat) :
        zeroContraction (x, 1) = zeroProjection 0 (vertex 0 0) := by
      induction x using Quot.inductionOn with | h r
      obtain ⟨q, u⟩ := r
      change zeroProjection (q + 1) (coneSimplex q u 1) = _
      rw [coneSimplex_one]
      let a : Fin 1 →o Fin (q + 2) := ⟨fun _ => 0, monotone_const⟩
      have ha : Function.Injective a := fun _ _ _ => Subsingleton.elim _ _
      have hv : simplexMap a (vertex 0 0) = vertex (q + 1) 0 := by
        apply Subtype.ext
        funext i
        simp [simplexMap, vertex, a, eq_comm]
      exact (congrArg (zeroProjection (q + 1)) hv).symm.trans
        (zeroProjection_face a ha (vertex 0 0)).symm
    have fat_projection_positive_embedding (n q : ℕ) (z : K n q) (hz : z ≠ zero n q) :
        IsEmbedding (fun u : {s : Simplex q // ∀ i, 0 < s.1 i} => fatProjection n q z u.1) := by
      exact IsEmbedding.of_comp
        ((fatProjection_continuous n q z).comp continuous_subtype_val)
        (collapse n).continuous (projection_positive_embedding n q z hz)
    have fat_characteristic_data (n q : ℕ) (z : K n q) (hz : z ≠ zero n q) :
        ∃ c : PartialEquiv (Fin q → ℝ) (fatLevel n),
          c.source = Metric.ball 0 1 ∧
          ContinuousOn c (Metric.closedBall 0 1) ∧
          ContinuousOn c.symm c.target ∧
          c '' Metric.closedBall 0 1 = Set.range (fatProjection n q z) ∧
          c '' Metric.ball 0 1 = fatProjection n q z '' {t | ∀ i, 0 < t.1 i} ∧
          (∀ x ∈ Metric.sphere 0 1, ∃ t : Simplex q,
            (∃ i, t.1 i = 0) ∧ c x = fatProjection n q z t) := by
      obtain ⟨f, hf, e, he, hb⟩ := ball_simplex_data q
      let g : (Fin q → ℝ) → fatLevel n := fun x =>
        if h : x ∈ Metric.closedBall 0 1 then fatProjection n q z (f ⟨x, h⟩) else (fatLevel n).point
      have hg (x : Metric.closedBall (0 : Fin q → ℝ) 1) :
          g x.1 = fatProjection n q z (f x) := dif_pos x.2
      have hge (x : Metric.ball (0 : Fin q → ℝ) 1) :
          g x.1 = fatProjection n q z (e x).1 := by
        exact (hg ⟨x.1, Metric.ball_subset_closedBall x.2⟩).trans
          (congrArg (fatProjection n q z) (he x))
      have hgcont : ContinuousOn g (Metric.closedBall 0 1) := by
        rw [continuousOn_iff_continuous_restrict]
        exact ((fatProjection_continuous n q z).comp f.continuous).congr (fun x => (hg x).symm)
      have hgemb : IsEmbedding (fun x : Metric.ball (0 : Fin q → ℝ) 1 => g x.1) := by
        have h := (fat_projection_positive_embedding n q z hz).comp e.isEmbedding
        have hfun : (fun x : Metric.ball (0 : Fin q → ℝ) 1 => g x.1) =
            (fun t : {s : Simplex q // ∀ i, 0 < s.1 i} => fatProjection n q z t.1) ∘ e := by
          funext x
          exact hge x
        rw [hfun]
        exact h
      have hginj : Set.InjOn g (Metric.ball 0 1) := by
        intro x hx y hy hxy
        exact congrArg Subtype.val (hgemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
      let c : PartialEquiv (Fin q → ℝ) (fatLevel n) := hginj.toPartialEquiv g (Metric.ball 0 1)
      have hcclosed : c '' Metric.closedBall 0 1 = Set.range (fatProjection n q z) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨f ⟨x, hx⟩, (hg ⟨x, hx⟩).symm⟩
        · rintro ⟨t, rfl⟩
          obtain ⟨x, hx⟩ := hf t
          exact ⟨x.1, x.2, (hg x).trans (congrArg (fatProjection n q z) hx)⟩
      have hcopen : c '' Metric.ball 0 1 = fatProjection n q z '' {t | ∀ i, 0 < t.1 i} := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨(e ⟨x, hx⟩).1, (e ⟨x, hx⟩).2, (hge ⟨x, hx⟩).symm⟩
        · rintro ⟨t, ht, rfl⟩
          obtain ⟨x, hx⟩ := e.surjective ⟨t, ht⟩
          exact ⟨x.1, x.2, (hge x).trans (congrArg (fun t => fatProjection n q z t.1) hx)⟩
      refine ⟨c, rfl, hgcont, ?_, hcclosed, hcopen, ?_⟩
      · rw [continuousOn_iff_continuous_restrict]
        have hinv : Continuous (fun y : c.target =>
            (⟨c.symm y.1, c.map_target y.2⟩ : Metric.ball (0 : Fin q → ℝ) 1)) := by
          apply hgemb.isInducing.continuous_iff.mpr
          exact continuous_subtype_val.congr (fun y => (c.right_inv y.2).symm)
        exact continuous_subtype_val.comp hinv
      · intro x hx
        let x' : Metric.closedBall (0 : Fin q → ℝ) 1 := ⟨x, Metric.sphere_subset_closedBall hx⟩
        exact ⟨f x', (hb x').mp hx, hg x'⟩
    have fat_relative_cw (n : ℕ) :
        Nonempty (RelCWComplex (Set.univ : Set (fatLevel n)) (Set.range (zeroIncl n))) := by
      choose ch hsource hcont hinv hclosed hopen hbound using fat_characteristic_data n
      let Cell (q : ℕ) := {z : K n q // z ≠ zero n q}
      letI (q : ℕ) : Finite (K n q) := labels_finite n q
      letI (q : ℕ) : Fintype (Cell q) := Fintype.ofFinite _
      refine ⟨{
        cell := Cell
        map := fun q z => ch q z.1 z.2
        source_eq := fun q z => hsource q z.1 z.2
        continuousOn := fun q z => hcont q z.1 z.2
        continuousOn_symm := fun q z => hinv q z.1 z.2
        pairwiseDisjoint' := ?_
        disjointBase' := ?_
        mapsTo := ?_
        closed' := ?_
        isClosedBase := (zeroIncl_closed n).isClosed_range
        union' := ?_ }⟩
      · intro a _ b _ hab
        obtain ⟨p, z⟩ := a
        obtain ⟨q, w⟩ := b
        apply Set.disjoint_left.mpr
        intro x hx hy
        change x ∈ ch p z.1 z.2 '' Metric.ball 0 1 at hx
        change x ∈ ch q w.1 w.2 '' Metric.ball 0 1 at hy
        rw [hopen p z.1 z.2] at hx
        rw [hopen q w.1 w.2] at hy
        obtain ⟨s, hs, hsx⟩ := hx
        obtain ⟨t, ht, htx⟩ := hy
        have he := positive_label_unique n p q z.1 w.1 z.2 w.2 s t hs ht
          (congrArg (collapse n) (hsx.trans htx.symm))
        apply hab
        have hpq : p = q := congrArg Sigma.fst he
        subst q
        have hzw : z.1 = w.1 := eq_of_heq (Sigma.mk.inj he).2
        have hzw' : z = w := Subtype.ext hzw
        subst w
        rfl
      · intro q z
        apply Set.disjoint_left.mpr
        intro x hx hy
        rw [hopen] at hx
        obtain ⟨u, hu, rfl⟩ := hx
        exact positive_not_point n q z.1 z.2 u hu ((collapse_fiber n _).mpr hy)
      · intro q z
        refine ⟨fun _ => Finset.univ, ?_⟩
        intro x hx
        obtain ⟨t, ht, hxt⟩ := hbound q z.1 z.2 x hx
        obtain ⟨r, hr, a, u, hu, hmap⟩ := simplex_support_boundary q t ht
        have he : fatProjection n r (pull a.toOrderHom z.1) u = ch q z.1 z.2 x :=
          (fatProjection_face a.toOrderHom a.injective z.1 u).trans
            ((congrArg (fatProjection n q z.1) hmap).trans hxt.symm)
        by_cases hz : pull a.toOrderHom z.1 = zero n r
        · left
          rw [hz] at he
          exact ⟨zeroProjection r u, he⟩
        · right
          apply Set.mem_iUnion_of_mem r
          apply Set.mem_iUnion_of_mem hr
          apply Set.mem_iUnion_of_mem (⟨pull a.toOrderHom z.1, hz⟩ : Cell r)
          apply Set.mem_iUnion_of_mem (Finset.mem_univ _)
          rw [hclosed]
          exact ⟨u, he⟩
      · rintro A _ ⟨hA, hbase⟩
        apply isQuotientMap_quot_mk.isCoinducing.isClosed_preimage.mp
        apply isClosed_sigma_iff.mpr
        intro q
        apply isClosed_sigma_iff.mpr
        intro z
        change IsClosed ((fatProjection n q z) ⁻¹' A)
        by_cases hz : z = zero n q
        · subst z
          have he : (fatProjection n q (zero n q)) ⁻¹' (A ∩ Set.range (zeroIncl n)) =
              (fatProjection n q (zero n q)) ⁻¹' A := by
            ext u
            exact and_iff_left ⟨zeroProjection q u, rfl⟩
          rw [← he]
          exact hbase.preimage (fatProjection_continuous n q (zero n q))
        · have hc : IsClosed (A ∩ Set.range (fatProjection n q z)) := by
            have hc := hA q ⟨z, hz⟩
            change IsClosed (A ∩ ch q z hz '' Metric.closedBall 0 1) at hc
            rwa [hclosed] at hc
          have hh := hc.preimage (fatProjection_continuous n q z)
          simpa only [Set.preimage_inter, Set.preimage_range, Set.inter_univ] using hh
      · apply Set.eq_univ_of_forall
        intro x
        induction x using Quot.inductionOn with | h r
        obtain ⟨q, z, u⟩ := r
        change fatProjection n q z u ∈ _
        by_cases hz : z = zero n q
        · subst z
          exact Or.inl ⟨zeroProjection q u, rfl⟩
        · right
          apply Set.mem_iUnion_of_mem q
          apply Set.mem_iUnion_of_mem (⟨z, hz⟩ : Cell q)
          rw [hclosed]
          exact ⟨u, rfl⟩
    -- T6: descend an extension of the zero-subspace contraction through the actual quotient.
    have fat_pair_from_extension (n : ℕ) (H : C(fatLevel n × I, fatLevel n))
        (hH0 : ∀ x, H (x, 0) = x)
        (hHA : ∀ (x : zeroFat) t,
          H (zeroIncl n x, t) = zeroIncl n (zeroContraction (x, t))) :
        ∃ s : C(level n, fatLevel n), s (level n).point = (fatLevel n).point ∧
          (∀ x, H (x, 1) = s (collapse n x)) ∧
          (∀ (x : zeroFat) t, H (zeroIncl n x, t) ∈ Set.range (zeroIncl n)) ∧
          ∃ G : C(level n × I, level n),
            (∀ x, G (x, 0) = x) ∧
            (∀ x, G (x, 1) = collapse n (s x)) ∧
            (∀ t, G ((level n).point, t) = (level n).point) := by
      have hH1 (x : zeroFat) : H (zeroIncl n x, 1) = (fatLevel n).point := by
        rw [hHA, zeroContraction_one]
        rfl
      let rawS : Raw n → fatLevel n := fun x => H (fatProjection n x.1 x.2.1 x.2.2, 1)
      have rawS_respects : ∀ x y, relation n x y → rawS x = rawS y := by
        intro x y h
        rcases h with h | ⟨hx, hy⟩
        · exact congrArg (fun x => H (x, 1)) (Quot.sound h)
        · change H (fatProjection n x.1 x.2.1 x.2.2, 1) =
            H (fatProjection n y.1 y.2.1 y.2.2, 1)
          rw [hx, hy]
          exact (hH1 (zeroProjection x.1 x.2.2)).trans (hH1 (zeroProjection y.1 y.2.2)).symm
      let s : C(level n, fatLevel n) :=
        ⟨Quot.lift rawS rawS_respects, continuous_quot_lift rawS_respects
          (H.continuous.comp (continuous_quot_mk.prodMk continuous_const))⟩
      have hs0 : s (level n).point = (fatLevel n).point := hH1 (zeroProjection 0 (vertex 0 0))
      have hs : ∀ x, H (x, 1) = s (collapse n x) := by
        intro x
        induction x using Quot.inductionOn with | h r
        rfl
      have hHbase (x : zeroFat) (t : I) : collapse n (H (zeroIncl n x, t)) = (level n).point := by
        rw [hHA, collapse_zero]
      let rawG (x : Raw n) (t : I) : level n :=
        collapse n (H (fatProjection n x.1 x.2.1 x.2.2, t))
      have rawG_respects : ∀ x y, relation n x y → rawG x = rawG y := by
        intro x y h
        funext t
        rcases h with h | ⟨hx, hy⟩
        · exact congrArg (fun x => collapse n (H (x, t))) (Quot.sound h)
        · change collapse n (H (fatProjection n x.1 x.2.1 x.2.2, t)) =
            collapse n (H (fatProjection n y.1 y.2.1 y.2.2, t))
          rw [hx, hy]
          exact (hHbase (zeroProjection x.1 x.2.2) t).trans
            (hHbase (zeroProjection y.1 y.2.2) t).symm
      let G : C(level n × I, level n) :=
        ⟨fun p => Quot.lift rawG rawG_respects p.1 p.2, by
          apply (isQuotientMap_quot_mk (r := relation n)).continuous_lift_prod_left
          exact (collapse n).continuous.comp (H.continuous.comp
            ((continuous_quot_mk.comp continuous_fst).prodMk continuous_snd))⟩
      refine ⟨s, hs0, hs, ?_, G, ?_, ?_, ?_⟩
      · intro x t
        exact ⟨zeroContraction (x, t), (hHA x t).symm⟩
      · intro x
        induction x using Quot.inductionOn with | h r
        change collapse n (H (fatProjection n r.1 r.2.1 r.2.2, 0)) = _
        rw [hH0]
        rfl
      · intro x
        induction x using Quot.inductionOn with | h r
        rfl
      · intro t
        exact hHbase (zeroProjection 0 (vertex 0 0)) t
    have fat_projection_positive_embedding_all (n q : ℕ) (z : K n q) :
        IsEmbedding (fun t : {s : Simplex q // ∀ i, 0 < s.1 i} => fatProjection n q z t.1) := by
      let P := {s : Simplex q // ∀ i, 0 < s.1 i}
      let U := {x : fatLevel n // fatMomentMap n q z none x ≠ 0}
      let f : P → U := fun t => ⟨fatProjection n q z t.1, by
        have hp : 0 < ∏ i, t.1.1 i := Finset.prod_pos (fun i _ => t.2 i)
        simpa only [fatMomentMap_projection, moment_top, ite_true, Option.elim_none, mul_one]
          using hp.ne'⟩
      let g : U → (Fin (q + 1) → ℝ) := fun x i =>
        fatMomentMap n q z (some i) x.1 / fatMomentMap n q z none x.1
      have hf : Continuous f :=
        Continuous.subtype_mk ((fatProjection_continuous n q z).comp continuous_subtype_val) _
      have hg : Continuous g := by
        apply continuous_pi
        intro i
        exact ((fatMomentMap n q z (some i)).continuous.comp continuous_subtype_val).div
          ((fatMomentMap n q z none).continuous.comp continuous_subtype_val) (fun x => x.2)
      have hcomp : (g ∘ f) = fun t : P => t.1.1 := by
        funext t i
        change fatMomentMap n q z (some i) (fatProjection n q z t.1) /
          fatMomentMap n q z none (fatProjection n q z t.1) = t.1.1 i
        simp only [fatMomentMap_projection, moment_top, ite_true, Option.elim_none,
          Option.elim_some, mul_one]
        exact mul_div_cancel_left₀ _ (Finset.prod_pos (fun j _ => t.2 j)).ne'
      have he : IsEmbedding f := IsEmbedding.of_comp hf hg (by
        rw [hcomp]
        exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
      exact IsEmbedding.subtypeVal.comp he
    have fat_label_unique (n p q : ℕ) (z : K n p) (w : K n q)
        (s : Simplex p) (t : Simplex q) (hs : ∀ i, 0 < s.1 i) (ht : ∀ i, 0 < t.1 i)
        (he : fatProjection n p z s = fatProjection n q w t) :
        (⟨p, z⟩ : Σ r, K n r) = ⟨q, w⟩ := by
      have hp : 0 < ∏ i, s.1 i := Finset.prod_pos (fun i _ => hs i)
      have hq : 0 < ∏ i, t.1 i := Finset.prod_pos (fun i _ => ht i)
      have hpq : p = q := by
        rcases lt_trichotomy p q with hl | hh | hl
        · have hh := congrArg (fatMomentMap n q w none) he
          simp only [fatMomentMap_projection, moment_lower n q p hl, moment_top,
            ite_true, Option.elim_none, mul_one] at hh
          linarith
        · exact hh
        · have hh := congrArg (fatMomentMap n p z none) he
          simp only [fatMomentMap_projection, moment_lower n p q hl, moment_top,
            ite_true, Option.elim_none, mul_one] at hh
          linarith
      subst q
      have hzw : z = w := by
        by_contra hne
        have hh := congrArg (fatMomentMap n p z none) he
        simp only [fatMomentMap_projection, moment_top, ite_true, if_neg (Ne.symm hne),
          Option.elim_none, mul_one] at hh
        linarith
      subst w
      rfl
    have fat_characteristic_all (n q : ℕ) (z : K n q) :
        ∃ c : PartialEquiv (Fin q → ℝ) (fatLevel n),
          c.source = Metric.ball 0 1 ∧
          ContinuousOn c (Metric.closedBall 0 1) ∧
          ContinuousOn c.symm c.target ∧
          c '' Metric.closedBall 0 1 = Set.range (fatProjection n q z) ∧
          c '' Metric.ball 0 1 = fatProjection n q z '' {t | ∀ i, 0 < t.1 i} ∧
          (∀ x ∈ Metric.sphere 0 1, ∃ t : Simplex q,
            (∃ i, t.1 i = 0) ∧ c x = fatProjection n q z t) := by
      obtain ⟨f, hf, e, he, hb⟩ := ball_simplex_data q
      let g : (Fin q → ℝ) → fatLevel n := fun x =>
        if h : x ∈ Metric.closedBall 0 1 then fatProjection n q z (f ⟨x, h⟩) else (fatLevel n).point
      have hg (x : Metric.closedBall (0 : Fin q → ℝ) 1) :
          g x.1 = fatProjection n q z (f x) := dif_pos x.2
      have hge (x : Metric.ball (0 : Fin q → ℝ) 1) :
          g x.1 = fatProjection n q z (e x).1 := by
        exact (hg ⟨x.1, Metric.ball_subset_closedBall x.2⟩).trans
          (congrArg (fatProjection n q z) (he x))
      have hgcont : ContinuousOn g (Metric.closedBall 0 1) := by
        rw [continuousOn_iff_continuous_restrict]
        exact ((fatProjection_continuous n q z).comp f.continuous).congr (fun x => (hg x).symm)
      have hgemb : IsEmbedding (fun x : Metric.ball (0 : Fin q → ℝ) 1 => g x.1) := by
        have h := (fat_projection_positive_embedding_all n q z).comp e.isEmbedding
        have hfun : (fun x : Metric.ball (0 : Fin q → ℝ) 1 => g x.1) =
            (fun t : {s : Simplex q // ∀ i, 0 < s.1 i} => fatProjection n q z t.1) ∘ e := by
          funext x
          exact hge x
        rw [hfun]
        exact h
      have hginj : Set.InjOn g (Metric.ball 0 1) := by
        intro x hx y hy hxy
        exact congrArg Subtype.val (hgemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
      let c : PartialEquiv (Fin q → ℝ) (fatLevel n) := hginj.toPartialEquiv g (Metric.ball 0 1)
      have hcclosed : c '' Metric.closedBall 0 1 = Set.range (fatProjection n q z) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨f ⟨x, hx⟩, (hg ⟨x, hx⟩).symm⟩
        · rintro ⟨t, rfl⟩
          obtain ⟨x, hx⟩ := hf t
          exact ⟨x.1, x.2, (hg x).trans (congrArg (fatProjection n q z) hx)⟩
      have hcopen : c '' Metric.ball 0 1 = fatProjection n q z '' {t | ∀ i, 0 < t.1 i} := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨(e ⟨x, hx⟩).1, (e ⟨x, hx⟩).2, (hge ⟨x, hx⟩).symm⟩
        · rintro ⟨t, ht, rfl⟩
          obtain ⟨x, hx⟩ := e.surjective ⟨t, ht⟩
          exact ⟨x.1, x.2, (hge x).trans (congrArg (fun t => fatProjection n q z t.1) hx)⟩
      refine ⟨c, rfl, hgcont, ?_, hcclosed, hcopen, ?_⟩
      · rw [continuousOn_iff_continuous_restrict]
        have hinv : Continuous (fun y : c.target =>
            (⟨c.symm y.1, c.map_target y.2⟩ : Metric.ball (0 : Fin q → ℝ) 1)) := by
          apply hgemb.isInducing.continuous_iff.mpr
          exact continuous_subtype_val.congr (fun y => (c.right_inv y.2).symm)
        exact continuous_subtype_val.comp hinv
      · intro x hx
        let x' : Metric.closedBall (0 : Fin q → ℝ) 1 := ⟨x, Metric.sphere_subset_closedBall hx⟩
        exact ⟨f x', (hb x').mp hx, hg x'⟩
    have fat_cw (n : ℕ) : Nonempty (CWComplex (Set.univ : Set (fatLevel n))) := by
      choose ch hsource hcont hinv hclosed hopen hbound using fat_characteristic_all n
      letI (q : ℕ) : Finite (K n q) := labels_finite n q
      letI (q : ℕ) : Fintype (K n q) := Fintype.ofFinite _
      refine ⟨{
        cell := K n
        map := ch
        source_eq := hsource
        continuousOn := hcont
        continuousOn_symm := hinv
        pairwiseDisjoint' := ?_
        mapsTo' := ?_
        closed' := ?_
        union' := ?_ }⟩
      · intro a _ b _ hab
        obtain ⟨p, z⟩ := a
        obtain ⟨q, w⟩ := b
        apply Set.disjoint_left.mpr
        intro x hx hy
        change x ∈ ch p z '' Metric.ball 0 1 at hx
        change x ∈ ch q w '' Metric.ball 0 1 at hy
        rw [hopen] at hx hy
        obtain ⟨s, hs, hsx⟩ := hx
        obtain ⟨t, ht, htx⟩ := hy
        exact hab (fat_label_unique n p q z w s t hs ht (hsx.trans htx.symm))
      · intro q z
        refine ⟨fun _ => Finset.univ, ?_⟩
        intro x hx
        obtain ⟨t, ht, hxt⟩ := hbound q z x hx
        obtain ⟨r, hr, a, u, hu, hmap⟩ := simplex_support_boundary q t ht
        have he : fatProjection n r (pull a.toOrderHom z) u = ch q z x :=
          (fatProjection_face a.toOrderHom a.injective z u).trans
            ((congrArg (fatProjection n q z) hmap).trans hxt.symm)
        apply Set.mem_iUnion_of_mem r
        apply Set.mem_iUnion_of_mem hr
        apply Set.mem_iUnion_of_mem (pull a.toOrderHom z)
        apply Set.mem_iUnion_of_mem (Finset.mem_univ _)
        rw [hclosed]
        exact ⟨u, he⟩
      · intro A _ hA
        apply isQuotientMap_quot_mk.isCoinducing.isClosed_preimage.mp
        apply isClosed_sigma_iff.mpr
        intro q
        apply isClosed_sigma_iff.mpr
        intro z
        change IsClosed ((fatProjection n q z) ⁻¹' A)
        have hc : IsClosed (A ∩ Set.range (fatProjection n q z)) := by
          have hc := hA q z
          change IsClosed (A ∩ ch q z '' Metric.closedBall 0 1) at hc
          rwa [hclosed] at hc
        have hh := hc.preimage (fatProjection_continuous n q z)
        simpa only [Set.preimage_inter, Set.preimage_range, Set.inter_univ] using hh
      · apply Set.eq_univ_of_forall
        intro x
        induction x using Quot.inductionOn with | h r
        obtain ⟨q, z, u⟩ := r
        apply Set.mem_iUnion_of_mem q
        apply Set.mem_iUnion_of_mem z
        rw [hclosed]
        exact ⟨u, rfl⟩
    -- T7: compact sets meet only finitely many open CW cells.
    have cw_compact_finite_closedCell {X : Type} [TopologicalSpace X] [T2Space X]
        [CWComplex (Set.univ : Set X)] (K : Set X) (hK : IsCompact K) :
        ∃ F : Finset (Σ n : ℕ, RelCWComplex.cell (Set.univ : Set X) n),
          K ⊆ ⋃ a ∈ F, RelCWComplex.closedCell a.1 a.2 := by
      classical
      let Cells := Σ n : ℕ, RelCWComplex.cell (Set.univ : Set X) n
      let J : Set Cells := {a | (K ∩ RelCWComplex.openCell a.1 a.2).Nonempty}
      choose p hp using (fun a : J => a.2)
      have hlabel (a : J) (b : Cells) (h : p a ∈ RelCWComplex.openCell b.1 b.2) :
          a.1 = b := by
        by_contra hn
        exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hn) (hp a).2 h
      have hinj : Function.Injective p := by
        intro a b h
        apply Subtype.ext
        apply hlabel a b.1
        rw [h]
        exact (hp b).2
      have hclosed (T : Set X) (hT : T ⊆ Set.range p) : IsClosed T := by
        apply CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
          (Set.subset_univ T)
        intro n hn i
        left
        have hs : (T ∩ RelCWComplex.openCell n i).Subsingleton := by
          intro x hx y hy
          obtain ⟨a,rfl⟩ := hT hx.1
          obtain ⟨b,rfl⟩ := hT hy.1
          have hab : a = b := Subtype.ext ((hlabel a ⟨n,i⟩ hx.2).trans
            (hlabel b ⟨n,i⟩ hy.2).symm)
          exact congrArg p hab
        exact hs.finite.isClosed
      have hcompact : IsCompact (Set.range p) :=
        hK.of_isClosed_subset (hclosed _ Set.Subset.rfl) (by
          rintro _ ⟨a,rfl⟩
          exact (hp a).1)
      have hdiscrete : IsDiscrete (Set.range p) :=
        isDiscrete_iff_forall_mem_exists_isClosed.mpr (by
          intro T hT
          exact ⟨T,hclosed T hT,Set.inter_eq_left.mpr hT⟩)
      have hfinite : Finite J := (Set.finite_range_iff hinj).mp (hcompact.finite hdiscrete)
      have hJ : J.Finite := Set.finite_coe_iff.mp hfinite
      refine ⟨hJ.toFinset,?_⟩
      intro x hx
      have hcover : x ∈ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
          RelCWComplex.openCell n i := by
        rw [CWComplex.iUnion_openCell_eq_complex]
        trivial
      obtain ⟨n,i,hi⟩ := by simpa only [Set.mem_iUnion] using hcover
      refine Set.mem_iUnion.mpr ⟨⟨n,i⟩,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
      · exact hJ.mem_toFinset.mpr ⟨x,hx,hi⟩
      · exact RelCWComplex.openCell_subset_closedCell n i hi
    -- T5: homotopy extension for an actual relative CW complex.
    have relative_cw_hep
        (X : Type) [TopologicalSpace X] [T2Space X] (A : Set X)
        [RelCWComplex (Set.univ : Set X) A] (Z : Type) [TopologicalSpace Z]
        (f : C(X,Z)) (h : C(A × I,Z)) (h0 : ∀ a : A, h (a,0)=f a) :
        ∃ H : C(X × I,Z), (∀ x, H (x,0)=f x) ∧
          (∀ (a : A) t, H (a,t)=h (a,t)) := open Set Metric in by
      have cube_boundary_retraction (n : ℕ) :
          ∃ r : C((Fin n → I) × I,(Fin n → I) × I),
            (∀ x, r (x,0)=(x,0)) ∧
            (∀ x, x ∈ Cube.boundary (Fin n) → ∀ t, r (x,t)=(x,t)) ∧
            (∀ q, (r q).2=0 ∨ (r q).1 ∈ Cube.boundary (Fin n)) := by
        let v (x : Fin n → I) (i : Fin n) : ℝ := (x i:ℝ)-1/2
        let m (q : (Fin n → I) × I) : ℝ := max ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
        have hb (x : Fin n → I) : 2*‖v x‖ ≤ 1 := by
          have hh : ‖v x‖ ≤ (1/2:ℝ) := by
            apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
            intro i
            rw [Real.norm_eq_abs]
            apply abs_le.mpr
            constructor <;> dsimp [v] <;> linarith [(x i).property.1,(x i).property.2]
          linarith
        have hm (q : (Fin n → I) × I) : 0 < m q ∧ m q ≤ 1 := by
          constructor
          · have h := le_max_left ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
            change 0 < max _ _
            linarith [q.2.property.2]
          · exact max_le (by linarith [q.2.property.1]) (hb q.1)
        have hcoord (q : (Fin n → I) × I) (i : Fin n) : 2*|(q.1 i:ℝ)-1/2| ≤ m q := by
          have h := norm_le_pi_norm (v q.1) i
          rw [Real.norm_eq_abs] at h
          have he := le_max_right ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
          change 2*‖v q.1‖ ≤ m q at he
          dsimp [v] at h
          linarith
        have hx (q : (Fin n → I) × I) (i : Fin n) :
            1/2+((q.1 i:ℝ)-1/2)/m q ∈ Set.Icc (0:ℝ) 1 := by
          have hl : -(1/2:ℝ) ≤ ((q.1 i:ℝ)-1/2)/m q := by
            apply (le_div_iff₀ (hm q).1).mpr
            linarith [hcoord q i,neg_abs_le ((q.1 i:ℝ)-1/2)]
          have hu : ((q.1 i:ℝ)-1/2)/m q ≤ (1/2:ℝ) := by
            apply (div_le_iff₀ (hm q).1).mpr
            linarith [hcoord q i,le_abs_self ((q.1 i:ℝ)-1/2)]
          constructor <;> linarith
        have hy (q : (Fin n → I) × I) : 2+((q.2:ℝ)-2)/m q ∈ Set.Icc (0:ℝ) 1 := by
          have hl : -(2:ℝ) ≤ ((q.2:ℝ)-2)/m q := by
            apply (le_div_iff₀ (hm q).1).mpr
            have h := le_max_left ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
            change (2-(q.2:ℝ))/2 ≤ m q at h
            linarith
          have hu : ((q.2:ℝ)-2)/m q ≤ (q.2:ℝ)-2 := by
            apply (div_le_iff₀ (hm q).1).mpr
            nlinarith [(hm q).2,q.2.property.2]
          constructor <;> linarith [q.2.property.2]
        have hv : Continuous v := continuous_pi fun i =>
          (continuous_subtype_val.comp (continuous_apply i)).sub continuous_const
        have hmcont : Continuous m :=
          ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).div_const 2).max
            (continuous_const.mul (hv.comp continuous_fst).norm)
        let r : C((Fin n → I) × I,(Fin n → I) × I) := ⟨fun q => (fun i => ⟨_,hx q i⟩,⟨_,hy q⟩),
          (continuous_pi fun i => (continuous_const.add
            (((continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)).sub continuous_const).div hmcont
              (fun q => ne_of_gt (hm q).1))).subtype_mk _).prodMk
            ((continuous_const.add
              (((continuous_subtype_val.comp continuous_snd).sub continuous_const).div hmcont
                (fun q => ne_of_gt (hm q).1))).subtype_mk _)⟩
        have hmzero (x : Fin n → I) : m (x,0)=1 := by
          dsimp [m]
          norm_num only [show ((0:I):ℝ)=0 from rfl,sub_zero,show (2:ℝ)/2=1 by norm_num]
          exact max_eq_left (hb x)
        have hmbound (x : Fin n → I) (hx : x ∈ Cube.boundary (Fin n)) (t : I) : m (x,t)=1 := by
          obtain ⟨i,hi⟩ := hx
          have h : 1 ≤ m (x,t) := by
            have hh := hcoord (x,t) i
            change 2*|(x i:ℝ)-1/2| ≤ m (x,t) at hh
            rcases hi with hi | hi <;> rw [hi] at hh <;> norm_num at hh ⊢ <;> linarith
          exact le_antisymm (hm (x,t)).2 h
        refine ⟨r,?_,?_,?_⟩
        · intro x
          apply Prod.ext
          · funext i
            apply Subtype.ext
            simp [r,hmzero]
          · apply Subtype.ext
            simp [r,hmzero]
        · intro x hx t
          apply Prod.ext
          · funext i
            apply Subtype.ext
            simp [r,hmbound x hx t]
          · apply Subtype.ext
            simp [r,hmbound x hx t]
        · intro q
          by_cases h : 2*‖v q.1‖ ≤ (2-(q.2:ℝ))/2
          · left
            apply Subtype.ext
            change 2+((q.2:ℝ)-2)/m q = 0
            have hd : ((q.2:ℝ)-2)/m q = -2 := by
              apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
              dsimp [m]
              rw [max_eq_left h]
              ring
            rw [hd]
            norm_num
          · have hmax : m q=2*‖v q.1‖ := max_eq_right (le_of_not_ge h)
            have hn : Nonempty (Fin n) := by
              by_contra he
              haveI : IsEmpty (Fin n) := not_nonempty_iff.mp he
              have hv0 : v q.1=0 := Subsingleton.elim _ _
              have := (hm q).1
              rw [hmax,hv0,norm_zero,mul_zero] at this
              exact (lt_irrefl _ this)
            letI := hn
            obtain ⟨i,hi⟩ := (IsGreatest.pi_norm (v q.1)).1
            change ‖v q.1 i‖=‖v q.1‖ at hi
            rw [Real.norm_eq_abs] at hi
            have hmax' : m q=2*|(q.1 i:ℝ)-1/2| := by
              rw [hmax,← hi]
            right
            refine ⟨i,?_⟩
            by_cases ht : 0 ≤ (q.1 i:ℝ)-1/2
            · right
              apply Subtype.ext
              change 1/2+((q.1 i:ℝ)-1/2)/m q = 1
              have hd : ((q.1 i:ℝ)-1/2)/m q = 1/2 := by
                apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
                rw [hmax',abs_of_nonneg ht]
                ring
              rw [hd]
              norm_num
            · left
              apply Subtype.ext
              change 1/2+((q.1 i:ℝ)-1/2)/m q = 0
              have hd : ((q.1 i:ℝ)-1/2)/m q = -(1/2) := by
                apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
                rw [hmax',abs_of_neg (lt_of_not_ge ht)]
                ring
              rw [hd]
              norm_num
      have cube_boundary_hep_general (n : ℕ) {Y : Type} [TopologicalSpace Y]
          (f : C((Fin n → I),Y))
          (g : C((Cube.boundary (Fin n)) × I,Y))
          (hg : ∀ x : Cube.boundary (Fin n), g (x,0)=f x.1) :
          ∃ H : C((Fin n → I) × I,Y), (∀ x, H (x,0)=f x) ∧
            (∀ (x : Cube.boundary (Fin n)) t, H (x.1,t)=g (x,t)) := by
        classical
        obtain ⟨r,hzero,hboundary,hr⟩ := cube_boundary_retraction n
        have hc : IsClosed (Cube.boundary (Fin n)) := by
          have he : Cube.boundary (Fin n)=⋃ i : Fin n, {x : Fin n → I | x i=0 ∨ x i=1} := by
            ext x
            simp [Cube.boundary]
          rw [he]
          apply isClosed_iUnion_of_finite
          intro i
          exact (isClosed_eq (continuous_apply i) continuous_const).union
            (isClosed_eq (continuous_apply i) continuous_const)
        let U : Set ((Fin n → I) × I) := {q | (r q).2=0}
        let V : Set ((Fin n → I) × I) := {q | (r q).1 ∈ Cube.boundary (Fin n)}
        have hU : IsClosed U := isClosed_eq r.continuous.snd continuous_const
        have hV : IsClosed V := hc.preimage r.continuous.fst
        have hUV : U ∪ V=Set.univ := by ext q; exact iff_true_intro (hr q)
        let F (q : (Fin n → I) × I) :=
          if h : (r q).1 ∈ Cube.boundary (Fin n) then g (⟨(r q).1,h⟩,(r q).2) else f (r q).1
        have hu : ContinuousOn F U := (f.continuous.comp r.continuous.fst).continuousOn.congr (by
          intro q hq
          dsimp only [F]
          split_ifs with hb
          · change g (⟨(r q).1,hb⟩,(r q).2)=f (r q).1
            rw [show (r q).2=0 from hq,hg]
          · rfl)
        have hv : ContinuousOn F V := by
          apply continuousOn_iff_continuous_restrict.mpr
          let h : V → (Cube.boundary (Fin n)) × I := fun q =>
            (⟨(r q.1).1,q.property⟩,(r q.1).2)
          have hh : Continuous h :=
            ((r.continuous.comp continuous_subtype_val).fst.subtype_mk _).prodMk
              (r.continuous.comp continuous_subtype_val).snd
          apply (g.continuous.comp hh).congr
          intro q
          change g (⟨(r q.1).1,q.property⟩,(r q.1).2)=F q.1
          dsimp only [F]
          rw [dif_pos (show (r q.1).1 ∈ Cube.boundary (Fin n) from q.property)]
        have hF : Continuous F := continuousOn_univ.mp (hUV ▸ hu.union_of_isClosed hv hU hV)
        refine ⟨⟨F,hF⟩,?_,?_⟩
        · intro x
          change F (x,0)=f x
          dsimp only [F]
          simp only [hzero]
          split_ifs with hx
          · exact hg ⟨x,hx⟩
          · rfl
        · intro x t
          change F (x.1,t)=g (x,t)
          dsimp only [F]
          simp only [hboundary x.1 x.property t,dif_pos x.property]
      have closedBall_boundary_hep (n : ℕ) {Y : Type} [TopologicalSpace Y]
          (f : C(Metric.closedBall (0 : Fin n → ℝ) 1,Y))
          (g : C((Metric.sphere (0 : Fin n → ℝ) 1) × I,Y))
          (hg : ∀ x : Metric.sphere (0 : Fin n → ℝ) 1,
            g (x,0)=f ⟨x.1,Metric.sphere_subset_closedBall x.2⟩) :
          ∃ H : C((Metric.closedBall (0 : Fin n → ℝ) 1) × I,Y),
            (∀ x, H (x,0)=f x) ∧
            (∀ (x : Metric.sphere (0 : Fin n → ℝ) 1) t,
              H (⟨x.1,Metric.sphere_subset_closedBall x.2⟩,t)=g (x,t)) := by
        have hc (z : Fin n → ℝ) : z ∈ Metric.closedBall 0 1 ↔
            ∀ i, -1≤z i ∧ z i≤1 := by
          rw [closedBall_pi _ (by norm_num : (0:ℝ)≤1)]
          simp [Real.closedBall_eq_Icc,Pi.le_def,forall_and]
        have hb (z : Fin n → ℝ) : z ∈ Metric.ball 0 1 ↔ ∀ i, -1<z i ∧ z i<1 := by
          rw [ball_pi _ (by norm_num : (0:ℝ)<1)]
          simp only [Set.mem_pi,Set.mem_univ,forall_const,Real.ball_eq_Ioo,Pi.zero_apply,
            zero_sub,zero_add,Set.mem_Ioo]
        let E : (Metric.closedBall (0 : Fin n → ℝ) 1) ≃ₜ (Fin n → I) :=
          { toFun := fun z i => ⟨(z.1 i+1)/2,by
              have h := (hc _).mp z.2 i
              constructor <;> linarith⟩
            invFun := fun t => ⟨fun i => 2*(t i:ℝ)-1,by
              apply (hc _).mpr
              intro i
              constructor <;> linarith [(t i).property.1,(t i).property.2]⟩
            left_inv := by intro z; apply Subtype.ext; funext i; dsimp; ring
            right_inv := by intro t; funext i; apply Subtype.ext; dsimp; ring
            continuous_toFun := by
              apply continuous_pi
              intro i
              apply Continuous.subtype_mk
              exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2
            continuous_invFun := by
              apply Continuous.subtype_mk
              apply continuous_pi
              intro i
              exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const }
        have hEb (z : Metric.closedBall (0 : Fin n → ℝ) 1) :
            z.1 ∈ Metric.sphere 0 1 ↔ E z ∈ Cube.boundary (Fin n) := by
          constructor
          · intro hz
            by_contra hn
            have hzball : z.1 ∈ Metric.ball 0 1 := by
              apply (hb _).mpr
              intro i
              have h0 : E z i≠0 := fun h => hn ⟨i,Or.inl h⟩
              have h1 : E z i≠1 := fun h => hn ⟨i,Or.inr h⟩
              have hi := (hc _).mp z.2 i
              constructor
              · apply lt_of_le_of_ne hi.1
                intro h
                apply h0
                apply Subtype.ext
                change (z.1 i+1)/2=0
                rw [← h]
                norm_num
              · apply lt_of_le_of_ne hi.2
                intro h
                apply h1
                apply Subtype.ext
                change (z.1 i+1)/2=1
                rw [h]
                norm_num
            exact Metric.sphere_disjoint_ball.le_bot ⟨hz,hzball⟩
          · rintro ⟨i,hi⟩
            rw [← Metric.closedBall_sdiff_ball]
            refine ⟨z.2,?_⟩
            intro hz
            have hzi := (hb _).mp hz i
            rcases hi with hi | hi
            · have hh := congrArg Subtype.val hi
              change (z.1 i+1)/2=0 at hh
              linarith
            · have hh := congrArg Subtype.val hi
              change (z.1 i+1)/2=1 at hh
              linarith
        let f' : C((Fin n → I),Y) := f.comp ⟨E.symm,E.symm.continuous⟩
        let g' : C((Cube.boundary (Fin n)) × I,Y) :=
          ⟨fun p => g (⟨(E.symm p.1.1).1,(hEb _).mpr (by simpa only [E.apply_symm_apply] using p.1.2)⟩,p.2),
            g.continuous.comp
              (((continuous_subtype_val.comp (E.symm.continuous.comp
                (continuous_subtype_val.comp continuous_fst))).subtype_mk _).prodMk continuous_snd)⟩
        obtain ⟨F,hF0,hFb⟩ := cube_boundary_hep_general n f' g' (by
          intro x
          exact hg ⟨(E.symm x.1).1,(hEb _).mpr (by simpa only [E.apply_symm_apply] using x.2)⟩)
        refine ⟨F.comp ⟨fun p => (E p.1,p.2),(E.continuous.comp continuous_fst).prodMk continuous_snd⟩,
          ?_,?_⟩
        · intro x
          change F (E x,0)=f x
          rw [hF0]
          change f (E.symm (E x))=f x
          rw [E.symm_apply_apply]
        · intro x t
          let z : Metric.closedBall (0 : Fin n → ℝ) 1 := ⟨x.1,Metric.sphere_subset_closedBall x.2⟩
          change F (E z,t)=g (x,t)
          rw [hFb ⟨E z,(hEb z).mp x.2⟩]
          change g (⟨(E.symm (E z)).1,_⟩,t)=g (x,t)
          simp only [E.symm_apply_apply]
          rfl
      have rel_cw_boundary_continuous (X : Type) [TopologicalSpace X] [T2Space X] (A : Set X)
          [RelCWComplex (Set.univ : Set X) A] (Z : Type) [TopologicalSpace Z]
          (F : X × I → Z) (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
          (hFA : Continuous (fun p : A × I => F (p.1,p.2)))
          (hF : ∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
            Continuous (fun p : (closedBall (0 : Fin m → ℝ) 1) × I =>
              F (RelCWComplex.map m j p.1,p.2))) :
          Continuous (fun p : (sphere (0 : Fin n → ℝ) 1) × I =>
            F (RelCWComplex.map n i p.1,p.2)) := by
        classical
        have hbase : ContinuousOn F (A ×ˢ (Set.univ : Set I)) := by
          apply continuousOn_iff_continuous_restrict.mpr
          exact hFA.comp (((continuous_fst.comp continuous_subtype_val).subtype_mk
            (fun p => p.2.1)).prodMk (continuous_snd.comp continuous_subtype_val))
        have hcell (m : ℕ) (hm : m < n) (j : RelCWComplex.cell (Set.univ : Set X) m) :
            ContinuousOn F ((RelCWComplex.closedCell m j) ×ˢ (Set.univ : Set I)) := by
          let c : C(closedBall (0 : Fin m → ℝ) 1,RelCWComplex.closedCell m j) :=
            ⟨fun z => ⟨RelCWComplex.map m j z,⟨z,z.property,rfl⟩⟩,
              (RelCWComplex.continuousOn m j).restrict.subtype_mk _⟩
          have hc : IsQuotientMap c := IsQuotientMap.of_surjective_continuous (by
            rintro ⟨x,z,hz,rfl⟩
            exact ⟨⟨z,hz⟩,rfl⟩) c.continuous
          have h : Continuous (fun p : (RelCWComplex.closedCell m j) × I => F (p.1,p.2)) :=
            hc.continuous_lift_prod_left (hF m hm j)
          apply continuousOn_iff_continuous_restrict.mpr
          exact h.comp (((continuous_fst.comp continuous_subtype_val).subtype_mk
            (fun p => p.2.1)).prodMk (continuous_snd.comp continuous_subtype_val))
        obtain ⟨J,hJ⟩ := RelCWComplex.mapsTo (C := (Set.univ : Set X)) n i
        let Ind := Σ m : Fin n, ↥(J m)
        let S : Option Ind → Set (X × I) :=
          fun o => o.elim (A ×ˢ Set.univ)
            (fun a => (RelCWComplex.closedCell a.1 a.2.1) ×ˢ Set.univ)
        have hS : ∀ a, IsClosed (S a) := by
          intro a
          cases a with
          | none => exact (RelCWComplex.isClosedBase (Set.univ : Set X)).prod isClosed_univ
          | some a => exact RelCWComplex.isClosed_closedCell.prod isClosed_univ
        have hcont : ContinuousOn F (⋃ a : Option Ind, S a) := by
          apply (locallyFinite_of_finite S).continuousOn_iUnion hS
          intro a
          cases a with
          | none => exact hbase
          | some a => exact hcell a.1 a.1.2 a.2.1
        let g : (sphere (0 : Fin n → ℝ) 1) × I → X × I :=
          fun p => (RelCWComplex.map n i p.1,p.2)
        have hg : Continuous g :=
          (((RelCWComplex.continuousOn n i).mono sphere_subset_closedBall).restrict.comp
            continuous_fst).prodMk continuous_snd
        have hmap : MapsTo g Set.univ (⋃ a : Option Ind, S a) := by
          intro p _
          rcases hJ p.1.2 with ha | hc
          · exact Set.mem_iUnion.mpr ⟨none, ha, trivial⟩
          · simp only [Set.mem_iUnion, exists_prop] at hc
            obtain ⟨m, hm, j, hj, hx⟩ := hc
            exact Set.mem_iUnion.mpr ⟨some ⟨⟨m, hm⟩, ⟨j, hj⟩⟩, hx, trivial⟩
        exact continuousOn_univ.mp (hcont.comp hg.continuousOn hmap)

      have rel_cw_extend_dimension
          (X : Type) [TopologicalSpace X] [T2Space X] (A : Set X)
          [RelCWComplex (Set.univ : Set X) A] (Z : Type) [TopologicalSpace Z]
          (f : C(X,Z)) (n : ℕ) (F : X × I → Z)
          (hF0 : ∀ x, F (x,0)=f x)
          (hFA : Continuous (fun p : A × I => F (p.1,p.2)))
          (hF : ∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
            Continuous (fun p : (closedBall (0 : Fin m → ℝ) 1) × I =>
              F (RelCWComplex.map m j p.1,p.2))) :
          ∃ G : X × I → Z,
            (∀ x, G (x,0)=f x) ∧
            (∀ x ∈ A, ∀ t, G (x,t)=F (x,t)) ∧
            (∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
              ∀ x ∈ RelCWComplex.closedCell m j, ∀ t, G (x,t)=F (x,t)) ∧
            (∀ i : RelCWComplex.cell (Set.univ : Set X) n,
              Continuous (fun p : (closedBall (0 : Fin n → ℝ) 1) × I =>
                G (RelCWComplex.map n i p.1,p.2))) := by
        classical
        have hExt (i : RelCWComplex.cell (Set.univ : Set X) n) :
            ∃ E : C((closedBall (0 : Fin n → ℝ) 1) × I,Z),
              (∀ z, E (z,0)=f (RelCWComplex.map n i z)) ∧
              (∀ (z : sphere (0 : Fin n → ℝ) 1) t,
                E (⟨z.1,sphere_subset_closedBall z.2⟩,t)=F (RelCWComplex.map n i z,t)) := by
          apply closedBall_boundary_hep n
            ⟨fun z => f (RelCWComplex.map n i z),
              f.continuous.comp (RelCWComplex.continuousOn n i).restrict⟩
            ⟨fun p => F (RelCWComplex.map n i p.1,p.2),rel_cw_boundary_continuous X A Z F n i hFA hF⟩
          exact fun z => hF0 _
        choose E hE0 hEb using hExt
        let New (x : X) := ∃ i : RelCWComplex.cell (Set.univ : Set X) n,
          x ∈ RelCWComplex.openCell n i
        have hinv (i : RelCWComplex.cell (Set.univ : Set X) n) {x : X}
            (hx : x ∈ RelCWComplex.openCell n i) :
            (RelCWComplex.map n i).symm x ∈ closedBall (0 : Fin n → ℝ) 1 := by
          have ht : x ∈ (RelCWComplex.map n i).target := by
            rw [← PartialEquiv.image_source_eq_target,RelCWComplex.source_eq]
            exact hx
          have hs := (RelCWComplex.map n i).map_target ht
          rw [RelCWComplex.source_eq] at hs
          exact ball_subset_closedBall hs
        let G : X × I → Z := fun p => if h : New p.1 then
          E (Classical.choose h) (⟨(RelCWComplex.map n (Classical.choose h)).symm p.1,
            hinv _ (Classical.choose_spec h)⟩,p.2) else F p
        have hopen {x : X} (i : RelCWComplex.cell (Set.univ : Set X) n)
            (hx : x ∈ RelCWComplex.openCell n i) (t : I) :
            G (x,t)=E i (⟨(RelCWComplex.map n i).symm x,hinv i hx⟩,t) := by
          have hnew : New x := ⟨i,hx⟩
          have hi : Classical.choose hnew=i := by
            by_contra h
            have hd := RelCWComplex.disjoint_openCell_of_ne
              (C := (Set.univ : Set X)) (n := n) (m := n)
              (i := Classical.choose hnew) (j := i) (by simpa using h)
            exact hd.le_bot ⟨Classical.choose_spec hnew,hx⟩
          dsimp only [G]
          rw [dif_pos hnew]
          subst hi
          rfl
        have hnone {x : X} (hx : x ∈ RelCWComplex.skeletonLT (Set.univ : Set X) n) :
            ¬New x := by
          rintro ⟨i,hi⟩
          exact (RelCWComplex.disjoint_skeletonLT_openCell (C := (Set.univ : Set X))
            (j := i) (le_refl (n : ℕ∞))).le_bot ⟨hx,hi⟩
        refine ⟨G,?_,?_,?_,?_⟩
        · intro x
          by_cases hx : New x
          · rw [hopen (Classical.choose hx) (Classical.choose_spec hx) 0,hE0]
            have ht : x ∈ (RelCWComplex.map n (Classical.choose hx)).target := by
              rw [← PartialEquiv.image_source_eq_target,RelCWComplex.source_eq]
              exact Classical.choose_spec hx
            rw [PartialEquiv.right_inv _ ht]
          · simp only [G,dif_neg hx,hF0]
        · intro x hx t
          have hn : ¬New x := by
            rintro ⟨i,hi⟩
            exact (RelCWComplex.disjointBase (C := (Set.univ : Set X)) n i).le_bot ⟨hi,hx⟩
          exact dif_neg hn
        · intro m hm j x hx t
          have hn : ¬New x := by
            rintro ⟨i,hi⟩
            exact (RelCWComplex.disjoint_skeleton_openCell (C := (Set.univ : Set X))
              (j := i) (ENat.coe_lt_coe.mpr hm)).le_bot
              ⟨RelCWComplex.closedCell_subset_skeleton m j hx,hi⟩
          exact dif_neg hn
        · intro i
          apply (E i).continuous.congr
          intro p
          by_cases hp : p.1.1 ∈ ball (0 : Fin n → ℝ) 1
          · have hx : RelCWComplex.map n i p.1 ∈ RelCWComplex.openCell n i :=
              ⟨p.1,hp,rfl⟩
            rw [hopen i hx p.2]
            have he : (RelCWComplex.map n i).symm (RelCWComplex.map n i p.1)=p.1 :=
              (RelCWComplex.map n i).left_inv (by rw [RelCWComplex.source_eq]; exact hp)
            exact congrArg (fun z : closedBall (0 : Fin n → ℝ) 1 => E i (z,p.2))
              (Subtype.ext he.symm)
          · have hs : p.1.1 ∈ sphere (0 : Fin n → ℝ) 1 := by
              rw [← closedBall_sdiff_ball]
              exact ⟨p.1.2,hp⟩
            have hx : RelCWComplex.map n i p.1 ∈
                RelCWComplex.skeletonLT (Set.univ : Set X) n :=
              RelCWComplex.cellFrontier_subset_skeletonLT n i ⟨p.1,hs,rfl⟩
            change E i p = G (RelCWComplex.map n i p.1,p.2)
            rw [show G (RelCWComplex.map n i p.1,p.2)=F (RelCWComplex.map n i p.1,p.2)
              from dif_neg (hnone hx)]
            exact hEb i ⟨p.1,hs⟩ p.2

      -- A direct continuity criterion replaces the old cw_cylinder_closed lemma.
      -- The domain includes A itself as well as every relative characteristic ball.
      have rel_cw_cylinder_continuous
          (X : Type) [TopologicalSpace X] [T2Space X] (A : Set X)
          [RelCWComplex (Set.univ : Set X) A] (Z : Type) [TopologicalSpace Z]
          (F : X × I → Z)
          (hFA : Continuous (fun p : A × I => F (p.1,p.2)))
          (hF : ∀ n (i : RelCWComplex.cell (Set.univ : Set X) n),
            Continuous (fun p : (closedBall (0 : Fin n → ℝ) 1) × I =>
              F (RelCWComplex.map n i p.1,p.2))) : Continuous F := by
        let Cells := Σ n : ℕ, Σ i : RelCWComplex.cell (Set.univ : Set X) n,
          closedBall (0 : Fin n → ℝ) 1
        let Dom := A ⊕ Cells
        let π : Dom → X := Sum.elim Subtype.val
          (fun a => RelCWComplex.map a.1 a.2.1 a.2.2)
        have hπcont : Continuous π := by
          apply continuous_sum_dom.mpr
          constructor
          · exact continuous_subtype_val
          · apply continuous_sigma
            intro n
            apply continuous_sigma
            intro i
            exact (RelCWComplex.continuousOn n i).restrict
        have hπsurj : Function.Surjective π := by
          intro x
          have hx : x ∈ A ∪ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
              RelCWComplex.closedCell n i := by
            rw [RelCWComplex.union]
            trivial
          rcases hx with hx | hx
          · exact ⟨Sum.inl ⟨x,hx⟩,rfl⟩
          · obtain ⟨n,i,z,hz,hzx⟩ := by
              simpa only [Set.mem_iUnion,RelCWComplex.closedCell,Set.mem_image] using hx
            exact ⟨Sum.inr ⟨n,i,z,hz⟩,hzx⟩
        have hπ : IsQuotientMap π := by
          apply isQuotientMap_iff_isClosed.mpr
          refine ⟨hπsurj,fun S => ⟨fun hS => hS.preimage hπcont,?_⟩⟩
          intro hS
          apply (RelCWComplex.closed (Set.univ : Set X) S (Set.subset_univ S)).mpr
          constructor
          · intro n i
            let c : C(closedBall (0 : Fin n → ℝ) 1,X) :=
              ⟨fun z => RelCWComplex.map n i z,(RelCWComplex.continuousOn n i).restrict⟩
            have hc : IsClosed (c ⁻¹' S) :=
              hS.preimage (continuous_inr.comp (continuous_sigmaMk.comp continuous_sigmaMk))
            have him : c '' (c ⁻¹' S)=S ∩ RelCWComplex.closedCell n i := by
              ext x
              constructor
              · rintro ⟨z,hz,rfl⟩
                exact ⟨hz,⟨z,z.property,rfl⟩⟩
              · rintro ⟨hx,z,hz,rfl⟩
                exact ⟨⟨z,hz⟩,hx,rfl⟩
            rw [← him]
            exact (hc.isCompact.image c.continuous).isClosed
          · let SA : Set A := {a | (a : X) ∈ S}
            have hc : IsClosed SA := hS.preimage continuous_inl
            have him : (fun a : A => (a : X)) '' SA=S ∩ A := by
              ext x
              constructor
              · rintro ⟨a,ha,rfl⟩
                exact ⟨ha,a.2⟩
              · rintro ⟨hxS,hxA⟩
                exact ⟨⟨x,hxA⟩,hxS,rfl⟩
            rw [← him]
            exact (RelCWComplex.isClosedBase (Set.univ : Set X)).isClosedMap_subtype_val SA hc
        apply hπ.continuous_lift_prod_left
        let e0 : Dom × I ≃ₜ (A × I) ⊕ (Cells × I) := Homeomorph.sumProdDistrib
        apply e0.symm.isQuotientMap.continuous_iff.mpr
        apply continuous_sum_dom.mpr
        constructor
        · exact hFA
        · let e : Cells × I ≃ₜ Σ n : ℕ,
              (Σ i : RelCWComplex.cell (Set.univ : Set X) n,
                closedBall (0 : Fin n → ℝ) 1) × I := Homeomorph.sigmaProdDistrib
          apply e.symm.isQuotientMap.continuous_iff.mpr
          apply continuous_sigma
          intro n
          let e' : (Σ i : RelCWComplex.cell (Set.univ : Set X) n,
              closedBall (0 : Fin n → ℝ) 1) × I ≃ₜ
              Σ i : RelCWComplex.cell (Set.univ : Set X) n,
                (closedBall (0 : Fin n → ℝ) 1) × I := Homeomorph.sigmaProdDistrib
          apply e'.symm.isQuotientMap.continuous_iff.mpr
          apply continuous_sigma
          intro i
          exact hF n i

      have relative_cw_hep
          (X : Type) [TopologicalSpace X] [T2Space X] (A : Set X)
          [RelCWComplex (Set.univ : Set X) A] (Z : Type) [TopologicalSpace Z]
          (f : C(X,Z)) (h : C(A × I,Z)) (h0 : ∀ a : A, h (a,0)=f a) :
          ∃ H : C(X × I,Z), (∀ x, H (x,0)=f x) ∧
            (∀ (a : A) t, H (a,t)=h (a,t)) := by
        classical
        let Pack (n : ℕ) := {F : X × I → Z //
          (∀ x, F (x,0)=f x) ∧ (∀ (a : A) t, F (a,t)=h (a,t)) ∧
          (∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
            Continuous (fun q : (closedBall (0 : Fin m → ℝ) 1) × I =>
              F (RelCWComplex.map m j q.1,q.2)))}
        let F0 : X × I → Z := fun q =>
          if hx : q.1 ∈ A then h (⟨q.1,hx⟩,q.2) else f q.1
        have hF00 : ∀ x, F0 (x,0)=f x := by
          intro x
          dsimp only [F0]
          split_ifs with hx
          · exact h0 ⟨x,hx⟩
          · rfl
        have hF0A : ∀ (a : A) t, F0 (a,t)=h (a,t) := by
          intro a t
          exact dif_pos a.2
        let init : Pack 0 := ⟨F0,hF00,hF0A,by
          intro m hm
          exact False.elim (Nat.not_lt_zero m hm)⟩
        have hstep (n : ℕ) (P : Pack n) : ∃ Q : Pack (n+1),
            ∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
              ∀ x ∈ RelCWComplex.closedCell m j, ∀ t, Q.1 (x,t)=P.1 (x,t) := by
          have hPA : Continuous (fun p : A × I => P.1 (p.1,p.2)) :=
            h.continuous.congr (fun p => (P.2.2.1 p.1 p.2).symm)
          obtain ⟨G,hG0,hGA,hGold,hGc⟩ :=
            rel_cw_extend_dimension X A Z f n P.1 P.2.1 hPA P.2.2.2
          refine ⟨⟨G,hG0,?_,?_⟩,hGold⟩
          · intro a t
            exact (hGA a a.2 t).trans (P.2.2.1 a t)
          · intro m hm j
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm | rfl
            · apply (P.2.2.2 m hm j).congr
              intro q
              exact (hGold m hm j _ ⟨q.1,q.1.2,rfl⟩ q.2).symm
            · exact hGc j
        let next (n : ℕ) (P : Pack n) : Pack (n+1) := Classical.choose (hstep n P)
        have hnext (n : ℕ) (P : Pack n) :
            ∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
              ∀ x ∈ RelCWComplex.closedCell m j, ∀ t,
                (next n P).1 (x,t)=P.1 (x,t) := Classical.choose_spec (hstep n P)
        let seq : (n : ℕ) → Pack n := fun n => Nat.rec init (fun n P => next n P) n
        have hseq (n : ℕ) : seq (n+1)=next n (seq n) := rfl
        have hstable (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) m)
            (x : X) (hx : x ∈ RelCWComplex.closedCell m i) (t : I)
            (a b : ℕ) (hma : m < a) (hab : a ≤ b) :
            (seq b).1 (x,t)=(seq a).1 (x,t) := by
          induction b,hab using Nat.le_induction with
          | base => rfl
          | succ b hab ih =>
              rw [hseq]
              exact (hnext b (seq b) m (hma.trans_le hab) i x hx t).trans ih
        have hcover (x : X) : ∃ n : ℕ,
            x ∈ A ∨ ∃ i : RelCWComplex.cell (Set.univ : Set X) n,
              x ∈ RelCWComplex.closedCell n i := by
          have hx : x ∈ A ∪ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
              RelCWComplex.closedCell n i := by
            rw [RelCWComplex.union]
            trivial
          rcases hx with hx | hx
          · exact ⟨0,Or.inl hx⟩
          · obtain ⟨n,i,hx⟩ := by simpa only [Set.mem_iUnion] using hx
            exact ⟨n,Or.inr ⟨i,hx⟩⟩
        choose dim hdim using hcover
        let H : X × I → Z := fun q => (seq (dim q.1+1)).1 q
        have hHcell (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) m)
            (x : X) (hx : x ∈ RelCWComplex.closedCell m i) (t : I) :
            H (x,t)=(seq (m+1)).1 (x,t) := by
          rcases hdim x with hxA | ⟨j,hxj⟩
          · exact ((seq (dim x+1)).2.2.1 ⟨x,hxA⟩ t).trans
              ((seq (m+1)).2.2.1 ⟨x,hxA⟩ t).symm
          · rcases le_total m (dim x) with hle | hle
            · exact hstable m i x hx t (m+1) (dim x+1)
                (Nat.lt_succ_self m) (Nat.succ_le_succ hle)
            · exact (hstable (dim x) j x hxj t (dim x+1) (m+1)
                (Nat.lt_succ_self (dim x)) (Nat.succ_le_succ hle)).symm
        have hH : Continuous H := by
          apply rel_cw_cylinder_continuous X A Z H
          · apply h.continuous.congr
            intro p
            exact ((seq (dim p.1+1)).2.2.1 p.1 p.2).symm
          · intro n i
            apply ((seq (n+1)).2.2.2 n (Nat.lt_succ_self n) i).congr
            intro q
            exact (hHcell n i _ ⟨q.1,q.1.2,rfl⟩ q.2).symm
        exact ⟨⟨H,hH⟩,
          fun x => (seq (dim x+1)).2.1 x,
          fun a t => (seq (dim a+1)).2.2.1 a t⟩
      exact relative_cw_hep X A Z f h h0
    have fat_pair_data (n : ℕ) :
        ∃ s : C(level n, fatLevel n),
          ∃ H : C(fatLevel n × I, fatLevel n), ∃ G : C(level n × I, level n),
            s (level n).point = (fatLevel n).point ∧
            (∀ x, H (x, 0) = x) ∧
            (∀ x, H (x, 1) = s (collapse n x)) ∧
            (∀ (x : zeroFat) t, H (zeroIncl n x, t) ∈ Set.range (zeroIncl n)) ∧
            (∀ x, G (x, 0) = x) ∧
            (∀ x, G (x, 1) = collapse n (s x)) ∧
            (∀ t, G ((level n).point, t) = (level n).point) := by
      letI := fat_t2 n
      letI := Classical.choice (fat_relative_cw n)
      let A := Set.range (zeroIncl n)
      let e : zeroFat ≃ₜ A := (zeroIncl_closed n).isEmbedding.toHomeomorph
      let g : C(A × I, fatLevel n) :=
        ⟨fun p => zeroIncl n (zeroContraction (e.symm p.1, p.2)),
          (zeroIncl n).continuous.comp (zeroContraction.continuous.comp
            ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))⟩
      have he (x : A) : zeroIncl n (e.symm x) = x.1 :=
        congrArg Subtype.val (e.apply_symm_apply x)
      have hg (x : A) : g (x, 0) = (ContinuousMap.id (fatLevel n)) x.1 := by
        change zeroIncl n (zeroContraction (e.symm x, 0)) = x.1
        rw [zeroContraction_zero, he]
      obtain ⟨H, hH0, hHA⟩ := relative_cw_hep (fatLevel n) A (fatLevel n)
        (ContinuousMap.id (fatLevel n)) g hg
      have hHA' (x : zeroFat) (t : I) :
          H (zeroIncl n x, t) = zeroIncl n (zeroContraction (x, t)) := by
        have h := hHA (e x) t
        change H (zeroIncl n x, t) = zeroIncl n (zeroContraction (e.symm (e x), t)) at h
        simpa only [e.symm_apply_apply] using h
      obtain ⟨s, hs0, hs, hHr, G, hG0, hG1, hGb⟩ := fat_pair_from_extension n H hH0 hHA'
      exact ⟨s, H, G, hs0, hH0, hs, hHr, hG0, hG1, hGb⟩
    -- A4: z + δ(b ⌣ λ), with the time zero-cochain at the last vertex.
    let cochainHomotopyLabel (n q : ℕ) (z : K (n + 1) q)
        (b : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2)
        (hb : ∀ a : Fin (n + 1) →o Fin (q + 1), ¬ Function.Injective a → b a = 0)
        (t : Fin (q + 1) → ZMod 2) : K (n + 1) q := by
      let v : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2 := fun a => b a * t (a (Fin.last n))
      have hv : ∀ a : Fin (n + 1) →o Fin (q + 1), ¬ Function.Injective a → v a = 0 := by
        intro a ha
        change b a * t (a (Fin.last n)) = 0
        rw [hb a ha, zero_mul]
      refine ⟨fun a => z.1 a + delta n q v a, ?_, ?_⟩
      · intro a ha
        change z.1 a + delta n q v a = 0
        rw [z.2.1 a ha, zero_add]
        exact normalized_delta_degenerate v hv a ha
      · intro a
        rw [Finset.sum_add_distrib, z.2.2 a, zero_add]
        exact congrFun (delta_sq n q v) a
    have cochain_pull_normalized {n p q : ℕ} (a : Fin (p + 1) →o Fin (q + 1))
        (b : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2)
        (hb : ∀ s : Fin (n + 1) →o Fin (q + 1), ¬ Function.Injective s → b s = 0) :
        ∀ s : Fin (n + 1) →o Fin (p + 1), ¬ Function.Injective s → b (a.comp s) = 0 := by
      intro s hs
      apply hb
      intro hinj
      exact hs (fun i j hij => hinj (congrArg a hij))
    have cochainHomotopyLabel_natural {n p q : ℕ} (a : Fin (p + 1) →o Fin (q + 1))
        (z : K (n + 1) q) (b : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2)
        (hb : ∀ s : Fin (n + 1) →o Fin (q + 1), ¬ Function.Injective s → b s = 0)
        (t : Fin (q + 1) → ZMod 2) :
        pull a (cochainHomotopyLabel n q z b hb t) =
          cochainHomotopyLabel n p (pull a z) (fun s => b (a.comp s))
            (cochain_pull_normalized a b hb) (fun i => t (a i)) := by
      apply Subtype.ext
      funext s
      rfl
    have cochainHomotopyLabel_zero_time (n q : ℕ) (z : K (n + 1) q)
        (b : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2)
        (hb : ∀ a : Fin (n + 1) →o Fin (q + 1), ¬ Function.Injective a → b a = 0) :
        cochainHomotopyLabel n q z b hb (fun _ => 0) = z := by
      apply Subtype.ext
      funext a
      simp [cochainHomotopyLabel, delta]
    have cochainHomotopyLabel_one_time (n q : ℕ) (z w : K (n + 1) q)
        (b : (Fin (n + 1) →o Fin (q + 1)) → ZMod 2)
        (hb : ∀ a : Fin (n + 1) →o Fin (q + 1), ¬ Function.Injective a → b a = 0)
        (hw : ∀ a, z.1 a + delta n q b a = w.1 a) :
        cochainHomotopyLabel n q z b hb (fun _ => 1) = w := by
      apply Subtype.ext
      funext a
      simpa only [cochainHomotopyLabel, delta, mul_one] using hw a
    have cochainHomotopyLabel_zero (n q : ℕ) (t : Fin (q + 1) → ZMod 2) :
        cochainHomotopyLabel n q (zero (n + 1) q) (fun _ => 0) (by intros; rfl) t =
          zero (n + 1) q := by
      apply Subtype.ext
      funext a
      simp [cochainHomotopyLabel, delta, zero]
    -- T1: the vertices of one barycentric subdivision are nonempty original faces.
    let Face (q : ℕ) := {S : Finset (Fin (q + 1)) // S.Nonempty}
    letI (q : ℕ) : Fintype (Face q) := by
      dsimp only [Face]
      infer_instance
    let barycenter (q : ℕ) (S : Face q) : Simplex q :=
      ⟨fun i => if i ∈ S.1 then (S.1.card : ℝ)⁻¹ else 0, by
        constructor
        · intro i
          dsimp only
          split_ifs
          · exact inv_nonneg.mpr (Nat.cast_nonneg _)
          · exact le_refl 0
        · have hc : (S.1.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr S.2))
          simp [Finset.sum_ite, hc]⟩
    let faceImage {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) (S : Face p) : Face q :=
      ⟨S.1.map a.toEmbedding, S.2.map⟩
    have barycenter_face {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) (S : Face p) :
        barycenter q (faceImage a S) = simplexMap a.toOrderHom (barycenter p S) := by
      apply Subtype.ext
      funext j
      by_cases hj : j ∈ Set.range a
      · obtain ⟨i, rfl⟩ := hj
        rw [simplexMap_apply_image a (barycenter p S) i]
        simp [barycenter, faceImage]
      · rw [simplexMap_apply_outside a (barycenter p S) j hj]
        have hn : j ∉ S.1.map a.toEmbedding := by
          intro h
          obtain ⟨i, hi, hije⟩ := Finset.mem_map.mp h
          exact hj ⟨i, hije⟩
        exact if_neg hn
    have barycenter_positive (q : ℕ) (S : Face q) (i : Fin (q + 1)) :
        0 < (barycenter q S).1 i ↔ i ∈ S.1 := by
      change 0 < (if i ∈ S.1 then (S.1.card : ℝ)⁻¹ else 0) ↔ i ∈ S.1
      by_cases hi : i ∈ S.1
      · simp only [hi, ↓reduceIte, iff_true]
        exact inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr S.2))
      · simp [hi]
    -- Continuous coordinates of the subdivision, without choosing an order of tied vertices.
    let faceLower (q : ℕ) (S : Face q) (u : Simplex q) : ℝ := S.1.inf' S.2 u.1
    let faceUpper (q : ℕ) (S : Face q) (u : Simplex q) : ℝ :=
      Finset.univ.sup' Finset.univ_nonempty (fun i => if i ∈ S.1 then 0 else u.1 i)
    let baryWeight (q : ℕ) (S : Face q) (u : Simplex q) : ℝ :=
      (S.1.card : ℝ) * max 0 (faceLower q S u - faceUpper q S u)
    have faceLower_continuous (q : ℕ) (S : Face q) : Continuous (faceLower q S) := by
      exact Continuous.finset_inf'_apply S.2
        (fun i _ => (continuous_apply i).comp continuous_subtype_val)
    have faceUpper_continuous (q : ℕ) (S : Face q) : Continuous (faceUpper q S) := by
      apply Continuous.finset_sup'_apply Finset.univ_nonempty
      intro i _
      by_cases hi : i ∈ S.1
      · simpa only [if_pos hi] using (continuous_const : Continuous (fun _ : Simplex q => (0 : ℝ)))
      · simp only [if_neg hi]
        exact (continuous_apply i).comp continuous_subtype_val
    have baryWeight_continuous (q : ℕ) (S : Face q) : Continuous (baryWeight q S) :=
      continuous_const.mul (continuous_const.max
        ((faceLower_continuous q S).sub (faceUpper_continuous q S)))
    have faceLower_le (q : ℕ) (S : Face q) (u : Simplex q) (i : Fin (q + 1)) (hi : i ∈ S.1) :
        faceLower q S u ≤ u.1 i := Finset.inf'_le u.1 hi
    have le_faceUpper (q : ℕ) (S : Face q) (u : Simplex q) (i : Fin (q + 1)) (hi : i ∉ S.1) :
        u.1 i ≤ faceUpper q S u := by
      have h := Finset.le_sup' (fun i => if i ∈ S.1 then (0 : ℝ) else u.1 i) (Finset.mem_univ i)
      simpa only [if_neg hi] using h
    have faceUpper_nonneg (q : ℕ) (S : Face q) (u : Simplex q) : 0 ≤ faceUpper q S u := by
      have h := Finset.le_sup' (fun i => if i ∈ S.1 then (0 : ℝ) else u.1 i)
        (Finset.mem_univ (0 : Fin (q + 1)))
      by_cases hi : (0 : Fin (q + 1)) ∈ S.1
      · simpa only [if_pos hi] using h
      · exact (u.2.1 0).trans (by simpa only [if_neg hi] using h)
    have baryWeight_nonneg (q : ℕ) (S : Face q) (u : Simplex q) : 0 ≤ baryWeight q S u :=
      mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)
    have baryWeight_pos (q : ℕ) (S : Face q) (u : Simplex q) :
        0 < baryWeight q S u ↔ faceUpper q S u < faceLower q S u := by
      have hc : (0 : ℝ) < S.1.card := Nat.cast_pos.mpr (Finset.card_pos.mpr S.2)
      change 0 < (S.1.card : ℝ) * max 0 (faceLower q S u - faceUpper q S u) ↔ _
      rw [mul_pos_iff_of_pos_left hc, lt_max_iff]
      simp only [lt_self_iff_false, false_or, sub_pos]
    have baryWeight_comparable (q : ℕ) (S T : Face q) (u : Simplex q)
        (hS : 0 < baryWeight q S u) (hT : 0 < baryWeight q T u) : S.1 ⊆ T.1 ∨ T.1 ⊆ S.1 := by
      by_cases hST : S.1 ⊆ T.1
      · exact Or.inl hST
      by_cases hTS : T.1 ⊆ S.1
      · exact Or.inr hTS
      obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hST
      obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.mp hTS
      have h1 := (baryWeight_pos q S u).mp hS
      have h2 := (baryWeight_pos q T u).mp hT
      have h3 := faceLower_le q S u i hiS
      have h4 := le_faceUpper q T u i hiT
      have h5 := faceLower_le q T u j hjT
      have h6 := le_faceUpper q S u j hjS
      linarith
    have faceLower_face {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (S : Face p) (u : Simplex p) :
        faceLower q (faceImage a S) (simplexMap a.toOrderHom u) = faceLower p S u := by
      change (S.1.map a.toEmbedding).inf' _ (simplexMap a.toOrderHom u).1 = S.1.inf' S.2 u.1
      rw [Finset.inf'_map]
      congr 1
      funext i
      exact simplexMap_apply_image a u i
    have faceUpper_face {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (S : Face p) (u : Simplex p) :
        faceUpper q (faceImage a S) (simplexMap a.toOrderHom u) = faceUpper p S u := by
      have hterm (i : Fin (p + 1)) :
          (if a i ∈ (faceImage a S).1 then (0 : ℝ) else (simplexMap a.toOrderHom u).1 (a i)) =
            if i ∈ S.1 then 0 else u.1 i := by
        rw [simplexMap_apply_image]
        simp [faceImage]
      apply le_antisymm
      · apply Finset.sup'_le
        intro j _
        by_cases hj : j ∈ Set.range a
        · obtain ⟨i, rfl⟩ := hj
          rw [hterm]
          exact Finset.le_sup' (fun k : Fin (p + 1) => if k ∈ S.1 then (0 : ℝ) else u.1 k)
            (Finset.mem_univ i)
        · have hn : j ∉ (faceImage a S).1 := by
            intro h
            obtain ⟨i, hi, hije⟩ := Finset.mem_map.mp h
            exact hj ⟨i, hije⟩
          rw [if_neg hn, simplexMap_apply_outside a u j hj]
          exact faceUpper_nonneg p S u
      · apply Finset.sup'_le
        intro i _
        rw [← hterm i]
        exact Finset.le_sup' (fun k : Fin (q + 1) => if k ∈ (faceImage a S).1 then (0 : ℝ)
          else (simplexMap a.toOrderHom u).1 k) (Finset.mem_univ (a i))
    have baryWeight_face {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (S : Face p) (u : Simplex p) :
        baryWeight q (faceImage a S) (simplexMap a.toOrderHom u) = baryWeight p S u := by
      dsimp only [baryWeight]
      rw [faceLower_face, faceUpper_face]
      simp only [faceImage, Finset.card_map]
    have faceLower_nonneg (q : ℕ) (S : Face q) (u : Simplex q) : 0 ≤ faceLower q S u := by
      apply Finset.le_inf'
      intro i _
      exact u.2.1 i
    have baryWeight_zero_of_coordinate_zero (q : ℕ) (S : Face q) (u : Simplex q)
        (i : Fin (q + 1)) (hi : i ∈ S.1) (hu : u.1 i = 0) : baryWeight q S u = 0 := by
      have hl : faceLower q S u = 0 := le_antisymm
        (hu ▸ faceLower_le q S u i hi) (faceLower_nonneg q S u)
      dsimp only [baryWeight]
      rw [hl, max_eq_left (by linarith [faceUpper_nonneg q S u]), mul_zero]
    have baryWeight_threshold (q : ℕ) (S : Face q) (u : Simplex q)
        (hS : 0 < baryWeight q S u) :
        S.1 = Finset.univ.filter (fun i => faceLower q S u ≤ u.1 i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact faceLower_le q S u i
      · intro hi
        by_contra hn
        have hg := (baryWeight_pos q S u).mp hS
        have ho := le_faceUpper q S u i hn
        linarith
    have baryWeight_positive_coordinates (q : ℕ) (S : Face q) (u : Simplex q)
        (hS : 0 < baryWeight q S u) (i : Fin (q + 1)) (hi : i ∈ S.1) : 0 < u.1 i := by
      exact lt_of_lt_of_le
        (lt_of_le_of_lt (faceUpper_nonneg q S u) ((baryWeight_pos q S u).mp hS))
        (faceLower_le q S u i hi)
    have faceLower_attained (q : ℕ) (S : Face q) (u : Simplex q) :
        ∃ i ∈ S.1, faceLower q S u = u.1 i :=
      Finset.exists_mem_eq_inf' S.2 u.1
    have faceImage_injective {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) :
        Function.Injective (faceImage a) := by
      intro S T h
      apply Subtype.ext
      exact Finset.map_injective a.toEmbedding (congrArg Subtype.val h)
    have baryWeight_face_outside {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (S : Face q) (u : Simplex p) (i : Fin (q + 1))
        (hi : i ∈ S.1) (hai : i ∉ Set.range a) :
        baryWeight q S (simplexMap a.toOrderHom u) = 0 :=
      baryWeight_zero_of_coordinate_zero q S (simplexMap a.toOrderHom u) i hi
        (simplexMap_apply_outside a u i hai)
    have baryWeight_face_support {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (S : Face q) (u : Simplex p) (hS : 0 < baryWeight q S (simplexMap a.toOrderHom u)) :
        ∃ T : Face p, faceImage a T = S := by
      have hr (j : Fin (q + 1)) (hj : j ∈ S.1) : j ∈ Set.range a := by
        by_contra hn
        rw [baryWeight_face_outside a S u j hj hn] at hS
        exact lt_irrefl 0 hS
      let T := Finset.univ.filter (fun i => a i ∈ S.1)
      have hT : T.Nonempty := by
        obtain ⟨j, hj⟩ := S.2
        obtain ⟨i, rfl⟩ := hr j hj
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hj⟩⟩
      refine ⟨⟨T, hT⟩, ?_⟩
      apply Subtype.ext
      ext j
      change j ∈ T.map a.toEmbedding ↔ j ∈ S.1
      constructor
      · intro hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
        exact (Finset.mem_filter.mp hi).2
      · intro hj
        obtain ⟨i, rfl⟩ := hr j hj
        exact Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hj⟩, rfl⟩
    let chainBary (q r : ℕ) (C : Fin (r + 1) → Face q) (u : Simplex r) : Simplex q :=
      ⟨fun v => ∑ i, u.1 i * (barycenter q (C i)).1 v, by
        constructor
        · intro v
          exact Finset.sum_nonneg (fun i _ => mul_nonneg (u.2.1 i) ((barycenter q (C i)).2.1 v))
        · rw [Finset.sum_comm]
          simp_rw [← Finset.mul_sum, (barycenter q (C _)).2.2, mul_one]
          exact u.2.2⟩
    have chainBary_continuous (q r : ℕ) (C : Fin (r + 1) → Face q) :
        Continuous (chainBary q r C) := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro v
      exact continuous_finsetSum _ (fun i _ =>
        ((continuous_apply i).comp continuous_subtype_val).mul continuous_const)
    have chainBary_apply (q r : ℕ) (C : Fin (r + 1) → Face q) (u : Simplex r)
        (v : Fin (q + 1)) :
        (chainBary q r C u).1 v = ∑ i, if v ∈ (C i).1 then u.1 i / ((C i).1.card : ℝ) else 0 := by
      dsimp only [chainBary]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [barycenter]
      split_ifs <;> simp [div_eq_mul_inv]
    have chain_mono (q r : ℕ) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) :
        ∀ i j, i ≤ j → (C i).1 ⊆ (C j).1 := by
      intro i j hij
      rcases lt_or_eq_of_le hij with h | rfl
      · exact (hC i j h).1
      · exact Finset.Subset.refl _
    have chain_new_vertex (q r : ℕ) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) (i : Fin (r + 1)) :
        ∃ v : Fin (q + 1), ∀ j, v ∈ (C j).1 ↔ i ≤ j := by
      refine Fin.cases ?_ (fun k => ?_) i
      · obtain ⟨v, hv⟩ := (C 0).2
        exact ⟨v, fun j => ⟨fun _ => Fin.zero_le j,
          fun hj => chain_mono q r C hC 0 j hj hv⟩⟩
      · obtain ⟨v, hv, hnot⟩ := Finset.exists_of_ssubset (hC k.castSucc k.succ (by simp))
        refine ⟨v, fun j => ⟨?_, ?_⟩⟩
        · intro hj
          by_contra h
          have hvj : ¬ k.val + 1 ≤ j.val := h
          exact hnot (chain_mono q r C hC j k.castSucc (by simpa only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] using (by omega : j.val ≤ k.val)) hj)
        · intro hj
          exact chain_mono q r C hC k.succ j hj hv
    have chainBary_lower (q r : ℕ) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) (u : Simplex r) (i : Fin (r + 1)) :
        faceLower q (C i) (chainBary q r C u) =
          ∑ j, if i ≤ j then u.1 j / ((C j).1.card : ℝ) else 0 := by
      have hnonneg (j : Fin (r + 1)) : 0 ≤ u.1 j / ((C j).1.card : ℝ) :=
        div_nonneg (u.2.1 j) (Nat.cast_nonneg _)
      apply le_antisymm
      · obtain ⟨v, hv⟩ := chain_new_vertex q r C hC i
        refine (faceLower_le q (C i) (chainBary q r C u) v ((hv i).mpr le_rfl)).trans ?_
        rw [chainBary_apply]
        simp only [hv, le_refl]
      · apply Finset.le_inf'
        intro v hv
        rw [chainBary_apply]
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i ≤ j
        · rw [if_pos hij, if_pos (chain_mono q r C hC i j hij hv)]
        · rw [if_neg hij]
          split_ifs
          · exact hnonneg j
          · exact le_refl 0
    have chainBary_upper (q r : ℕ) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) (u : Simplex r) (i : Fin (r + 1)) :
        faceUpper q (C i) (chainBary q r C u) =
          ∑ j, if i < j then u.1 j / ((C j).1.card : ℝ) else 0 := by
      have hnonneg (j : Fin (r + 1)) : 0 ≤ u.1 j / ((C j).1.card : ℝ) :=
        div_nonneg (u.2.1 j) (Nat.cast_nonneg _)
      have hsum : 0 ≤ ∑ j, if i < j then u.1 j / ((C j).1.card : ℝ) else 0 :=
        Finset.sum_nonneg (fun j _ => by
          split_ifs
          · exact hnonneg j
          · exact le_refl 0)
      apply le_antisymm
      · apply Finset.sup'_le
        intro v _
        split_ifs with hv
        · exact hsum
        · rw [chainBary_apply]
          apply Finset.sum_le_sum
          intro j _
          by_cases hij : i < j
          · rw [if_pos hij]
            split_ifs
            · exact le_refl _
            · exact hnonneg j
          · have hnot : v ∉ (C j).1 := fun hj => hv (chain_mono q r C hC j i (by omega) hj)
            rw [if_neg hij, if_neg hnot]
      · revert hsum
        refine Fin.lastCases ?_ (fun k => ?_) i
        · intro _
          have hj : ∀ j : Fin (r + 1), ¬ Fin.last r < j := fun j => not_lt.mpr (Fin.le_last j)
          simpa only [hj, ↓reduceIte, Finset.sum_const_zero] using
            faceUpper_nonneg q (C (Fin.last r)) (chainBary q r C u)
        · intro _
          obtain ⟨v, hv⟩ := chain_new_vertex q r C hC k.succ
          have hnot : v ∉ (C k.castSucc).1 := fun h => (by simp : ¬ k.succ ≤ k.castSucc) ((hv _).mp h)
          refine le_trans ?_ (le_faceUpper q (C k.castSucc) (chainBary q r C u) v hnot)
          rw [chainBary_apply]
          apply le_of_eq
          apply Finset.sum_congr rfl
          intro j _
          have hiff : k.succ ≤ j ↔ k.castSucc < j := by
            change k.val + 1 ≤ j.val ↔ k.val < j.val
            omega
          simp only [hv j, hiff]
    have baryWeight_chain (q r : ℕ) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) (u : Simplex r) (i : Fin (r + 1)) :
        baryWeight q (C i) (chainBary q r C u) = u.1 i := by
      have hsplit :
          (∑ j, if i ≤ j then u.1 j / ((C j).1.card : ℝ) else 0) =
          u.1 i / ((C i).1.card : ℝ) +
            ∑ j, if i < j then u.1 j / ((C j).1.card : ℝ) else 0 := by
        have hterm (j : Fin (r + 1)) :
            (if i ≤ j then u.1 j / ((C j).1.card : ℝ) else 0) =
            (if j = i then u.1 j / ((C j).1.card : ℝ) else 0) +
              (if i < j then u.1 j / ((C j).1.card : ℝ) else 0) := by
          by_cases he : j = i
          · subst j
            simp
          · by_cases hij : i < j
            · simp [he, hij, hij.le]
            · simp [he, hij, show ¬ i ≤ j by omega]
        simp_rw [hterm, Finset.sum_add_distrib]
        simp
      have hc : (0 : ℝ) < (C i).1.card := Nat.cast_pos.mpr (Finset.card_pos.mpr (C i).2)
      dsimp only [baryWeight]
      rw [chainBary_lower q r C hC, chainBary_upper q r C hC, hsplit, add_sub_cancel_right,
        max_eq_right (div_nonneg (u.2.1 i) hc.le)]
      field_simp
    have chainBary_face {p q r : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (C : Fin (r + 1) → Face p) (u : Simplex r) :
        chainBary q r (fun i => faceImage a (C i)) u =
          simplexMap a.toOrderHom (chainBary p r C u) := by
      apply Subtype.ext
      funext v
      by_cases hv : v ∈ Set.range a
      · obtain ⟨j, rfl⟩ := hv
        rw [simplexMap_apply_image]
        change (∑ i, u.1 i * (barycenter q (faceImage a (C i))).1 (a j)) =
          ∑ i, u.1 i * (barycenter p (C i)).1 j
        simp_rw [barycenter_face, simplexMap_apply_image]
      · rw [simplexMap_apply_outside a (chainBary p r C u) v hv]
        change (∑ i, u.1 i * (barycenter q (faceImage a (C i))).1 v) = 0
        simp_rw [barycenter_face, simplexMap_apply_outside a _ v hv, mul_zero, Finset.sum_const_zero]
    have chainBary_chainface {q r s : ℕ} (a : Fin (s + 1) ↪o Fin (r + 1))
        (C : Fin (r + 1) → Face q) (u : Simplex s) :
        chainBary q r C (simplexMap a.toOrderHom u) = chainBary q s (fun i => C (a i)) u := by
      apply Subtype.ext
      funext v
      change (∑ j, (∑ i, if a i = j then u.1 i else 0) * (barycenter q (C j)).1 v) =
        ∑ i, u.1 i * (barycenter q (C (a i))).1 v
      simp_rw [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      simp

    -- Sort the distinct positive coordinate values, not the vertices.
    have simplex_positive_levels (q : ℕ) (u : Simplex q) :
        ∃ k : ℕ, ∃ c : Fin (k + 1) → ℝ,
          StrictAnti c ∧ (∀ j, 0 < c j) ∧
          (∀ j, ∃ v : Fin (q + 1), u.1 v = c j) ∧
          (∀ v : Fin (q + 1), 0 < u.1 v → ∃ j, c j = u.1 v) := by
      let S : Finset ℝ := (Finset.univ.image u.1).filter (fun x => 0 < x)
      have hpositive : ∃ v : Fin (q + 1), 0 < u.1 v := by
        by_contra hn
        have hz : ∀ v : Fin (q + 1), u.1 v = 0 := by
          intro v
          apply le_antisymm
          · exact le_of_not_gt (fun hv => hn ⟨v, hv⟩)
          · exact u.2.1 v
        have hs := u.2.2
        simp [hz] at hs
      have hS : S.Nonempty := by
        obtain ⟨v, hv⟩ := hpositive
        exact ⟨u.1 v, Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩, hv⟩⟩
      let k := S.card - 1
      have hk : S.card = k + 1 := by
        have hcard := Finset.card_pos.mpr hS
        dsimp only [k]
        omega
      let e : Fin (k + 1) ↪o ℝ := S.orderEmbOfFin hk
      let c : Fin (k + 1) → ℝ := fun j => e j.rev
      have hmem (j : Fin (k + 1)) : c j ∈ S :=
        Finset.orderEmbOfFin_mem S hk j.rev
      refine ⟨k, c, ?_, ?_, ?_, ?_⟩
      · intro i j hij
        exact e.strictMono (Fin.rev_lt_rev.mpr hij)
      · intro j
        exact (Finset.mem_filter.mp (hmem j)).2
      · intro j
        obtain ⟨v, hv, hvc⟩ := Finset.mem_image.mp
          (Finset.mem_filter.mp (hmem j)).1
        exact ⟨v, hvc⟩
      · intro v hv
        have hvS : u.1 v ∈ S := Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩, hv⟩
        have hrange : u.1 v ∈ Set.range e := by
          rw [show Set.range e = (S : Set ℝ) from Finset.range_orderEmbOfFin S hk]
          exact hvS
        obtain ⟨j, hj⟩ := hrange
        refine ⟨j.rev, ?_⟩
        simpa only [c, Fin.rev_rev] using hj

    let thresholdFace {q k : ℕ} (u : Simplex q) (c : Fin (k + 1) → ℝ)
        (hc : ∀ j, ∃ v : Fin (q + 1), u.1 v = c j)
        (j : Fin (k + 1)) : Face q :=
      ⟨Finset.univ.filter (fun v => c j ≤ u.1 v), by
        obtain ⟨v, hv⟩ := hc j
        exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv.ge⟩⟩⟩
    have mem_thresholdFace {q k : ℕ} (u : Simplex q) (c : Fin (k + 1) → ℝ)
        (hc : ∀ j, ∃ v : Fin (q + 1), u.1 v = c j)
        (j : Fin (k + 1)) (v : Fin (q + 1)) :
        v ∈ (thresholdFace u c hc j).1 ↔ c j ≤ u.1 v := by
      simp only [thresholdFace, Finset.mem_filter, Finset.mem_univ, true_and]
    have thresholdFace_strict {q k : ℕ} (u : Simplex q) (c : Fin (k + 1) → ℝ)
        (hc : ∀ j, ∃ v : Fin (q + 1), u.1 v = c j)
        (hanti : StrictAnti c) (i j : Fin (k + 1)) (hij : i < j) :
        (thresholdFace u c hc i).1 ⊂ (thresholdFace u c hc j).1 := by
      have hsub : (thresholdFace u c hc i).1 ⊆ (thresholdFace u c hc j).1 := by
        intro v hv
        apply (mem_thresholdFace u c hc j v).mpr
        exact (hanti hij).le.trans ((mem_thresholdFace u c hc i v).mp hv)
      apply (Finset.ssubset_iff_of_subset hsub).mpr
      obtain ⟨v, hv⟩ := hc j
      refine ⟨v, (mem_thresholdFace u c hc j v).mpr hv.ge, ?_⟩
      intro hiv
      have hle := (mem_thresholdFace u c hc i v).mp hiv
      rw [hv] at hle
      exact (not_le_of_gt (hanti hij)) hle

    -- The appended zero handles the final gap and the zero-coordinate face.
    let thresholdGap (k : ℕ) (c : Fin (k + 1) → ℝ) (i : Fin (k + 1)) : ℝ :=
      c i - Fin.snoc (α := fun _ => ℝ) c 0 i.succ
    have thresholdGap_pos (k : ℕ) (c : Fin (k + 1) → ℝ)
        (hanti : StrictAnti c) (hpos : ∀ i, 0 < c i) (i : Fin (k + 1)) :
        0 < thresholdGap k c i := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [thresholdGap, Fin.succ_last, Fin.snoc_last, sub_zero] using
          hpos (Fin.last k)
      · dsimp only [thresholdGap]
        rw [Fin.succ_castSucc, Fin.snoc_castSucc]
        exact sub_pos.mpr (hanti Fin.castSucc_lt_succ)
    have thresholdGap_sum_tail (k : ℕ) (c : Fin (k + 1) → ℝ)
        (i : Fin (k + 1)) :
        (∑ j ∈ Finset.Icc i (Fin.last k), thresholdGap k c j) = c i := by
      simpa only [thresholdGap, Fin.snoc_castSucc, Fin.succ_last,
        Fin.snoc_last, neg_sub_neg, sub_zero] using
        (Fin.sum_Icc_sub (a := i) (b := Fin.last k) (Fin.le_last i)
          (fun j : Fin ((k + 1) + 1) => -(Fin.snoc (α := fun _ => ℝ) c 0 j)))
    have thresholdGap_sum_ite (k : ℕ) (c : Fin (k + 1) → ℝ)
        (i : Fin (k + 1)) :
        (∑ j, if i ≤ j then thresholdGap k c j else 0) = c i := by
      calc
        (∑ j, if i ≤ j then thresholdGap k c j else 0) =
            ∑ j ∈ Finset.Icc i (Fin.last k), thresholdGap k c j := by
          simpa only [Finset.mem_Icc, Fin.le_last, and_true] using
            (Finset.sum_ite_mem_eq (Finset.Icc i (Fin.last k)) (thresholdGap k c))
        _ = c i := thresholdGap_sum_tail k c i

    have threshold_reconstruct {q k : ℕ} (u : Simplex q) (c : Fin (k + 1) → ℝ)
        (hc : ∀ j, ∃ v : Fin (q + 1), u.1 v = c j)
        (hanti : StrictAnti c) (hpos : ∀ j, 0 < c j)
        (hcover : ∀ v : Fin (q + 1), 0 < u.1 v → ∃ j, c j = u.1 v)
        (v : Fin (q + 1)) :
        (∑ j, if v ∈ (thresholdFace u c hc j).1 then thresholdGap k c j else 0) =
          u.1 v := by
      by_cases hv : 0 < u.1 v
      · obtain ⟨i, hi⟩ := hcover v hv
        have hmem (j : Fin (k + 1)) :
            v ∈ (thresholdFace u c hc j).1 ↔ i ≤ j := by
          rw [mem_thresholdFace u c hc j v, ← hi]
          exact hanti.le_iff_ge
        calc
          (∑ j, if v ∈ (thresholdFace u c hc j).1 then thresholdGap k c j else 0) =
              ∑ j, if i ≤ j then thresholdGap k c j else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [hmem j]
          _ = c i := thresholdGap_sum_ite k c i
          _ = u.1 v := hi
      · have hz : u.1 v = 0 := le_antisymm (le_of_not_gt hv) (u.2.1 v)
        have hn (j : Fin (k + 1)) : v ∉ (thresholdFace u c hc j).1 := by
          intro hj
          have hle := (mem_thresholdFace u c hc j v).mp hj
          rw [hz] at hle
          exact (not_le_of_gt (hpos j)) hle
        rw [hz]
        apply Finset.sum_eq_zero
        intro j hj
        exact if_neg (hn j)

    have thresholdFace_covers_weights {q k : ℕ} (u : Simplex q) (c : Fin (k + 1) → ℝ)
        (hc : ∀ j, ∃ v : Fin (q + 1), u.1 v = c j)
        (hcover : ∀ v : Fin (q + 1), 0 < u.1 v → ∃ j, c j = u.1 v)
        (S : Face q) (hS : 0 < baryWeight q S u) : ∃ j, thresholdFace u c hc j = S := by
      obtain ⟨v, hv, he⟩ := faceLower_attained q S u
      obtain ⟨j, hj⟩ := hcover v (baryWeight_positive_coordinates q S u hS v hv)
      have hj' : c j = faceLower q S u := hj.trans he.symm
      refine ⟨j, Subtype.ext ?_⟩
      rw [baryWeight_threshold q S u hS]
      change Finset.univ.filter (fun v => c j ≤ u.1 v) = _
      rw [hj']
    -- Convert the gap parameters into positive simplex weights.
    have simplex_threshold_chain (q : ℕ) (u : Simplex q) :
        ∃ k : ℕ, ∃ C : Fin (k + 1) → Face q, ∃ w : Simplex k,
          (∀ i j, i < j → (C i).1 ⊂ (C j).1) ∧
          (∀ j, 0 < w.1 j) ∧
          (∀ v : Fin (q + 1),
            (∑ j, w.1 j * (barycenter q (C j)).1 v) = u.1 v) ∧
          (∀ S : Face q, 0 < baryWeight q S u → ∃ j, C j = S) := by
      obtain ⟨k, c, hanti, hpos, hc, hcover⟩ := simplex_positive_levels q u
      let C : Fin (k + 1) → Face q := thresholdFace u c hc
      let weights : Fin (k + 1) → ℝ :=
        fun j => ((C j).1.card : ℝ) * thresholdGap k c j
      have hweights_pos (j : Fin (k + 1)) : 0 < weights j := by
        exact mul_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr (C j).2))
          (thresholdGap_pos k c hanti hpos j)
      have hterm (j : Fin (k + 1)) (v : Fin (q + 1)) :
          weights j * (barycenter q (C j)).1 v =
            if v ∈ (C j).1 then thresholdGap k c j else 0 := by
        change (((C j).1.card : ℝ) * thresholdGap k c j) *
          (if v ∈ (C j).1 then ((C j).1.card : ℝ)⁻¹ else 0) = _
        by_cases hv : v ∈ (C j).1
        · rw [if_pos hv, if_pos hv]
          have hcard : ((C j).1.card : ℝ) ≠ 0 :=
            ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr (C j).2))
          calc
            (((C j).1.card : ℝ) * thresholdGap k c j) * ((C j).1.card : ℝ)⁻¹ =
                (((C j).1.card : ℝ) * ((C j).1.card : ℝ)⁻¹) * thresholdGap k c j := by ring
            _ = thresholdGap k c j := by rw [mul_inv_cancel₀ hcard, one_mul]
        · rw [if_neg hv, if_neg hv, mul_zero]
      have hcoordinate (v : Fin (q + 1)) :
          (∑ j, weights j * (barycenter q (C j)).1 v) = u.1 v := by
        simp_rw [hterm]
        exact threshold_reconstruct u c hc hanti hpos hcover v
      have hsum : ∑ j, weights j = 1 := by
        calc
          (∑ j, weights j) = ∑ j, ∑ v, weights j * (barycenter q (C j)).1 v := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.mul_sum, (barycenter q (C j)).2.2, mul_one]
          _ = ∑ v, ∑ j, weights j * (barycenter q (C j)).1 v := Finset.sum_comm
          _ = ∑ v, u.1 v := by
            apply Finset.sum_congr rfl
            intro v hv
            exact hcoordinate v
          _ = 1 := u.2.2
      let w : Simplex k := ⟨weights, ⟨fun j => (hweights_pos j).le, hsum⟩⟩
      refine ⟨k, C, w, ?_, hweights_pos, hcoordinate, ?_⟩
      · intro i j hij
        exact thresholdFace_strict u c hc hanti i j hij
      · exact thresholdFace_covers_weights u c hc hcover

    have chain_injective (q r : ℕ) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) : Function.Injective C := by
      have hmono : StrictMono (fun i => (C i).1) := fun _ _ hij => hC _ _ hij
      exact fun _ _ h => hmono.injective (congrArg Subtype.val h)
    have baryWeight_sum (q : ℕ) (u : Simplex q) : ∑ S : Face q, baryWeight q S u = 1 := by
      obtain ⟨r, C, w, hC, hwpos, hcoord, hcover⟩ := simplex_threshold_chain q u
      have he : chainBary q r C w = u := Subtype.ext (funext hcoord)
      have hvalues (i : Fin (r + 1)) : w.1 i = baryWeight q (C i) u := by
        rw [← he, baryWeight_chain q r C hC]
      have hsum : (∑ i, w.1 i) = ∑ S : Face q, baryWeight q S u := by
        apply Finset.sum_of_injOn C (chain_injective q r C hC).injOn
          (fun _ _ => Finset.mem_univ _)
        · intro S _ hnot
          apply le_antisymm _ (baryWeight_nonneg q S u)
          apply le_of_not_gt
          intro hpos
          obtain ⟨i, hi⟩ := hcover S hpos
          exact hnot ⟨i, Finset.mem_univ i, hi⟩
        · intro i _
          exact hvalues i
      exact hsum.symm.trans w.2.2
    have baryWeight_chain_outside (q r : ℕ) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) (u : Simplex r)
        (S : Face q) (hS : S ∉ Set.range C) : baryWeight q S (chainBary q r C u) = 0 := by
      let T := Finset.univ.image C
      have hsum : ∑ S ∈ T, baryWeight q S (chainBary q r C u) = 1 := by
        rw [Finset.sum_image (chain_injective q r C hC).injOn]
        simp_rw [baryWeight_chain q r C hC]
        exact u.2.2
      have hcompl : ∑ S ∈ Tᶜ, baryWeight q S (chainBary q r C u) = 0 := by
        have h := Finset.sum_add_sum_compl T (fun S => baryWeight q S (chainBary q r C u))
        rw [hsum, baryWeight_sum] at h
        linarith
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun S _ => baryWeight_nonneg q S (chainBary q r C u))).mp hcompl
      simpa only [T, Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hS
    let SdPoint (q : ℕ) := {w : Face q → ℝ //
      (∀ S, 0 ≤ w S) ∧ (∑ S, w S = 1) ∧
      (∀ S T, 0 < w S → 0 < w T → S.1 ⊆ T.1 ∨ T.1 ⊆ S.1)}
    letI (q : ℕ) : TopologicalSpace (SdPoint q) := by dsimp only [SdPoint]; infer_instance
    let sdBary (q : ℕ) (w : SdPoint q) : Simplex q :=
      ⟨fun v => ∑ S, w.1 S * (barycenter q S).1 v, by
        constructor
        · intro v
          exact Finset.sum_nonneg (fun S _ => mul_nonneg (w.2.1 S) ((barycenter q S).2.1 v))
        · rw [Finset.sum_comm]
          simp_rw [← Finset.mul_sum, (barycenter q _).2.2, mul_one]
          exact w.2.2.1⟩
    let sdCoordinates (q : ℕ) (u : Simplex q) : SdPoint q :=
      ⟨fun S => baryWeight q S u, (fun S => baryWeight_nonneg q S u), baryWeight_sum q u,
        fun S T => baryWeight_comparable q S T u⟩
    have sdBary_continuous (q : ℕ) : Continuous (sdBary q) := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro v
      exact continuous_finsetSum _ (fun S _ =>
        ((continuous_apply S).comp continuous_subtype_val).mul continuous_const)
    have sdCoordinates_continuous (q : ℕ) : Continuous (sdCoordinates q) := by
      apply Continuous.subtype_mk
      apply continuous_pi
      exact baryWeight_continuous q
    have sdBary_coordinates (q : ℕ) (u : Simplex q) : sdBary q (sdCoordinates q u) = u := by
      obtain ⟨r, C, w, hC, hwpos, hcoord, hcover⟩ := simplex_threshold_chain q u
      have he : chainBary q r C w = u := Subtype.ext (funext hcoord)
      apply Subtype.ext
      funext v
      change (∑ S, baryWeight q S u * (barycenter q S).1 v) = u.1 v
      rw [← hcoord v]
      symm
      apply Finset.sum_of_injOn C (chain_injective q r C hC).injOn
        (fun _ _ => Finset.mem_univ _)
      · intro S _ hnot
        have hS : S ∉ Set.range C := by simpa only [Set.mem_image, Finset.mem_coe,
          Finset.mem_univ, true_and, Set.mem_range] using hnot
        rw [← he, baryWeight_chain_outside q r C hC w S hS, zero_mul]
      · intro i _
        rw [← he, baryWeight_chain q r C hC]
    have chainBary_isEmbedding (q r : ℕ) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) : IsEmbedding (chainBary q r C) := by
      let f : Simplex q → (Fin (r + 1) → ℝ) := fun v i => baryWeight q (C i) v
      have hf : Continuous f := continuous_pi (fun i => baryWeight_continuous q (C i))
      have hcomp : f ∘ chainBary q r C = fun u : Simplex r => u.1 := by
        funext u i
        exact baryWeight_chain q r C hC u i
      exact IsEmbedding.of_comp (chainBary_continuous q r C) hf
        (by rw [hcomp]; exact IsEmbedding.subtypeVal)
    have baryWeight_face_sum {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (S : Face q) (u : Simplex p) :
        baryWeight q S (simplexMap a.toOrderHom u) =
          ∑ T : Face p, if faceImage a T = S then baryWeight p T u else 0 := by
      by_cases hS : S ∈ Set.range (faceImage a)
      · obtain ⟨T, rfl⟩ := hS
        rw [baryWeight_face]
        simp only [(faceImage_injective a).eq_iff]
        exact (Fintype.sum_ite_eq' T (fun S => baryWeight p S u)).symm
      · have hz : baryWeight q S (simplexMap a.toOrderHom u) = 0 := by
          apply le_antisymm _ (baryWeight_nonneg q S (simplexMap a.toOrderHom u))
          apply le_of_not_gt
          intro hpos
          exact hS (baryWeight_face_support a S u hpos)
        rw [hz]
        symm
        apply Finset.sum_eq_zero
        intro T _
        exact if_neg (fun h => hS ⟨T, h⟩)
    -- T1: every subdivision point is represented by its positive face chain.
    have sdPoint_chain (q : ℕ) (w : SdPoint q) :
        ∃ r : ℕ, ∃ C : Fin (r + 1) → Face q, ∃ u : Simplex r,
          (∀ i j, i < j → (C i).1 ⊂ (C j).1) ∧
          (∀ i, 0 < u.1 i) ∧
          (∀ i, u.1 i = w.1 (C i)) ∧
          (∀ S : Face q, 0 < w.1 S → ∃ i, C i = S) ∧
          chainBary q r C u = sdBary q w := by
      classical
      let P : Finset (Face q) := Finset.univ.filter (fun S => 0 < w.1 S)
      have hPmem (S : Face q) : S ∈ P ↔ 0 < w.1 S := by
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      have hpositive : ∃ S : Face q, 0 < w.1 S := by
        by_contra hn
        have hz : ∀ S : Face q, w.1 S = 0 := by
          intro S
          apply le_antisymm
          · exact le_of_not_gt (fun hS => hn ⟨S, hS⟩)
          · exact w.2.1 S
        have hs := w.2.2.1
        simp [hz] at hs
      have hP : P.Nonempty := by
        obtain ⟨S, hS⟩ := hpositive
        exact ⟨S, (hPmem S).2 hS⟩
      have hcard_inj (S T : Face q) (hS : 0 < w.1 S) (hT : 0 < w.1 T)
          (hcard : S.1.card = T.1.card) : S = T := by
        apply Subtype.ext
        rcases w.2.2.2 S T hS hT with hST | hTS
        · exact Finset.eq_of_subset_of_card_le hST (by omega)
        · exact (Finset.eq_of_subset_of_card_le hTS (by omega)).symm
      let R : Finset ℕ := P.image (fun S => S.1.card)
      have hR : R.Nonempty := by
        obtain ⟨S, hS⟩ := hP
        exact ⟨S.1.card, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩
      let r := R.card - 1
      have hr : R.card = r + 1 := by
        have hcard := Finset.card_pos.mpr hR
        dsimp only [r]
        omega
      let e : Fin (r + 1) ↪o ℕ := R.orderEmbOfFin hr
      have hex (i : Fin (r + 1)) : ∃ S : Face q, S ∈ P ∧ S.1.card = e i := by
        exact Finset.mem_image.mp (Finset.orderEmbOfFin_mem R hr i)
      let C : Fin (r + 1) → Face q := fun i => Classical.choose (hex i)
      have hCmem (i : Fin (r + 1)) : C i ∈ P :=
        (Classical.choose_spec (hex i)).1
      have hCcard (i : Fin (r + 1)) : (C i).1.card = e i :=
        (Classical.choose_spec (hex i)).2
      have hCpos (i : Fin (r + 1)) : 0 < w.1 (C i) :=
        (hPmem (C i)).1 (hCmem i)
      have hCstrict : ∀ i j, i < j → (C i).1 ⊂ (C j).1 := by
        intro i j hij
        have hlt : (C i).1.card < (C j).1.card := by
          rw [hCcard i, hCcard j]
          exact e.strictMono hij
        rcases w.2.2.2 (C i) (C j) (hCpos i) (hCpos j) with hsub | hsub
        · apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨hsub, ?_⟩
          intro he
          exact (ne_of_lt hlt) (congrArg Finset.card he)
        · have hle := Finset.card_le_card hsub
          omega
      have hcover (S : Face q) (hS : 0 < w.1 S) : ∃ i, C i = S := by
        have hScard : S.1.card ∈ R :=
          Finset.mem_image.mpr ⟨S, (hPmem S).2 hS, rfl⟩
        have hrange : S.1.card ∈ Set.range e := by
          rw [show Set.range e = (R : Set ℕ) from Finset.range_orderEmbOfFin R hr]
          exact hScard
        obtain ⟨i, hi⟩ := hrange
        exact ⟨i, hcard_inj (C i) S (hCpos i) hS ((hCcard i).trans hi)⟩
      have hzero (S : Face q) (hS : S ∉ Set.range C) : w.1 S = 0 := by
        apply le_antisymm _ (w.2.1 S)
        apply le_of_not_gt
        intro hpos
        exact hS (hcover S hpos)
      have hsum : (∑ i, w.1 (C i)) = ∑ S : Face q, w.1 S := by
        apply Finset.sum_of_injOn C (chain_injective q r C hCstrict).injOn
          (fun _ _ => Finset.mem_univ _)
        · intro S _ hnot
          apply hzero S
          rintro ⟨i, rfl⟩
          exact hnot ⟨i, Finset.mem_univ i, rfl⟩
        · intro i _
          rfl
      let u : Simplex r :=
        ⟨fun i => w.1 (C i), ⟨fun i => (hCpos i).le, hsum.trans w.2.2.1⟩⟩
      refine ⟨r, C, u, hCstrict, hCpos, (fun _ => rfl), hcover, ?_⟩
      apply Subtype.ext
      funext v
      change (∑ i, w.1 (C i) * (barycenter q (C i)).1 v) =
        ∑ S : Face q, w.1 S * (barycenter q S).1 v
      apply Finset.sum_of_injOn C (chain_injective q r C hCstrict).injOn
        (fun _ _ => Finset.mem_univ _)
      · intro S _ hnot
        have hz : w.1 S = 0 := by
          apply hzero S
          rintro ⟨i, rfl⟩
          exact hnot ⟨i, Finset.mem_univ i, rfl⟩
        rw [hz, zero_mul]
      · intro i _
        rfl
    have sdCoordinates_bary (q : ℕ) (w : SdPoint q) : sdCoordinates q (sdBary q w) = w := by
      obtain ⟨r, C, u, hC, hupos, hu, hcover, he⟩ := sdPoint_chain q w
      apply Subtype.ext
      funext S
      change baryWeight q S (sdBary q w) = w.1 S
      rw [← he]
      by_cases hS : S ∈ Set.range C
      · obtain ⟨i, rfl⟩ := hS
        rw [baryWeight_chain q r C hC]
        exact hu i
      · rw [baryWeight_chain_outside q r C hC u S hS]
        symm
        apply le_antisymm _ (w.2.1 S)
        apply le_of_not_gt
        intro hpos
        exact hS (hcover S hpos)
    let subdivisionHomeomorph (q : ℕ) : SdPoint q ≃ₜ Simplex q :=
      { toFun := sdBary q
        invFun := sdCoordinates q
        left_inv := sdCoordinates_bary q
        right_inv := sdBary_coordinates q
        continuous_toFun := sdBary_continuous q
        continuous_invFun := sdCoordinates_continuous q }
    have chainBary_positive_iff (q r : ℕ) (C : Fin (r + 1) → Face q)
        (u : Simplex r) (v : Fin (q + 1)) :
        0 < (chainBary q r C u).1 v ↔ ∃ i, v ∈ (C i).1 ∧ 0 < u.1 i := by
      change 0 < ∑ i, u.1 i * (barycenter q (C i)).1 v ↔ _
      rw [Finset.sum_pos_iff_of_nonneg
        (fun i _ => mul_nonneg (u.2.1 i) ((barycenter q (C i)).2.1 v))]
      constructor
      · rintro ⟨i, _, hi⟩
        have h := (mul_pos_iff.mp hi).resolve_right (fun h => (not_lt_of_ge (u.2.1 i)) h.1)
        exact ⟨i, (barycenter_positive q (C i) v).mp h.2, h.1⟩
      · rintro ⟨i, hv, hi⟩
        exact ⟨i, Finset.mem_univ i, mul_pos hi ((barycenter_positive q (C i) v).mpr hv)⟩
    have chainBary_positive_unique (q r s : ℕ)
        (C : Fin (r + 1) → Face q) (D : Fin (s + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1)
        (hD : ∀ i j, i < j → (D i).1 ⊂ (D j).1)
        (u : Simplex r) (v : Simplex s) (hu : ∀ i, 0 < u.1 i) (hv : ∀ i, 0 < v.1 i)
        (he : chainBary q r C u = chainBary q s D v) :
        (⟨r, (C, u)⟩ : Σ k, (Fin (k + 1) → Face q) × Simplex k) = ⟨s, (D, v)⟩ := by
      have hsubset : Set.range C ⊆ Set.range D := by
        rintro S ⟨i, rfl⟩
        by_contra hn
        have h := baryWeight_chain q r C hC u i
        rw [he, baryWeight_chain_outside q s D hD v (C i) hn] at h
        exact (ne_of_gt (hu i)) h.symm
      have hsupset : Set.range D ⊆ Set.range C := by
        rintro S ⟨i, rfl⟩
        by_contra hn
        have h := baryWeight_chain q s D hD v i
        rw [← he, baryWeight_chain_outside q r C hC u (D i) hn] at h
        exact (ne_of_gt (hv i)) h.symm
      have hRange : Set.range C = Set.range D := Set.Subset.antisymm hsubset hsupset
      have himage : Finset.univ.image C = Finset.univ.image D := by
        ext S
        simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using
          Set.ext_iff.mp hRange S
      have hrs : r = s := by
        have hcard := congrArg Finset.card himage
        rw [Finset.card_image_of_injective _ (chain_injective q r C hC),
          Finset.card_image_of_injective _ (chain_injective q s D hD)] at hcard
        simp only [Finset.card_univ, Fintype.card_fin] at hcard
        omega
      subst s
      have hCmono : StrictMono (fun i => (C i).1) := fun _ _ h => hC _ _ h
      have hDmono : StrictMono (fun i => (D i).1) := fun _ _ h => hD _ _ h
      have hRange' : Set.range (fun i => (C i).1) = Set.range (fun i => (D i).1) := by
        ext S
        constructor
        · rintro ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := hsubset ⟨i, rfl⟩
          exact ⟨j, congrArg Subtype.val hj⟩
        · rintro ⟨j, rfl⟩
          obtain ⟨i, hi⟩ := hsupset ⟨j, rfl⟩
          exact ⟨i, congrArg Subtype.val hi⟩
      have hCD : C = D := by
        funext i
        exact Subtype.ext (congrFun ((hCmono.range_inj hDmono).mp hRange') i)
      subst D
      have huv : u = v := (chainBary_isEmbedding q r C hC).injective he
      subst v
      rfl
    have simplexMap_id (q : ℕ) (u : Simplex q) : simplexMap (OrderHom.id) u = u := by
      apply Subtype.ext
      funext i
      simp [simplexMap]
    have simplexMap_comp {p q r : ℕ} (a : Fin (p + 1) →o Fin (q + 1))
        (b : Fin (q + 1) →o Fin (r + 1)) (u : Simplex p) :
        simplexMap b (simplexMap a u) = simplexMap (b.comp a) u := by
      apply Subtype.ext
      funext k
      change (∑ j, if b j = k then (∑ i, if a i = j then u.1 i else 0) else 0) =
        ∑ i, if b (a i) = k then u.1 i else 0
      have hsum (j : Fin (q + 1)) :
          (if b j = k then (∑ i, if a i = j then u.1 i else 0) else 0) =
            ∑ i, if b j = k then (if a i = j then u.1 i else 0) else 0 := by
        split_ifs <;> simp
      simp_rw [hsum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      have hterm (j : Fin (q + 1)) :
          (if b j = k then (if a i = j then u.1 i else 0) else 0) =
            if a i = j then (if b (a i) = k then u.1 i else 0) else 0 := by
        by_cases hij : a i = j
        · subst j
          simp
        · simp [hij]
      simp_rw [hterm]
      simp
    -- T1: canonical enumeration and restriction of a nonempty face.
    let fullFace (q : ℕ) : Face q := ⟨Finset.univ, Finset.univ_nonempty⟩
    let faceDim {q : ℕ} (S : Face q) : ℕ := S.1.card - 1
    have faceCard {q : ℕ} (S : Face q) : S.1.card = faceDim S + 1 := by
      have hpos := Finset.card_pos.mpr S.2
      dsimp only [faceDim]
      omega
    let faceEnum {q : ℕ} (S : Face q) : Fin (faceDim S + 1) ↪o Fin (q + 1) :=
      S.1.orderEmbOfFin (faceCard S)
    have faceEnum_mem {q : ℕ} (S : Face q) (i : Fin (faceDim S + 1)) :
        faceEnum S i ∈ S.1 :=
      Finset.orderEmbOfFin_mem S.1 (faceCard S) i
    have faceEnum_range {q : ℕ} (S : Face q) :
        Set.range (faceEnum S) = (S.1 : Set (Fin (q + 1))) :=
      Finset.range_orderEmbOfFin S.1 (faceCard S)
    have faceDim_full (q : ℕ) : faceDim (fullFace q) = q := by
      simp [faceDim, fullFace]
    have faceEnum_full (q : ℕ) :
        faceEnum (fullFace q) =
          (Fin.castOrderIso (congrArg (fun d : ℕ => d + 1) (faceDim_full q))).toOrderEmbedding := by
      symm
      apply Finset.orderEmbOfFin_unique' (faceCard (fullFace q))
      intro i
      exact Finset.mem_univ _
    have faceImage_comp {p q r : ℕ}
        (a : Fin (p + 1) ↪o Fin (q + 1)) (b : Fin (q + 1) ↪o Fin (r + 1))
        (S : Face p) : faceImage b (faceImage a S) = faceImage (a.comp b) S := by
      apply Subtype.ext
      exact Finset.map_map a.toEmbedding b.toEmbedding S.1
    have faceImage_mono {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1))
        (S T : Face p) (hST : S.1 ⊆ T.1) : (faceImage a S).1 ⊆ (faceImage a T).1 :=
      Finset.map_subset_map.mpr hST
    have faceDim_image {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) (S : Face p) :
        faceDim (faceImage a S) = faceDim S := by
      simp only [faceDim, faceImage, Finset.card_map]
    have faceEnum_image {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) (S : Face p) :
        faceEnum (faceImage a S) =
          ((Fin.castOrderIso
            (congrArg (fun d : ℕ => d + 1) (faceDim_image a S))).toOrderEmbedding).comp
              ((faceEnum S).comp a) := by
      symm
      apply Finset.orderEmbOfFin_unique' (faceCard (faceImage a S))
      intro i
      exact Finset.mem_map.mpr ⟨_, faceEnum_mem S _, rfl⟩
    let restrictFace {q : ℕ} (S T : Face q) (hTS : T.1 ⊆ S.1) : Face (faceDim S) :=
      ⟨Finset.univ.filter (fun i => faceEnum S i ∈ T.1), by
        obtain ⟨v, hv⟩ := T.2
        have hvS : v ∈ Set.range (faceEnum S) := by
          rw [faceEnum_range S]
          exact hTS hv
        obtain ⟨i, rfl⟩ := hvS
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hv⟩⟩⟩
    have restrictFace_mem {q : ℕ} (S T : Face q) (hTS : T.1 ⊆ S.1)
        (i : Fin (faceDim S + 1)) :
        i ∈ (restrictFace S T hTS).1 ↔ faceEnum S i ∈ T.1 := by
      simp only [restrictFace, Finset.mem_filter, Finset.mem_univ, true_and]
    have restrictFace_map {q : ℕ} (S T : Face q) (hTS : T.1 ⊆ S.1) :
        faceImage (faceEnum S) (restrictFace S T hTS) = T := by
      apply Subtype.ext
      ext v
      change v ∈ (restrictFace S T hTS).1.map (faceEnum S).toEmbedding ↔ v ∈ T.1
      constructor
      · intro hv
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
        exact (restrictFace_mem S T hTS i).1 hi
      · intro hv
        have hvS : v ∈ Set.range (faceEnum S) := by
          rw [faceEnum_range S]
          exact hTS hv
        obtain ⟨i, rfl⟩ := hvS
        exact Finset.mem_map.mpr
          ⟨i, (restrictFace_mem S T hTS i).2 hv, rfl⟩
    have restrictFace_self {q : ℕ} (S : Face q) :
        restrictFace S S (fun _ hi => hi) = fullFace (faceDim S) := by
      apply Subtype.ext
      ext i
      constructor
      · intro _
        exact Finset.mem_univ i
      · intro _
        exact (restrictFace_mem S S (fun _ hi => hi) i).2 (faceEnum_mem S i)
    have restrictFace_card {q : ℕ} (S T : Face q) (hTS : T.1 ⊆ S.1) :
        (restrictFace S T hTS).1.card = T.1.card := by
      have h := congrArg (fun U : Face q => U.1.card) (restrictFace_map S T hTS)
      simpa only [faceImage, Finset.card_map] using h
    have restrictFace_dim {q : ℕ} (S T : Face q) (hTS : T.1 ⊆ S.1) :
        faceDim (restrictFace S T hTS) = faceDim T :=
      congrArg (fun c : ℕ => c - 1) (restrictFace_card S T hTS)
    have restrictFace_mono {q : ℕ} (S T U : Face q)
        (hTS : T.1 ⊆ S.1) (hUS : U.1 ⊆ S.1) (hTU : T.1 ⊆ U.1) :
        (restrictFace S T hTS).1 ⊆ (restrictFace S U hUS).1 := by
      intro i hi
      exact (restrictFace_mem S U hUS i).2
        (hTU ((restrictFace_mem S T hTS i).1 hi))
    have restrictFace_strict {q : ℕ} (S T U : Face q)
        (hTS : T.1 ⊆ S.1) (hUS : U.1 ⊆ S.1) (hTU : T.1 ⊂ U.1) :
        (restrictFace S T hTS).1 ⊂ (restrictFace S U hUS).1 := by
      apply (Finset.map_ssubset_map (f := (faceEnum S).toEmbedding)).mp
      change (faceImage (faceEnum S) (restrictFace S T hTS)).1 ⊂
        (faceImage (faceEnum S) (restrictFace S U hUS)).1
      rw [restrictFace_map S T hTS, restrictFace_map S U hUS]
      exact hTU
    let Flag (q r : ℕ) := {C : Fin (r + 1) → Face q //
      (∀ i j, i < j → (C i).1 ⊂ (C j).1) ∧ C (Fin.last r) = fullFace q}
    let Cell1 (n r : ℕ) := Σ q, Σ z : K n q, Flag q r
    let char1 (n r : ℕ) (cellA : Cell1 n r) (u : Simplex r) : fatLevel n :=
      fatProjection n cellA.1 cellA.2.1 (chainBary cellA.1 r cellA.2.2.1 u)
    have char1_continuous (n r : ℕ) (cellA : Cell1 n r) : Continuous (char1 n r cellA) :=
      (fatProjection_continuous n cellA.1 cellA.2.1).comp (chainBary_continuous cellA.1 r cellA.2.2.1)
    have flagBary_positive (q r : ℕ) (C : Flag q r) (u : Simplex r)
        (hu : ∀ i, 0 < u.1 i) (v : Fin (q + 1)) : 0 < (chainBary q r C.1 u).1 v := by
      apply (chainBary_positive_iff q r C.1 u v).mpr
      refine ⟨Fin.last r, ?_, hu (Fin.last r)⟩
      rw [C.2.2]
      exact Finset.mem_univ v
    have char1_positive_unique (n r s : ℕ) (cellA : Cell1 n r) (cellB : Cell1 n s)
        (u : Simplex r) (v : Simplex s) (hu : ∀ i, 0 < u.1 i) (hv : ∀ i, 0 < v.1 i)
        (he : char1 n r cellA u = char1 n s cellB v) :
        (⟨r, (cellA, u)⟩ : Σ k, Cell1 n k × Simplex k) = ⟨s, (cellB, v)⟩ := by
      obtain ⟨q, z, C⟩ := cellA
      obtain ⟨p, w, D⟩ := cellB
      have htop := fat_label_unique n q p z w (chainBary q r C.1 u) (chainBary p s D.1 v)
        (flagBary_positive q r C u hu) (flagBary_positive p s D v hv) he
      have hqp : q = p := congrArg Sigma.fst htop
      subst p
      have hzw : z = w := eq_of_heq (Sigma.mk.inj_iff.mp htop).2
      subst w
      have hcoord : chainBary q r C.1 u = chainBary q s D.1 v := by
        have h := (fat_projection_positive_embedding_all n q z).injective
          (a₁ := ⟨chainBary q r C.1 u, flagBary_positive q r C u hu⟩)
          (a₂ := ⟨chainBary q s D.1 v, flagBary_positive q s D v hv⟩) he
        exact congrArg Subtype.val h
      have hchain := chainBary_positive_unique q r s C.1 D.1 C.2.1 D.2.1 u v hu hv hcoord
      have hrs : r = s := congrArg Sigma.fst hchain
      subst s
      have hpairs : (C.1, u) = (D.1, v) := eq_of_heq (Sigma.mk.inj_iff.mp hchain).2
      have hCD : C = D := Subtype.ext (congrArg Prod.fst hpairs)
      have huv : u = v := congrArg Prod.snd hpairs
      subst D
      subst v
      rfl
    have char1_positive_rep (n : ℕ) (x : fatLevel n) :
        ∃ r, ∃ cellA : Cell1 n r, ∃ u : Simplex r, (∀ i, 0 < u.1 i) ∧ char1 n r cellA u = x := by
      obtain ⟨q, z, u, hu, he⟩ := fat_positive_rep n x
      obtain ⟨r, C, v, hC, hv, hcoord, hcover⟩ := simplex_threshold_chain q u
      have hcu : chainBary q r C v = u := Subtype.ext (funext hcoord)
      have hlast : C (Fin.last r) = fullFace q := by
        apply Subtype.ext
        ext i
        simp only [fullFace, Finset.mem_univ, iff_true]
        have hipos : 0 < (chainBary q r C v).1 i := by rw [hcu]; exact hu i
        obtain ⟨j, hj, _⟩ := (chainBary_positive_iff q r C v i).mp hipos
        exact chain_mono q r C hC j (Fin.last r) (Fin.le_last j) hj
      refine ⟨r, ⟨q, z, ⟨C, hC, hlast⟩⟩, v, hv, ?_⟩
      change fatProjection n q z (chainBary q r C v) = x
      rw [hcu]
      exact he
    let restrictFlag {q r s : ℕ} (C : Flag q r) (b : Fin (s + 1) ↪o Fin (r + 1)) :
        Flag (faceDim (C.1 (b (Fin.last s)))) s := by
      let S := C.1 (b (Fin.last s))
      have hsub (j : Fin (s + 1)) : (C.1 (b j)).1 ⊆ S.1 :=
        chain_mono q r C.1 C.2.1 (b j) (b (Fin.last s)) (b.monotone (Fin.le_last j))
      refine ⟨fun j => restrictFace S (C.1 (b j)) (hsub j), ?_, ?_⟩
      · intro i j hij
        exact restrictFace_strict S (C.1 (b i)) (C.1 (b j)) (hsub i) (hsub j)
          (C.2.1 (b i) (b j) (b.strictMono hij))
      · exact restrictFace_self S
    let face1 {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1)) (cellA : Cell1 n r) : Cell1 n s :=
      ⟨faceDim (cellA.2.2.1 (b (Fin.last s))),
        pull (faceEnum (cellA.2.2.1 (b (Fin.last s)))).toOrderHom cellA.2.1,
        restrictFlag cellA.2.2 b⟩
    have restrictFlag_map {q r s : ℕ} (C : Flag q r) (b : Fin (s + 1) ↪o Fin (r + 1))
        (i : Fin (s + 1)) :
        faceImage (faceEnum (C.1 (b (Fin.last s)))) ((restrictFlag C b).1 i) = C.1 (b i) :=
      restrictFace_map _ _ (chain_mono q r C.1 C.2.1 (b i) (b (Fin.last s))
        (b.monotone (Fin.le_last i)))
    have char1_face {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1))
        (cellA : Cell1 n r) (u : Simplex s) :
        char1 n s (face1 b cellA) u = char1 n r cellA (simplexMap b.toOrderHom u) := by
      obtain ⟨q, z, C⟩ := cellA
      change fatProjection n _ (pull (faceEnum (C.1 (b (Fin.last s)))).toOrderHom z)
        (chainBary _ s (restrictFlag C b).1 u) =
          fatProjection n q z (chainBary q r C.1 (simplexMap b.toOrderHom u))
      rw [fatProjection_face _ (faceEnum _).injective]
      apply congrArg (fatProjection n q z)
      rw [← chainBary_face, chainBary_chainface]
      congr 1
      funext i
      exact restrictFlag_map C b i
    have char1_ext (n r : ℕ) (cellA cellB : Cell1 n r)
        (he : ∀ u, char1 n r cellA u = char1 n r cellB u) : cellA = cellB := by
      let u := barycenter r (fullFace r)
      have hu (i : Fin (r + 1)) : 0 < u.1 i :=
        (barycenter_positive r (fullFace r) i).mpr (Finset.mem_univ i)
      have h := char1_positive_unique n r r cellA cellB u u hu hu (he u)
      exact congrArg Prod.fst (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    have face1_id (n r : ℕ) (cellA : Cell1 n r) : face1 (OrderEmbedding.id _) cellA = cellA := by
      apply char1_ext n r
      intro u
      rw [char1_face]
      exact congrArg (char1 n r cellA) (simplexMap_id r u)
    have face1_comp {n r s t : ℕ} (a : Fin (t + 1) ↪o Fin (s + 1))
        (b : Fin (s + 1) ↪o Fin (r + 1)) (cellA : Cell1 n r) :
        face1 a (face1 b cellA) = face1 (a.comp b) cellA := by
      apply char1_ext n t
      intro u
      rw [char1_face, char1_face, char1_face, simplexMap_comp]
      rfl
    let rank1 {n r : ℕ} (cellA : Cell1 n r) (i : Fin (r + 1)) : ℕ :=
      (cellA.2.2.1 i).1.card
    have rank1_face {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1))
        (cellA : Cell1 n r) (i : Fin (s + 1)) : rank1 (face1 b cellA) i = rank1 cellA (b i) :=
      restrictFace_card _ _ (chain_mono cellA.1 r cellA.2.2.1 cellA.2.2.2.1
        (b i) (b (Fin.last s)) (b.monotone (Fin.le_last i)))
    have face1_occurrence_injective {n r s : ℕ} (cellA : Cell1 n r) :
        Function.Injective (fun b : Fin (s + 1) ↪o Fin (r + 1) => face1 b cellA) := by
      have hmono : StrictMono (rank1 cellA) := fun _ _ hij => Finset.card_lt_card (cellA.2.2.2.1 _ _ hij)
      intro a b he
      change face1 a cellA = face1 b cellA at he
      apply DFunLike.ext
      intro i
      apply hmono.injective
      rw [← rank1_face a cellA i, he, rank1_face b cellA i]
    -- T1: every closed first-subdivision cell is embedded.
    have char1_injective (n r : ℕ) (cellA : Cell1 n r) :
        Function.Injective (char1 n r cellA) := by
      intro u v huv
      obtain ⟨p, a, u', hu', hua⟩ := simplex_support r u
      obtain ⟨s, b, v', hv', hvb⟩ := simplex_support r v
      have he : char1 n p (face1 a cellA) u' = char1 n s (face1 b cellA) v' := by
        rw [char1_face, char1_face, hua, hvb]
        exact huv
      have hrep := char1_positive_unique n p s (face1 a cellA) (face1 b cellA)
        u' v' hu' hv' he
      have hps : p = s := congrArg Sigma.fst hrep
      subst s
      have hpairs : (face1 a cellA, u') = (face1 b cellA, v') :=
        eq_of_heq (Sigma.mk.inj_iff.mp hrep).2
      have hab : a = b := face1_occurrence_injective cellA (congrArg Prod.fst hpairs)
      have huv' : u' = v' := congrArg Prod.snd hpairs
      calc
        u = simplexMap a.toOrderHom u' := hua.symm
        _ = simplexMap b.toOrderHom v' := by rw [hab, huv']
        _ = v := hvb
    have simplex_compact (r : ℕ) : CompactSpace (Simplex r) := by
      obtain ⟨f, hf, _⟩ := ball_simplex_data r
      exact Function.Surjective.compactSpace f.continuous hf
    have char1_isClosedEmbedding (n r : ℕ) (cellA : Cell1 n r) :
        IsClosedEmbedding (char1 n r cellA) := by
      letI : CompactSpace (Simplex r) := simplex_compact r
      letI : T2Space (fatLevel n) := fat_t2 n
      exact (char1_continuous n r cellA).isClosedEmbedding (char1_injective n r cellA)
    have char1_range_closed (n r : ℕ) (cellA : Cell1 n r) :
        IsClosed (Set.range (char1 n r cellA)) :=
      (char1_isClosedEmbedding n r cellA).isClosed_range
    let AllCell1 (n : ℕ) := Σ r, Cell1 n r
    let faceLE1 (n : ℕ) (cellA cellB : AllCell1 n) : Prop :=
      ∃ b : Fin (cellA.1 + 1) ↪o Fin (cellB.1 + 1), face1 b cellB.2 = cellA.2
    have faceLE1_refl (n : ℕ) (cellA : AllCell1 n) : faceLE1 n cellA cellA :=
      ⟨OrderEmbedding.id _, face1_id n cellA.1 cellA.2⟩
    have faceLE1_trans (n : ℕ) (cellA cellB cellC : AllCell1 n)
        (hAB : faceLE1 n cellA cellB) (hBC : faceLE1 n cellB cellC) : faceLE1 n cellA cellC := by
      obtain ⟨a, ha⟩ := hAB
      obtain ⟨b, hb⟩ := hBC
      refine ⟨a.comp b, ?_⟩
      rw [← face1_comp, hb, ha]
    have faceLE1_dim (n : ℕ) (cellA cellB : AllCell1 n)
        (hAB : faceLE1 n cellA cellB) : cellA.1 ≤ cellB.1 := by
      obtain ⟨b, _⟩ := hAB
      have hcard := Fintype.card_le_of_injective b b.injective
      simp only [Fintype.card_fin] at hcard
      omega
    have faceLE1_eq_of_dim (n r : ℕ) (cellA cellB : Cell1 n r)
        (hAB : faceLE1 n ⟨r, cellA⟩ ⟨r, cellB⟩) : cellA = cellB := by
      obtain ⟨b, hb⟩ := hAB
      have hid : b = OrderEmbedding.id _ := by
        apply DFunLike.ext
        intro i
        exact DFunLike.congr_fun (b.toOrderHom.eq_id_of_injective b.injective) i
      rw [hid, face1_id] at hb
      exact hb.symm
    have faceLE1_antisymm (n : ℕ) (cellA cellB : AllCell1 n)
        (hAB : faceLE1 n cellA cellB) (hBA : faceLE1 n cellB cellA) : cellA = cellB := by
      obtain ⟨r, cellA⟩ := cellA
      obtain ⟨s, cellB⟩ := cellB
      have hrs : r = s := Nat.le_antisymm (faceLE1_dim n _ _ hAB) (faceLE1_dim n _ _ hBA)
      subst s
      exact congrArg (Sigma.mk r) (faceLE1_eq_of_dim n r cellA cellB hAB)
    letI (n : ℕ) : PartialOrder (AllCell1 n) :=
      { le := faceLE1 n
        le_refl := faceLE1_refl n
        le_trans := fun A B C => faceLE1_trans n A B C
        le_antisymm := fun A B => faceLE1_antisymm n A B }
    have cell1_dim_strict (n : ℕ) : StrictMono (fun cellA : AllCell1 n => cellA.1) := by
      intro cellA cellB hAB
      have hle := faceLE1_dim n cellA cellB hAB.le
      apply lt_of_le_of_ne hle
      intro he
      obtain ⟨r, cellA⟩ := cellA
      obtain ⟨s, cellB⟩ := cellB
      change r = s at he
      subst s
      have hab := faceLE1_eq_of_dim n r cellA cellB hAB.le
      subst cellB
      exact (lt_irrefl (⟨r, cellA⟩ : AllCell1 n)) hAB
    have chain_length_le (q r : ℕ) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) : r ≤ q := by
      choose f hf using chain_new_vertex q r C hC
      have hinj : Function.Injective f := by
        intro i j he
        apply le_antisymm
        · have hj := (hf j j).mpr le_rfl
          rw [← he] at hj
          exact (hf i j).mp hj
        · have hi := (hf i i).mpr le_rfl
          rw [he] at hi
          exact (hf j i).mp hi
      have hcard := Fintype.card_le_of_injective f hinj
      simp only [Fintype.card_fin] at hcard
      omega
    let ChainChoice (q : ℕ) := Σ r : Fin (q + 1),
      {C : Fin (r.1 + 1) → Face q // ∀ i j, i < j → (C i).1 ⊂ (C j).1}
    letI (q : ℕ) : Fintype (ChainChoice q) := by dsimp only [ChainChoice]; infer_instance
    have continuous_of_chainBary (q : ℕ) (Z : Type) [TopologicalSpace Z] (f : Simplex q → Z)
        (hf : ∀ r (C : Fin (r + 1) → Face q),
          (∀ i j, i < j → (C i).1 ⊂ (C j).1) → Continuous (f ∘ chainBary q r C)) : Continuous f := by
      letI (r : ℕ) : CompactSpace (Simplex r) := simplex_compact r
      let W := Σ c : ChainChoice q, Simplex c.1.1
      letI : CompactSpace W := by
        have hc : IsCompact (⋃ c : ChainChoice q, Set.range (fun u : Simplex c.1.1 => (⟨c, u⟩ : W))) :=
          isCompact_iUnion (fun c => isCompact_range
            (continuous_sigmaMk («σ» := fun d : ChainChoice q => Simplex d.1.1) (i := c)))
        have he : (⋃ c : ChainChoice q, Set.range (fun u : Simplex c.1.1 => (⟨c, u⟩ : W))) = Set.univ := by
          apply Set.eq_univ_of_forall
          rintro ⟨c, u⟩
          exact Set.mem_iUnion.mpr ⟨c, u, rfl⟩
        exact ⟨he ▸ hc⟩
      let g : W → Simplex q := fun w => chainBary q w.1.1.1 w.1.2.1 w.2
      have hg : Continuous g := continuous_sigma (fun c => chainBary_continuous q c.1.1 c.2.1)
      have hsurj : Function.Surjective g := by
        intro u
        obtain ⟨r, C, v, hC, hv, hcoord, hcover⟩ := simplex_threshold_chain q u
        let c : ChainChoice q := ⟨⟨r, Nat.lt_succ_of_le (chain_length_le q r C hC)⟩, ⟨C, hC⟩⟩
        exact ⟨⟨c, v⟩, Subtype.ext (funext hcoord)⟩
      have hquot : IsQuotientMap g := hg.isClosedMap.isQuotientMap hg hsurj
      exact hquot.continuous_iff.mpr (continuous_sigma (fun c => hf c.1.1 c.2.1 c.2.2))
    let normalizeFlag {q r : ℕ} (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) : Flag (faceDim (C (Fin.last r))) r := by
      let S := C (Fin.last r)
      have hsub (i : Fin (r + 1)) : (C i).1 ⊆ S.1 :=
        chain_mono q r C hC i (Fin.last r) (Fin.le_last i)
      refine ⟨fun i => restrictFace S (C i) (hsub i), ?_, ?_⟩
      · intro i j hij
        exact restrictFace_strict S (C i) (C j) (hsub i) (hsub j) (hC i j hij)
      · exact restrictFace_self S
    let chainCell1 (n q r : ℕ) (z : K n q) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) : Cell1 n r :=
      ⟨faceDim (C (Fin.last r)), pull (faceEnum (C (Fin.last r))).toOrderHom z, normalizeFlag C hC⟩
    have chainCell1_char (n q r : ℕ) (z : K n q) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) (u : Simplex r) :
        char1 n r (chainCell1 n q r z C hC) u = fatProjection n q z (chainBary q r C u) := by
      change fatProjection n _ (pull (faceEnum (C (Fin.last r))).toOrderHom z)
        (chainBary _ r (normalizeFlag C hC).1 u) = _
      rw [fatProjection_face _ (faceEnum _).injective]
      apply congrArg (fatProjection n q z)
      rw [← chainBary_face]
      congr 1
      funext i
      exact restrictFace_map _ _ (chain_mono q r C hC i (Fin.last r) (Fin.le_last i))
    have char1_final (n : ℕ) (Z : Type) [TopologicalSpace Z] (f : fatLevel n → Z)
        (hf : ∀ r (cellA : Cell1 n r), Continuous (f ∘ char1 n r cellA)) : Continuous f := by
      apply (isQuotientMap_quot_mk (r := faceRelation n)).continuous_iff.mpr
      apply continuous_sigma
      intro q
      apply continuous_sigma
      intro z
      apply continuous_of_chainBary q Z (f ∘ fatProjection n q z)
      intro r C hC
      have he : (f ∘ fatProjection n q z) ∘ chainBary q r C =
          f ∘ char1 n r (chainCell1 n q r z C hC) := by
        funext u
        exact congrArg f (chainCell1_char n q r z C hC u).symm
      rw [he]
      exact hf r (chainCell1 n q r z C hC)
    -- T1: the unique face occurrence and its vertex subset in an upper cell.
    let occ1 {n : ℕ} (cellA cellB : AllCell1 n) (hAB : cellA ≤ cellB) :
        Fin (cellA.1 + 1) ↪o Fin (cellB.1 + 1) :=
      Classical.choose (show faceLE1 n cellA cellB from hAB)
    have face1_occ1 {n : ℕ} (cellA cellB : AllCell1 n) (hAB : cellA ≤ cellB) :
        face1 (occ1 cellA cellB hAB) cellB.2 = cellA.2 :=
      Classical.choose_spec (show faceLE1 n cellA cellB from hAB)
    have occ1_unique {n : ℕ} (cellA cellB : AllCell1 n) (hAB : cellA ≤ cellB)
        (b : Fin (cellA.1 + 1) ↪o Fin (cellB.1 + 1))
        (hb : face1 b cellB.2 = cellA.2) : occ1 cellA cellB hAB = b := by
      apply face1_occurrence_injective cellB.2
      exact (face1_occ1 cellA cellB hAB).trans hb.symm
    have occ1_self {n : ℕ} (cellA : AllCell1 n) :
        occ1 cellA cellA le_rfl = OrderEmbedding.id _ :=
      occ1_unique cellA cellA le_rfl (OrderEmbedding.id _) (face1_id n cellA.1 cellA.2)
    have occ1_comp {n : ℕ} (cellA cellB cellC : AllCell1 n)
        (hAB : cellA ≤ cellB) (hBC : cellB ≤ cellC) :
        (occ1 cellA cellB hAB).comp (occ1 cellB cellC hBC) =
          occ1 cellA cellC (hAB.trans hBC) := by
      apply face1_occurrence_injective cellC.2
      calc
        face1 ((occ1 cellA cellB hAB).comp (occ1 cellB cellC hBC)) cellC.2 =
            face1 (occ1 cellA cellB hAB) (face1 (occ1 cellB cellC hBC) cellC.2) :=
          (face1_comp (occ1 cellA cellB hAB) (occ1 cellB cellC hBC) cellC.2).symm
        _ = cellA.2 := by rw [face1_occ1 cellB cellC hBC, face1_occ1 cellA cellB hAB]
        _ = face1 (occ1 cellA cellC (hAB.trans hBC)) cellC.2 :=
          (face1_occ1 cellA cellC (hAB.trans hBC)).symm
    let cell1Face {n : ℕ} (cellA cellB : AllCell1 n) (hAB : cellA ≤ cellB) : Face cellB.1 :=
      faceImage (occ1 cellA cellB hAB) (fullFace cellA.1)
    have cell1Face_card {n : ℕ} (cellA cellB : AllCell1 n) (hAB : cellA ≤ cellB) :
        (cell1Face cellA cellB hAB).1.card = cellA.1 + 1 := by
      simp only [cell1Face, faceImage, fullFace, Finset.card_map, Finset.card_univ,
        Fintype.card_fin]
    have cell1Face_self {n : ℕ} (cellA : AllCell1 n) :
        cell1Face cellA cellA le_rfl = fullFace cellA.1 := by
      apply Subtype.ext
      change Finset.univ.map (occ1 cellA cellA le_rfl).toEmbedding = Finset.univ
      rw [occ1_self]
      exact Finset.map_refl
    have cell1Face_natural {n : ℕ} (cellA cellB cellC : AllCell1 n)
        (hAB : cellA ≤ cellB) (hBC : cellB ≤ cellC) :
        faceImage (occ1 cellB cellC hBC) (cell1Face cellA cellB hAB) =
          cell1Face cellA cellC (hAB.trans hBC) := by
      change faceImage (occ1 cellB cellC hBC)
        (faceImage (occ1 cellA cellB hAB) (fullFace cellA.1)) =
          faceImage (occ1 cellA cellC (hAB.trans hBC)) (fullFace cellA.1)
      rw [faceImage_comp, occ1_comp cellA cellB cellC hAB hBC]
    have cell1Face_subset {n : ℕ} (cellA cellC cellB : AllCell1 n)
        (hAB : cellA ≤ cellB) (hCB : cellC ≤ cellB) (hAC : cellA ≤ cellC) :
        (cell1Face cellA cellB hAB).1 ⊆ (cell1Face cellC cellB hCB).1 := by
      have he : cell1Face cellA cellB hAB =
          faceImage (occ1 cellC cellB hCB) (cell1Face cellA cellC hAC) :=
        (cell1Face_natural cellA cellC cellB hAC hCB).symm
      rw [he]
      exact faceImage_mono (occ1 cellC cellB hCB) (cell1Face cellA cellC hAC)
        (fullFace cellC.1) (Finset.subset_univ _)
    have cell1Face_strict {n : ℕ} (cellA cellC cellB : AllCell1 n)
        (hAB : cellA ≤ cellB) (hCB : cellC ≤ cellB) (hAC : cellA < cellC) :
        (cell1Face cellA cellB hAB).1 ⊂ (cell1Face cellC cellB hCB).1 := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨cell1Face_subset cellA cellC cellB hAB hCB hAC.le, ?_⟩
      intro he
      have hcard := congrArg Finset.card he
      rw [cell1Face_card cellA cellB hAB, cell1Face_card cellC cellB hCB] at hcard
      have hdim := cell1_dim_strict n hAC
      change cellA.1 < cellC.1 at hdim
      omega
    -- T1: the second subdivision has actual first-subdivision cells as vertices.
    let Cell2 (n r : ℕ) := Fin (r + 1) ↪o AllCell1 n
    let face2 {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1)) (C : Cell2 n r) : Cell2 n s := b.comp C
    let flag2 {n r : ℕ} (C : Cell2 n r) : Flag (C (Fin.last r)).1 r :=
      ⟨fun i => cell1Face (C i) (C (Fin.last r)) (C.monotone (Fin.le_last i)),
        fun i j hij => cell1Face_strict (C i) (C j) (C (Fin.last r))
          (C.monotone (Fin.le_last i)) (C.monotone (Fin.le_last j)) (C.strictMono hij),
        cell1Face_self (C (Fin.last r))⟩
    let char2 (n r : ℕ) (C : Cell2 n r) (u : Simplex r) : fatLevel n :=
      char1 n (C (Fin.last r)).1 (C (Fin.last r)).2 (chainBary _ r (flag2 C).1 u)
    have char2_continuous (n r : ℕ) (C : Cell2 n r) : Continuous (char2 n r C) :=
      (char1_continuous n _ _).comp (chainBary_continuous _ r (flag2 C).1)
    have flag2_face {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1)) (C : Cell2 n r)
        (i : Fin (s + 1)) :
        faceImage (occ1 (C (b (Fin.last s))) (C (Fin.last r)) (C.monotone (Fin.le_last _)))
          ((flag2 (face2 b C)).1 i) = (flag2 C).1 (b i) :=
      cell1Face_natural (C (b i)) (C (b (Fin.last s))) (C (Fin.last r))
        (C.monotone (b.monotone (Fin.le_last i))) (C.monotone (Fin.le_last _))
    have char2_face {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1))
        (C : Cell2 n r) (u : Simplex s) :
        char2 n s (face2 b C) u = char2 n r C (simplexMap b.toOrderHom u) := by
      let A := C (b (Fin.last s))
      let B := C (Fin.last r)
      have hAB : A ≤ B := C.monotone (Fin.le_last _)
      let d := occ1 A B hAB
      have hd : face1 d B.2 = A.2 := face1_occ1 A B hAB
      change char1 n A.1 A.2 (chainBary A.1 s (flag2 (face2 b C)).1 u) =
        char1 n B.1 B.2 (chainBary B.1 r (flag2 C).1 (simplexMap b.toOrderHom u))
      rw [← hd, char1_face]
      apply congrArg (char1 n B.1 B.2)
      rw [← chainBary_face, chainBary_chainface]
      congr 1
      funext i
      exact flag2_face b C i
    have cell1Face_injective {n : ℕ} (cellB cellA cellC : AllCell1 n)
        (hAB : cellA ≤ cellB) (hCB : cellC ≤ cellB)
        (he : cell1Face cellA cellB hAB = cell1Face cellC cellB hCB) : cellA = cellC := by
      have hdim : cellA.1 = cellC.1 := by
        have hcard := congrArg (fun S : Face cellB.1 => S.1.card) he
        rw [cell1Face_card cellA cellB hAB, cell1Face_card cellC cellB hCB] at hcard
        omega
      obtain ⟨r, cellA⟩ := cellA
      obtain ⟨s, cellC⟩ := cellC
      change r = s at hdim
      subst s
      let a := occ1 (⟨r, cellA⟩ : AllCell1 n) cellB hAB
      let b := occ1 (⟨r, cellC⟩ : AllCell1 n) cellB hCB
      have himage : Finset.univ.map a.toEmbedding = Finset.univ.map b.toEmbedding :=
        congrArg Subtype.val he
      have hrange : Set.range a = Set.range b := by
        ext j
        have hj := Finset.ext_iff.mp himage j
        simp only [Finset.mem_map, Finset.mem_univ, true_and] at hj
        exact hj
      have hab : a = b := by
        apply DFunLike.ext
        intro i
        exact congrFun ((a.strictMono.range_inj b.strictMono).mp hrange) i
      have hac : cellA = cellC := by
        calc
          cellA = face1 a cellB.2 := (face1_occ1 ⟨r, cellA⟩ cellB hAB).symm
          _ = face1 b cellB.2 := by rw [hab]
          _ = cellC := face1_occ1 ⟨r, cellC⟩ cellB hCB
      exact congrArg (Sigma.mk r) hac
    -- Move a chain to any upper first-subdivision cell, without a dimension cast.
    have char2_in_upper {n r : ℕ} (C : Cell2 n r) (cellB : AllCell1 n)
        (hCB : C (Fin.last r) ≤ cellB) (u : Simplex r) :
        char2 n r C u = char1 n cellB.1 cellB.2
          (chainBary cellB.1 r
            (fun i => cell1Face (C i) cellB ((C.monotone (Fin.le_last i)).trans hCB)) u) := by
      let cellA := C (Fin.last r)
      let a := occ1 cellA cellB hCB
      have ha : face1 a cellB.2 = cellA.2 := face1_occ1 cellA cellB hCB
      change char1 n cellA.1 cellA.2 (chainBary cellA.1 r (flag2 C).1 u) = _
      rw [← ha, char1_face]
      apply congrArg (char1 n cellB.1 cellB.2)
      rw [← chainBary_face]
      congr 1
      funext i
      exact cell1Face_natural (C i) cellA cellB (C.monotone (Fin.le_last i)) hCB
    have char2_positive_unique (n r s : ℕ) (C : Cell2 n r) (D : Cell2 n s)
        (u : Simplex r) (v : Simplex s) (hu : ∀ i, 0 < u.1 i) (hv : ∀ i, 0 < v.1 i)
        (he : char2 n r C u = char2 n s D v) :
        (⟨r, (C, u)⟩ : Σ k, Cell2 n k × Simplex k) = ⟨s, (D, v)⟩ := by
      have hmax := char1_positive_unique n (C (Fin.last r)).1 (D (Fin.last s)).1
        (C (Fin.last r)).2 (D (Fin.last s)).2
        (chainBary _ r (flag2 C).1 u) (chainBary _ s (flag2 D).1 v)
        (flagBary_positive _ r (flag2 C) u hu) (flagBary_positive _ s (flag2 D) v hv) he
      have htop : C (Fin.last r) = D (Fin.last s) := by
        simpa only [Sigma.eta] using congrArg
          (fun x : Σ k, Cell1 n k × Simplex k => (⟨x.1, x.2.1⟩ : AllCell1 n)) hmax
      let cellB := C (Fin.last r)
      have hDB : D (Fin.last s) ≤ cellB := le_of_eq htop.symm
      have hCi (i : Fin (r + 1)) : C i ≤ cellB := C.monotone (Fin.le_last i)
      have hDi (i : Fin (s + 1)) : D i ≤ cellB :=
        (D.monotone (Fin.le_last i)).trans hDB
      let P : Fin (r + 1) → Face cellB.1 := fun i => cell1Face (C i) cellB (hCi i)
      let Q : Fin (s + 1) → Face cellB.1 := fun i => cell1Face (D i) cellB (hDi i)
      have hP : ∀ i j, i < j → (P i).1 ⊂ (P j).1 := fun i j hij =>
        cell1Face_strict (C i) (C j) cellB (hCi i) (hCi j) (C.strictMono hij)
      have hQ : ∀ i j, i < j → (Q i).1 ⊂ (Q j).1 := fun i j hij =>
        cell1Face_strict (D i) (D j) cellB (hDi i) (hDi j) (D.strictMono hij)
      have hchar : char1 n cellB.1 cellB.2 (chainBary cellB.1 r P u) =
          char1 n cellB.1 cellB.2 (chainBary cellB.1 s Q v) :=
        (char2_in_upper C cellB le_rfl u).symm.trans
          (he.trans (char2_in_upper D cellB hDB v))
      have hcoord : chainBary cellB.1 r P u = chainBary cellB.1 s Q v :=
        char1_injective n cellB.1 cellB.2 hchar
      have hchain := chainBary_positive_unique cellB.1 r s P Q hP hQ u v hu hv hcoord
      have hrs : r = s := congrArg Sigma.fst hchain
      subst s
      have hpairs : (P, u) = (Q, v) := eq_of_heq (Sigma.mk.inj_iff.mp hchain).2
      have hCD : C = D := by
        apply DFunLike.ext
        intro i
        exact cell1Face_injective cellB (C i) (D i) (hCi i) (hDi i)
          (congrFun (congrArg Prod.fst hpairs) i)
      have huv : u = v := congrArg Prod.snd hpairs
      subst D
      subst v
      rfl
    -- T1: every chain of faces in a first cell gives a second-subdivision cell.
    let faceCell1 {n q : ℕ} (cellA : Cell1 n q) (S : Face q) : AllCell1 n :=
      ⟨faceDim S, face1 (faceEnum S) cellA⟩
    have faceCell1_le {n q : ℕ} (cellA : Cell1 n q) (S : Face q) :
        faceCell1 cellA S ≤ (⟨q, cellA⟩ : AllCell1 n) :=
      ⟨faceEnum S, rfl⟩
    have faceEnum_image_full {q : ℕ} (S : Face q) :
        faceImage (faceEnum S) (fullFace (faceDim S)) = S := by
      apply Subtype.ext
      ext j
      change j ∈ Finset.univ.map (faceEnum S).toEmbedding ↔ j ∈ S.1
      simp only [Finset.mem_map, Finset.mem_univ, true_and]
      exact Set.ext_iff.mp (faceEnum_range S) j
    have cell1Face_faceCell1 {n q : ℕ} (cellA : Cell1 n q) (S : Face q) :
        cell1Face (faceCell1 cellA S) ⟨q, cellA⟩ (faceCell1_le cellA S) = S := by
      change faceImage (occ1 (faceCell1 cellA S) ⟨q, cellA⟩ (faceCell1_le cellA S))
        (fullFace (faceDim S)) = S
      rw [occ1_unique (faceCell1 cellA S) ⟨q, cellA⟩ (faceCell1_le cellA S) (faceEnum S) rfl]
      exact faceEnum_image_full S
    have faceCell1_mono {n q : ℕ} (cellA : Cell1 n q) (S T : Face q)
        (hST : S.1 ⊆ T.1) : faceCell1 cellA S ≤ faceCell1 cellA T := by
      obtain ⟨a, ha⟩ := embedding_factor (faceEnum T) (faceEnum S) (by
        intro i
        rw [faceEnum_range T]
        exact hST (faceEnum_mem S i))
      refine ⟨a, ?_⟩
      change face1 a (face1 (faceEnum T) cellA) = face1 (faceEnum S) cellA
      rw [face1_comp, ha]
    have faceCell1_strict {n q : ℕ} (cellA : Cell1 n q) (S T : Face q)
        (hST : S.1 ⊂ T.1) : faceCell1 cellA S < faceCell1 cellA T := by
      apply lt_of_le_of_ne (faceCell1_mono cellA S T hST.subset)
      intro he
      have hd := congrArg Sigma.fst he
      have hcard := Finset.card_lt_card hST
      change faceDim S = faceDim T at hd
      rw [faceCard S, faceCard T] at hcard
      omega
    let chainCell2 {n q r : ℕ} (cellA : Cell1 n q) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) : Cell2 n r :=
      OrderEmbedding.ofStrictMono (fun i => faceCell1 cellA (C i))
        (fun i j hij => faceCell1_strict cellA (C i) (C j) (hC i j hij))
    have chainCell2_char {n q r : ℕ} (cellA : Cell1 n q) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) (u : Simplex r) :
        char2 n r (chainCell2 cellA C hC) u = char1 n q cellA (chainBary q r C u) := by
      rw [char2_in_upper (chainCell2 cellA C hC) ⟨q, cellA⟩ (faceCell1_le cellA (C (Fin.last r))) u]
      apply congrArg (char1 n q cellA)
      congr 1
      funext i
      exact cell1Face_faceCell1 cellA (C i)
    have char2_positive_rep (n : ℕ) (x : fatLevel n) :
        ∃ r : ℕ, ∃ C : Cell2 n r, ∃ u : Simplex r,
          (∀ i, 0 < u.1 i) ∧ char2 n r C u = x := by
      obtain ⟨q, cellA, v, hv, hx⟩ := char1_positive_rep n x
      obtain ⟨r, C, u, hC, hu, he, _⟩ := simplex_threshold_chain q v
      refine ⟨r, chainCell2 cellA C hC, u, hu, ?_⟩
      rw [chainCell2_char cellA C hC u, show chainBary q r C u = v from Subtype.ext (funext he)]
      exact hx
    have char2_final (n : ℕ) (Z : Type) [TopologicalSpace Z] (f : fatLevel n → Z)
        (hf : ∀ r (C : Cell2 n r), Continuous (f ∘ char2 n r C)) : Continuous f := by
      apply char1_final n Z f
      intro q cellA
      apply continuous_of_chainBary q Z (f ∘ char1 n q cellA)
      intro r C hC
      have he : (f ∘ char1 n q cellA) ∘ chainBary q r C =
          f ∘ char2 n r (chainCell2 cellA C hC) := by
        funext u
        exact congrArg f (chainCell2_char cellA C hC u).symm
      rw [he]
      exact hf r (chainCell2 cellA C hC)
    have face2_id (n r : ℕ) (C : Cell2 n r) : face2 (OrderEmbedding.id _) C = C :=
      OrderEmbedding.id_comp C
    have face2_comp {n r s t : ℕ} (a : Fin (t + 1) ↪o Fin (s + 1))
        (b : Fin (s + 1) ↪o Fin (r + 1)) (C : Cell2 n r) :
        face2 a (face2 b C) = face2 (a.comp b) C := by
      rfl
    have face2_occurrence_injective {n r s : ℕ} (C : Cell2 n r) :
        Function.Injective (fun b : Fin (s + 1) ↪o Fin (r + 1) => face2 b C) := by
      intro a b he
      apply DFunLike.ext
      intro i
      apply C.injective
      exact DFunLike.congr_fun he i
    have char2_support_unique (n r p q : ℕ) (C : Cell2 n r)
        (a : Fin (p + 1) ↪o Fin (r + 1)) (b : Fin (q + 1) ↪o Fin (r + 1))
        (u : Simplex p) (v : Simplex q) (hu : ∀ i, 0 < u.1 i) (hv : ∀ i, 0 < v.1 i)
        (he : char2 n r C (simplexMap a.toOrderHom u) =
          char2 n r C (simplexMap b.toOrderHom v)) :
        (⟨p, (a, u)⟩ : Σ k, (Fin (k + 1) ↪o Fin (r + 1)) × Simplex k) = ⟨q, (b, v)⟩ := by
      have hfaces : char2 n p (face2 a C) u = char2 n q (face2 b C) v := by
        rw [char2_face a C u, char2_face b C v]
        exact he
      have hrep := char2_positive_unique n p q (face2 a C) (face2 b C) u v hu hv hfaces
      have hpq : p = q := congrArg Sigma.fst hrep
      subst q
      have hpairs : (face2 a C, u) = (face2 b C, v) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hrep).2
      have hab : a = b := face2_occurrence_injective C (congrArg Prod.fst hpairs)
      have huv : u = v := congrArg Prod.snd hpairs
      subst b
      subst v
      rfl
    have char2_injective (n r : ℕ) (C : Cell2 n r) : Function.Injective (char2 n r C) := by
      intro u v huv
      obtain ⟨p, a, u', hu', hua⟩ := simplex_support r u
      obtain ⟨s, b, v', hv', hvb⟩ := simplex_support r v
      have he : char2 n r C (simplexMap a.toOrderHom u') =
          char2 n r C (simplexMap b.toOrderHom v') := by
        rw [hua, hvb]
        exact huv
      have hrep := char2_support_unique n r p s C a b u' v' hu' hv' he
      have hps : p = s := congrArg Sigma.fst hrep
      subst s
      have hpairs : (a, u') = (b, v') := eq_of_heq (Sigma.mk.inj_iff.mp hrep).2
      have hab : a = b := congrArg Prod.fst hpairs
      have huv' : u' = v' := congrArg Prod.snd hpairs
      calc
        u = simplexMap a.toOrderHom u' := hua.symm
        _ = simplexMap b.toOrderHom v' := by rw [hab, huv']
        _ = v := hvb
    have char2_isClosedEmbedding (n r : ℕ) (C : Cell2 n r) :
        IsClosedEmbedding (char2 n r C) := by
      letI : CompactSpace (Simplex r) := simplex_compact r
      letI : T2Space (fatLevel n) := fat_t2 n
      exact (char2_continuous n r C).isClosedEmbedding (char2_injective n r C)
    have char2_range_closed (n r : ℕ) (C : Cell2 n r) :
        IsClosed (Set.range (char2 n r C)) := (char2_isClosedEmbedding n r C).isClosed_range
    -- T1: the face order on second-subdivision cells.
    let AllCell2 (n : ℕ) := Σ r, Cell2 n r
    let faceLE2 (n : ℕ) (cellA cellB : AllCell2 n) : Prop :=
      ∃ b : Fin (cellA.1 + 1) ↪o Fin (cellB.1 + 1), face2 b cellB.2 = cellA.2
    have faceLE2_refl (n : ℕ) (cellA : AllCell2 n) : faceLE2 n cellA cellA :=
      ⟨OrderEmbedding.id _, face2_id n cellA.1 cellA.2⟩
    have faceLE2_trans (n : ℕ) (cellA cellB cellC : AllCell2 n)
        (hAB : faceLE2 n cellA cellB) (hBC : faceLE2 n cellB cellC) :
        faceLE2 n cellA cellC := by
      obtain ⟨a, ha⟩ := hAB
      obtain ⟨b, hb⟩ := hBC
      refine ⟨a.comp b, ?_⟩
      rw [← face2_comp, hb, ha]
    have faceLE2_dim (n : ℕ) (cellA cellB : AllCell2 n)
        (hAB : faceLE2 n cellA cellB) : cellA.1 ≤ cellB.1 := by
      obtain ⟨b, _⟩ := hAB
      have hcard := Fintype.card_le_of_injective b b.injective
      simp only [Fintype.card_fin] at hcard
      omega
    have faceLE2_eq_of_dim (n r : ℕ) (cellA cellB : Cell2 n r)
        (hAB : faceLE2 n ⟨r, cellA⟩ ⟨r, cellB⟩) : cellA = cellB := by
      obtain ⟨b, hb⟩ := hAB
      have hid : b = OrderEmbedding.id _ := by
        apply DFunLike.ext
        intro i
        exact DFunLike.congr_fun (b.toOrderHom.eq_id_of_injective b.injective) i
      rw [hid, face2_id] at hb
      exact hb.symm
    have faceLE2_antisymm (n : ℕ) (cellA cellB : AllCell2 n)
        (hAB : faceLE2 n cellA cellB) (hBA : faceLE2 n cellB cellA) :
        cellA = cellB := by
      obtain ⟨r, cellA⟩ := cellA
      obtain ⟨s, cellB⟩ := cellB
      have hrs : r = s :=
        Nat.le_antisymm (faceLE2_dim n _ _ hAB) (faceLE2_dim n _ _ hBA)
      subst s
      exact congrArg (Sigma.mk r) (faceLE2_eq_of_dim n r cellA cellB hAB)
    letI (n : ℕ) : PartialOrder (AllCell2 n) :=
      { le := faceLE2 n
        le_refl := faceLE2_refl n
        le_trans := fun cellA cellB cellC => faceLE2_trans n cellA cellB cellC
        le_antisymm := fun cellA cellB => faceLE2_antisymm n cellA cellB }
    have cell2_dim_strict (n : ℕ) : StrictMono (fun cellA : AllCell2 n => cellA.1) := by
      intro cellA cellB hAB
      have hle := faceLE2_dim n cellA cellB hAB.le
      apply lt_of_le_of_ne hle
      intro he
      obtain ⟨r, cellA⟩ := cellA
      obtain ⟨s, cellB⟩ := cellB
      change r = s at he
      subst s
      have hab := faceLE2_eq_of_dim n r cellA cellB hAB.le
      subst cellB
      exact (lt_irrefl (⟨r, cellA⟩ : AllCell2 n)) hAB

    -- Each second-subdivision face has a unique occurrence in its upper cell.
    let occ2 {n : ℕ} (cellA cellB : AllCell2 n) (hAB : cellA ≤ cellB) :
        Fin (cellA.1 + 1) ↪o Fin (cellB.1 + 1) :=
      Classical.choose (show faceLE2 n cellA cellB from hAB)
    have face2_occ2 {n : ℕ} (cellA cellB : AllCell2 n) (hAB : cellA ≤ cellB) :
        face2 (occ2 cellA cellB hAB) cellB.2 = cellA.2 :=
      Classical.choose_spec (show faceLE2 n cellA cellB from hAB)
    have occ2_unique {n : ℕ} (cellA cellB : AllCell2 n) (hAB : cellA ≤ cellB)
        (b : Fin (cellA.1 + 1) ↪o Fin (cellB.1 + 1))
        (hb : face2 b cellB.2 = cellA.2) : occ2 cellA cellB hAB = b := by
      apply face2_occurrence_injective cellB.2
      exact (face2_occ2 cellA cellB hAB).trans hb.symm
    have occ2_self {n : ℕ} (cellA : AllCell2 n) :
        occ2 cellA cellA le_rfl = OrderEmbedding.id _ :=
      occ2_unique cellA cellA le_rfl (OrderEmbedding.id _) (face2_id n cellA.1 cellA.2)
    have occ2_comp {n : ℕ} (cellA cellB cellC : AllCell2 n)
        (hAB : cellA ≤ cellB) (hBC : cellB ≤ cellC) :
        (occ2 cellA cellB hAB).comp (occ2 cellB cellC hBC) =
          occ2 cellA cellC (hAB.trans hBC) := by
      apply face2_occurrence_injective cellC.2
      calc
        face2 ((occ2 cellA cellB hAB).comp (occ2 cellB cellC hBC)) cellC.2 =
            face2 (occ2 cellA cellB hAB) (face2 (occ2 cellB cellC hBC) cellC.2) :=
          (face2_comp (occ2 cellA cellB hAB) (occ2 cellB cellC hBC) cellC.2).symm
        _ = cellA.2 := by rw [face2_occ2 cellB cellC hBC, face2_occ2 cellA cellB hAB]
        _ = face2 (occ2 cellA cellC (hAB.trans hBC)) cellC.2 :=
          (face2_occ2 cellA cellC (hAB.trans hBC)).symm
    -- T2/T8: barycentric coordinates descend through the unique positive support.
    let chainWeight {V : Type} (r : ℕ) (C : Fin (r + 1) → V)
        (u : Simplex r) (v : V) : ℝ := ∑ i, if C i = v then u.1 i else 0
    have chainWeight_nonneg {V : Type} (r : ℕ) (C : Fin (r + 1) → V)
        (u : Simplex r) (v : V) : 0 ≤ chainWeight r C u v := by
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact u.2.1 i
      · exact le_rfl
    have chainWeight_continuous {V : Type} (r : ℕ) (C : Fin (r + 1) → V) (v : V) :
        Continuous (fun u : Simplex r => chainWeight r C u v) := by
      apply continuous_finset_sum
      intro i _
      by_cases hi : C i = v
      · simp only [hi, if_true]
        exact (continuous_apply i).comp continuous_subtype_val
      · simp only [hi, if_false]
        exact continuous_const
    have chainWeight_image {V : Type} (r : ℕ) (C : Fin (r + 1) → V)
        (hC : Function.Injective C) (u : Simplex r) (i : Fin (r + 1)) :
        chainWeight r C u (C i) = u.1 i := by
      change (∑ j, if C j = C i then u.1 j else 0) = u.1 i
      simp only [hC.eq_iff]
      exact Fintype.sum_ite_eq' i u.1
    have chainWeight_outside {V : Type} (r : ℕ) (C : Fin (r + 1) → V)
        (u : Simplex r) (v : V) (hv : v ∉ Set.range C) : chainWeight r C u v = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun hi => hv ⟨i, hi⟩)
    have chainWeight_face {V : Type} {r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1))
        (C : Fin (r + 1) → V) (u : Simplex s) (v : V) :
        chainWeight s (fun i => C (b i)) u v =
          chainWeight r C (simplexMap b.toOrderHom u) v := by
      change (∑ i, if C (b i) = v then u.1 i else 0) =
        ∑ j, if C j = v then (∑ i, if b i = j then u.1 i else 0) else 0
      have hsum (j : Fin (r + 1)) :
          (if C j = v then (∑ i, if b i = j then u.1 i else 0) else 0) =
            ∑ i, if C j = v then (if b i = j then u.1 i else 0) else 0 := by
        split_ifs <;> simp
      simp_rw [hsum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      have hterm (j : Fin (r + 1)) :
          (if C j = v then (if b i = j then u.1 i else 0) else 0) =
            if b i = j then (if C (b i) = v then u.1 i else 0) else 0 := by
        by_cases hij : b i = j
        · subst j
          simp
        · simp [hij]
      simp_rw [hterm]
      simp
    have chain_coordinate_data (V X : Type) [PartialOrder V] [TopologicalSpace X]
        (ch : ∀ r, (Fin (r + 1) ↪o V) → Simplex r → X)
        (hface : ∀ {r s} (b : Fin (s + 1) ↪o Fin (r + 1))
          (C : Fin (r + 1) ↪o V) (u : Simplex s),
          ch s (b.comp C) u = ch r C (simplexMap b.toOrderHom u))
        (hrep : ∀ x : X, ∃ r, ∃ C : Fin (r + 1) ↪o V, ∃ u : Simplex r,
          (∀ i, 0 < u.1 i) ∧ ch r C u = x)
        (hunique : ∀ r s (C : Fin (r + 1) ↪o V) (D : Fin (s + 1) ↪o V)
          (u : Simplex r) (v : Simplex s), (∀ i, 0 < u.1 i) → (∀ i, 0 < v.1 i) →
          ch r C u = ch s D v →
          (⟨r, (C, u)⟩ : Σ k, (Fin (k + 1) ↪o V) × Simplex k) = ⟨s, (D, v)⟩)
        (hfinal : ∀ f : X → ℝ, (∀ r C, Continuous (f ∘ ch r C)) → Continuous f) :
        ∃ coord : X → V → ℝ,
          (∀ r C u v, coord (ch r C u) v = chainWeight r C u v) ∧
          (∀ v, Continuous (fun x => coord x v)) := by
      choose dim cell weight hpos hpoint using hrep
      let coord (x : X) (v : V) : ℝ := chainWeight (dim x) (cell x) (weight x) v
      have hvaluepos (r : ℕ) (C : Fin (r + 1) ↪o V) (u : Simplex r)
          (hu : ∀ i, 0 < u.1 i) (v : V) : coord (ch r C u) v = chainWeight r C u v := by
        have he := hunique (dim (ch r C u)) r (cell (ch r C u)) C
          (weight (ch r C u)) u (hpos _) hu (hpoint _)
        exact congrArg (fun a : Σ k, (Fin (k + 1) ↪o V) × Simplex k =>
          chainWeight a.1 a.2.1 a.2.2 v) he
      have hvalue (r : ℕ) (C : Fin (r + 1) ↪o V) (u : Simplex r) (v : V) :
          coord (ch r C u) v = chainWeight r C u v := by
        obtain ⟨s, b, u', hu', he⟩ := simplex_support r u
        calc
          coord (ch r C u) v = coord (ch s (b.comp C) u') v := by rw [hface, he]
          _ = chainWeight s (b.comp C) u' v := hvaluepos s (b.comp C) u' hu' v
          _ = chainWeight r C (simplexMap b.toOrderHom u') v := chainWeight_face b C u' v
          _ = chainWeight r C u v := by rw [he]
      refine ⟨coord, hvalue, ?_⟩
      intro v
      apply hfinal
      intro r C
      exact (chainWeight_continuous r C v).congr (fun u => (hvalue r C u v).symm)
    -- T1: a lower second-subdivision cell determines its vertex face upstairs.
    let cell2Face {n : ℕ} (cellA cellB : AllCell2 n) (hAB : cellA ≤ cellB) : Face cellB.1 :=
      faceImage (occ2 cellA cellB hAB) (fullFace cellA.1)
    have cell2Face_card {n : ℕ} (cellA cellB : AllCell2 n) (hAB : cellA ≤ cellB) :
        (cell2Face cellA cellB hAB).1.card = cellA.1 + 1 := by
      simp only [cell2Face, faceImage, fullFace, Finset.card_map, Finset.card_univ,
        Fintype.card_fin]
    have cell2Face_self {n : ℕ} (cellA : AllCell2 n) :
        cell2Face cellA cellA le_rfl = fullFace cellA.1 := by
      apply Subtype.ext
      change Finset.univ.map (occ2 cellA cellA le_rfl).toEmbedding = Finset.univ
      rw [occ2_self cellA]
      exact Finset.map_refl
    have cell2Face_natural {n : ℕ} (cellA cellB cellC : AllCell2 n)
        (hAB : cellA ≤ cellB) (hBC : cellB ≤ cellC) :
        faceImage (occ2 cellB cellC hBC) (cell2Face cellA cellB hAB) =
          cell2Face cellA cellC (hAB.trans hBC) := by
      change faceImage (occ2 cellB cellC hBC)
        (faceImage (occ2 cellA cellB hAB) (fullFace cellA.1)) =
          faceImage (occ2 cellA cellC (hAB.trans hBC)) (fullFace cellA.1)
      rw [faceImage_comp (occ2 cellA cellB hAB) (occ2 cellB cellC hBC) (fullFace cellA.1),
        occ2_comp cellA cellB cellC hAB hBC]
    have cell2Face_subset {n : ℕ} (cellA cellC cellB : AllCell2 n)
        (hAB : cellA ≤ cellB) (hCB : cellC ≤ cellB) (hAC : cellA ≤ cellC) :
        (cell2Face cellA cellB hAB).1 ⊆ (cell2Face cellC cellB hCB).1 := by
      have he : cell2Face cellA cellB hAB =
          faceImage (occ2 cellC cellB hCB) (cell2Face cellA cellC hAC) :=
        (cell2Face_natural cellA cellC cellB hAC hCB).symm
      rw [he]
      exact faceImage_mono (occ2 cellC cellB hCB) (cell2Face cellA cellC hAC)
        (fullFace cellC.1) (Finset.subset_univ _)
    have cell2Face_strict {n : ℕ} (cellA cellC cellB : AllCell2 n)
        (hAB : cellA ≤ cellB) (hCB : cellC ≤ cellB) (hAC : cellA < cellC) :
        (cell2Face cellA cellB hAB).1 ⊂ (cell2Face cellC cellB hCB).1 := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨cell2Face_subset cellA cellC cellB hAB hCB hAC.le, ?_⟩
      intro he
      have hcard := congrArg Finset.card he
      rw [cell2Face_card cellA cellB hAB, cell2Face_card cellC cellB hCB] at hcard
      have hdim := cell2_dim_strict n hAC
      change cellA.1 < cellC.1 at hdim
      omega
    have cell2Face_injective {n : ℕ} (cellB cellA cellC : AllCell2 n)
        (hAB : cellA ≤ cellB) (hCB : cellC ≤ cellB)
        (he : cell2Face cellA cellB hAB = cell2Face cellC cellB hCB) : cellA = cellC := by
      have hdim : cellA.1 = cellC.1 := by
        have hcard := congrArg (fun S : Face cellB.1 => S.1.card) he
        rw [cell2Face_card cellA cellB hAB, cell2Face_card cellC cellB hCB] at hcard
        omega
      obtain ⟨r, cellA⟩ := cellA
      obtain ⟨s, cellC⟩ := cellC
      change r = s at hdim
      subst s
      let a := occ2 (⟨r, cellA⟩ : AllCell2 n) cellB hAB
      let b := occ2 (⟨r, cellC⟩ : AllCell2 n) cellB hCB
      have himage : Finset.univ.map a.toEmbedding = Finset.univ.map b.toEmbedding :=
        congrArg Subtype.val he
      have hrange : Set.range a = Set.range b := by
        ext j
        have hj := Finset.ext_iff.mp himage j
        simp only [Finset.mem_map, Finset.mem_univ, true_and] at hj
        exact hj
      have hab : a = b := by
        apply DFunLike.ext
        intro i
        exact congrFun ((a.strictMono.range_inj b.strictMono).mp hrange) i
      have hac : cellA = cellC := by
        calc
          cellA = face2 a cellB.2 := (face2_occ2 ⟨r, cellA⟩ cellB hAB).symm
          _ = face2 b cellB.2 := by rw [hab]
          _ = cellC := face2_occ2 ⟨r, cellC⟩ cellB hCB
      exact congrArg (Sigma.mk r) hac
    -- T1: the third subdivision has actual second-subdivision cells as vertices.
    let Cell3 (n r : ℕ) := Fin (r + 1) ↪o AllCell2 n
    let face3 {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1)) (C : Cell3 n r) : Cell3 n s := b.comp C
    let flag3 {n r : ℕ} (C : Cell3 n r) : Flag (C (Fin.last r)).1 r :=
      ⟨fun i => cell2Face (C i) (C (Fin.last r)) (C.monotone (Fin.le_last i)),
        fun i j hij => cell2Face_strict (C i) (C j) (C (Fin.last r))
          (C.monotone (Fin.le_last i)) (C.monotone (Fin.le_last j)) (C.strictMono hij),
        cell2Face_self (C (Fin.last r))⟩
    let char3 (n r : ℕ) (C : Cell3 n r) (u : Simplex r) : fatLevel n :=
      char2 n (C (Fin.last r)).1 (C (Fin.last r)).2 (chainBary _ r (flag3 C).1 u)
    have char3_continuous (n r : ℕ) (C : Cell3 n r) : Continuous (char3 n r C) :=
      (char2_continuous n _ _).comp (chainBary_continuous _ r (flag3 C).1)
    have flag3_face {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1)) (C : Cell3 n r)
        (i : Fin (s + 1)) :
        faceImage (occ2 (C (b (Fin.last s))) (C (Fin.last r)) (C.monotone (Fin.le_last _)))
          ((flag3 (face3 b C)).1 i) = (flag3 C).1 (b i) :=
      cell2Face_natural (C (b i)) (C (b (Fin.last s))) (C (Fin.last r))
        (C.monotone (b.monotone (Fin.le_last i))) (C.monotone (Fin.le_last _))
    have char3_face {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1))
        (C : Cell3 n r) (u : Simplex s) :
        char3 n s (face3 b C) u = char3 n r C (simplexMap b.toOrderHom u) := by
      let A := C (b (Fin.last s))
      let B := C (Fin.last r)
      have hAB : A ≤ B := C.monotone (Fin.le_last _)
      let d := occ2 A B hAB
      have hd : face2 d B.2 = A.2 := face2_occ2 A B hAB
      change char2 n A.1 A.2 (chainBary A.1 s (flag3 (face3 b C)).1 u) =
        char2 n B.1 B.2 (chainBary B.1 r (flag3 C).1 (simplexMap b.toOrderHom u))
      rw [← hd, char2_face d B.2 (chainBary A.1 s (flag3 (face3 b C)).1 u)]
      apply congrArg (char2 n B.1 B.2)
      rw [← chainBary_face d (flag3 (face3 b C)).1 u,
        chainBary_chainface b (flag3 C).1 u]
      congr 1
      funext i
      exact flag3_face b C i
    -- Move a chain to any upper second-subdivision cell, without a dimension cast.
    have char3_in_upper {n r : ℕ} (C : Cell3 n r) (cellB : AllCell2 n)
        (hCB : C (Fin.last r) ≤ cellB) (u : Simplex r) :
        char3 n r C u = char2 n cellB.1 cellB.2
          (chainBary cellB.1 r
            (fun i => cell2Face (C i) cellB ((C.monotone (Fin.le_last i)).trans hCB)) u) := by
      let cellA := C (Fin.last r)
      let a := occ2 cellA cellB hCB
      have ha : face2 a cellB.2 = cellA.2 := face2_occ2 cellA cellB hCB
      change char2 n cellA.1 cellA.2 (chainBary cellA.1 r (flag3 C).1 u) = _
      rw [← ha, char2_face a cellB.2 (chainBary cellA.1 r (flag3 C).1 u)]
      apply congrArg (char2 n cellB.1 cellB.2)
      rw [← chainBary_face a (flag3 C).1 u]
      congr 1
      funext i
      exact cell2Face_natural (C i) cellA cellB (C.monotone (Fin.le_last i)) hCB
    have char3_positive_unique (n r s : ℕ) (C : Cell3 n r) (D : Cell3 n s)
        (u : Simplex r) (v : Simplex s) (hu : ∀ i, 0 < u.1 i) (hv : ∀ i, 0 < v.1 i)
        (he : char3 n r C u = char3 n s D v) :
        (⟨r, (C, u)⟩ : Σ k, Cell3 n k × Simplex k) = ⟨s, (D, v)⟩ := by
      have hmax := char2_positive_unique n (C (Fin.last r)).1 (D (Fin.last s)).1
        (C (Fin.last r)).2 (D (Fin.last s)).2
        (chainBary _ r (flag3 C).1 u) (chainBary _ s (flag3 D).1 v)
        (flagBary_positive _ r (flag3 C) u hu) (flagBary_positive _ s (flag3 D) v hv) he
      have htop : C (Fin.last r) = D (Fin.last s) := by
        simpa only [Sigma.eta] using congrArg
          (fun x : Σ k, Cell2 n k × Simplex k => (⟨x.1, x.2.1⟩ : AllCell2 n)) hmax
      let cellB := C (Fin.last r)
      have hDB : D (Fin.last s) ≤ cellB := le_of_eq htop.symm
      have hCi (i : Fin (r + 1)) : C i ≤ cellB := C.monotone (Fin.le_last i)
      have hDi (i : Fin (s + 1)) : D i ≤ cellB :=
        (D.monotone (Fin.le_last i)).trans hDB
      let P : Fin (r + 1) → Face cellB.1 := fun i => cell2Face (C i) cellB (hCi i)
      let Q : Fin (s + 1) → Face cellB.1 := fun i => cell2Face (D i) cellB (hDi i)
      have hP : ∀ i j, i < j → (P i).1 ⊂ (P j).1 := fun i j hij =>
        cell2Face_strict (C i) (C j) cellB (hCi i) (hCi j) (C.strictMono hij)
      have hQ : ∀ i j, i < j → (Q i).1 ⊂ (Q j).1 := fun i j hij =>
        cell2Face_strict (D i) (D j) cellB (hDi i) (hDi j) (D.strictMono hij)
      have hchar : char2 n cellB.1 cellB.2 (chainBary cellB.1 r P u) =
          char2 n cellB.1 cellB.2 (chainBary cellB.1 s Q v) :=
        (char3_in_upper C cellB le_rfl u).symm.trans
          (he.trans (char3_in_upper D cellB hDB v))
      have hcoord : chainBary cellB.1 r P u = chainBary cellB.1 s Q v :=
        char2_injective n cellB.1 cellB.2 hchar
      have hchain := chainBary_positive_unique cellB.1 r s P Q hP hQ u v hu hv hcoord
      have hrs : r = s := congrArg Sigma.fst hchain
      subst s
      have hpairs : (P, u) = (Q, v) := eq_of_heq (Sigma.mk.inj_iff.mp hchain).2
      have hCD : C = D := by
        apply DFunLike.ext
        intro i
        exact cell2Face_injective cellB (C i) (D i) (hCi i) (hDi i)
          (congrFun (congrArg Prod.fst hpairs) i)
      have huv : u = v := congrArg Prod.snd hpairs
      subst D
      subst v
      rfl
    -- T1: every chain of faces in a second cell gives a third-subdivision cell.
    let faceCell2 {n q : ℕ} (cellA : Cell2 n q) (S : Face q) : AllCell2 n :=
      ⟨faceDim S, face2 (faceEnum S) cellA⟩
    have faceCell2_le {n q : ℕ} (cellA : Cell2 n q) (S : Face q) :
        faceCell2 cellA S ≤ (⟨q, cellA⟩ : AllCell2 n) :=
      ⟨faceEnum S, rfl⟩
    have cell2Face_faceCell2 {n q : ℕ} (cellA : Cell2 n q) (S : Face q) :
        cell2Face (faceCell2 cellA S) ⟨q, cellA⟩ (faceCell2_le cellA S) = S := by
      change faceImage (occ2 (faceCell2 cellA S) ⟨q, cellA⟩ (faceCell2_le cellA S))
        (fullFace (faceDim S)) = S
      rw [occ2_unique (faceCell2 cellA S) ⟨q, cellA⟩ (faceCell2_le cellA S) (faceEnum S) rfl]
      exact faceEnum_image_full S
    have faceCell2_mono {n q : ℕ} (cellA : Cell2 n q) (S T : Face q)
        (hST : S.1 ⊆ T.1) : faceCell2 cellA S ≤ faceCell2 cellA T := by
      obtain ⟨a, ha⟩ := embedding_factor (faceEnum T) (faceEnum S) (by
        intro i
        rw [faceEnum_range T]
        exact hST (faceEnum_mem S i))
      refine ⟨a, ?_⟩
      change face2 a (face2 (faceEnum T) cellA) = face2 (faceEnum S) cellA
      rw [face2_comp, ha]
    have faceCell2_strict {n q : ℕ} (cellA : Cell2 n q) (S T : Face q)
        (hST : S.1 ⊂ T.1) : faceCell2 cellA S < faceCell2 cellA T := by
      apply lt_of_le_of_ne (faceCell2_mono cellA S T hST.subset)
      intro he
      have hd := congrArg Sigma.fst he
      have hcard := Finset.card_lt_card hST
      change faceDim S = faceDim T at hd
      rw [faceCard S, faceCard T] at hcard
      omega
    let chainCell3 {n q r : ℕ} (cellA : Cell2 n q) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) : Cell3 n r :=
      OrderEmbedding.ofStrictMono (fun i => faceCell2 cellA (C i))
        (fun i j hij => faceCell2_strict cellA (C i) (C j) (hC i j hij))
    have chainCell3_char {n q r : ℕ} (cellA : Cell2 n q) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) (u : Simplex r) :
        char3 n r (chainCell3 cellA C hC) u = char2 n q cellA (chainBary q r C u) := by
      rw [char3_in_upper (chainCell3 cellA C hC) ⟨q, cellA⟩ (faceCell2_le cellA (C (Fin.last r))) u]
      apply congrArg (char2 n q cellA)
      congr 1
      funext i
      exact cell2Face_faceCell2 cellA (C i)
    have char3_positive_rep (n : ℕ) (x : fatLevel n) :
        ∃ r : ℕ, ∃ C : Cell3 n r, ∃ u : Simplex r,
          (∀ i, 0 < u.1 i) ∧ char3 n r C u = x := by
      obtain ⟨q, cellA, v, hv, hx⟩ := char2_positive_rep n x
      obtain ⟨r, C, u, hC, hu, he, _⟩ := simplex_threshold_chain q v
      refine ⟨r, chainCell3 cellA C hC, u, hu, ?_⟩
      rw [chainCell3_char cellA C hC u, show chainBary q r C u = v from Subtype.ext (funext he)]
      exact hx
    have char3_final (n : ℕ) (Z : Type) [TopologicalSpace Z] (f : fatLevel n → Z)
        (hf : ∀ r (C : Cell3 n r), Continuous (f ∘ char3 n r C)) : Continuous f := by
      apply char2_final n Z f
      intro q cellA
      apply continuous_of_chainBary q Z (f ∘ char2 n q cellA)
      intro r C hC
      have he : (f ∘ char2 n q cellA) ∘ chainBary q r C =
          f ∘ char3 n r (chainCell3 cellA C hC) := by
        funext u
        exact congrArg f (chainCell3_char cellA C hC u).symm
      rw [he]
      exact hf r (chainCell3 cellA C hC)
    -- T1: the actual zero subspace is a subcomplex of both subdivisions.
    let zeroCell1 {n : ℕ} (cellA : AllCell1 n) : Prop :=
      cellA.2.2.1 = zero n cellA.2.1
    have zeroCell1_face1 {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1))
        (cellA : Cell1 n r) (hA : zeroCell1 (⟨r, cellA⟩ : AllCell1 n)) :
        zeroCell1 (⟨s, face1 b cellA⟩ : AllCell1 n) := by
      change cellA.2.1 = zero n cellA.1 at hA
      change pull (faceEnum (cellA.2.2.1 (b (Fin.last s)))).toOrderHom cellA.2.1 =
        zero n (faceDim (cellA.2.2.1 (b (Fin.last s))))
      rw [hA, pull_zero]
    have zeroCell1_of_le {n : ℕ} (cellA cellB : AllCell1 n)
        (hAB : cellA ≤ cellB) (hB : zeroCell1 cellB) : zeroCell1 cellA := by
      obtain ⟨b, hb⟩ := (show faceLE1 n cellA cellB from hAB)
      have hface := zeroCell1_face1 b cellB.2 hB
      simpa only [hb] using hface
    have char1_mem_zero_of_zero (n r : ℕ) (cellA : Cell1 n r)
        (hA : zeroCell1 (⟨r, cellA⟩ : AllCell1 n)) (u : Simplex r) :
        char1 n r cellA u ∈ Set.range (zeroIncl n) := by
      change cellA.2.1 = zero n cellA.1 at hA
      refine ⟨zeroProjection cellA.1 (chainBary cellA.1 r cellA.2.2.1 u), ?_⟩
      change fatProjection n cellA.1 (zero n cellA.1)
          (chainBary cellA.1 r cellA.2.2.1 u) =
        fatProjection n cellA.1 cellA.2.1 (chainBary cellA.1 r cellA.2.2.1 u)
      exact congrArg (fun z => fatProjection n cellA.1 z
        (chainBary cellA.1 r cellA.2.2.1 u)) hA.symm
    have char1_positive_mem_zero_iff (n r : ℕ) (cellA : Cell1 n r)
        (u : Simplex r) (hu : ∀ i, 0 < u.1 i) :
        char1 n r cellA u ∈ Set.range (zeroIncl n) ↔
          zeroCell1 (⟨r, cellA⟩ : AllCell1 n) := by
      constructor
      · intro hx
        change cellA.2.1 = zero n cellA.1
        by_contra hA
        have hcollapse := (collapse_fiber n (char1 n r cellA u)).mpr hx
        change projection n cellA.1 cellA.2.1
          (chainBary cellA.1 r cellA.2.2.1 u) = (level n).point at hcollapse
        exact positive_not_point n cellA.1 cellA.2.1 hA
          (chainBary cellA.1 r cellA.2.2.1 u)
          (flagBary_positive cellA.1 r cellA.2.2 u hu) hcollapse
      · intro hA
        exact char1_mem_zero_of_zero n r cellA hA u

    let zeroCell2 {n r : ℕ} (C : Cell2 n r) : Prop :=
      ∀ i, zeroCell1 (C i)
    have zeroCell2_iff_forall {n r : ℕ} (C : Cell2 n r) :
        zeroCell2 C ↔ ∀ i, zeroCell1 (C i) := Iff.rfl
    have zeroCell2_iff_last {n r : ℕ} (C : Cell2 n r) :
        zeroCell2 C ↔ zeroCell1 (C (Fin.last r)) := by
      constructor
      · intro hC
        exact hC (Fin.last r)
      · intro hlast i
        exact zeroCell1_of_le (C i) (C (Fin.last r))
          (C.monotone (Fin.le_last i)) hlast
    have zeroCell2_face2 {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1))
        (C : Cell2 n r) (hC : zeroCell2 C) : zeroCell2 (face2 b C) := by
      intro i
      exact hC (b i)
    have char2_mem_zero_of_zero (n r : ℕ) (C : Cell2 n r)
        (hC : zeroCell2 C) (u : Simplex r) :
        char2 n r C u ∈ Set.range (zeroIncl n) := by
      change char1 n (C (Fin.last r)).1 (C (Fin.last r)).2
        (chainBary _ r (flag2 C).1 u) ∈ Set.range (zeroIncl n)
      exact char1_mem_zero_of_zero n (C (Fin.last r)).1 (C (Fin.last r)).2
        ((zeroCell2_iff_last C).mp hC) (chainBary _ r (flag2 C).1 u)
    have char2_positive_mem_zero_iff (n r : ℕ) (C : Cell2 n r)
        (u : Simplex r) (hu : ∀ i, 0 < u.1 i) :
        char2 n r C u ∈ Set.range (zeroIncl n) ↔ zeroCell2 C := by
      change char1 n (C (Fin.last r)).1 (C (Fin.last r)).2
        (chainBary _ r (flag2 C).1 u) ∈ Set.range (zeroIncl n) ↔ zeroCell2 C
      exact (char1_positive_mem_zero_iff n (C (Fin.last r)).1 (C (Fin.last r)).2
        (chainBary _ r (flag2 C).1 u)
        (flagBary_positive (C (Fin.last r)).1 r (flag2 C) u hu)).trans
          (zeroCell2_iff_last C).symm

    -- Positive zero-cell representatives cover the actual zero subspace.
    have zero_char1_positive_rep (n : ℕ) (x : fatLevel n)
        (hx : x ∈ Set.range (zeroIncl n)) :
        ∃ r, ∃ cellA : Cell1 n r, ∃ u : Simplex r,
          zeroCell1 (⟨r, cellA⟩ : AllCell1 n) ∧
            (∀ i, 0 < u.1 i) ∧ char1 n r cellA u = x := by
      obtain ⟨r, cellA, u, hu, he⟩ := char1_positive_rep n x
      refine ⟨r, cellA, u, ?_, hu, he⟩
      apply (char1_positive_mem_zero_iff n r cellA u hu).mp
      rw [he]
      exact hx
    have zero_char2_positive_rep (n : ℕ) (x : fatLevel n)
        (hx : x ∈ Set.range (zeroIncl n)) :
        ∃ r, ∃ C : Cell2 n r, ∃ u : Simplex r,
          zeroCell2 C ∧ (∀ i, 0 < u.1 i) ∧ char2 n r C u = x := by
      obtain ⟨r, C, u, hu, he⟩ := char2_positive_rep n x
      refine ⟨r, C, u, ?_, hu, he⟩
      apply (char2_positive_mem_zero_iff n r C u hu).mp
      rw [he]
      exact hx

    -- T1: zero second-subdivision cells are closed under taking faces.
    have zeroCell2_of_le {n : ℕ} (cellA cellB : AllCell2 n)
        (hAB : cellA ≤ cellB) (hB : zeroCell2 cellB.2) : zeroCell2 cellA.2 := by
      obtain ⟨b, hb⟩ := (show faceLE2 n cellA cellB from hAB)
      have hface := zeroCell2_face2 b cellB.2 hB
      simpa only [hb] using hface
    -- The third-subdivision zero subcomplex contains exactly the chains
    -- whose vertices are zero second-subdivision cells.
    let zeroCell3 {n r : ℕ} (C : Cell3 n r) : Prop :=
      ∀ i, zeroCell2 (C i).2
    have zeroCell3_iff_forall {n r : ℕ} (C : Cell3 n r) :
        zeroCell3 C ↔ ∀ i, zeroCell2 (C i).2 := Iff.rfl
    have zeroCell3_iff_last {n r : ℕ} (C : Cell3 n r) :
        zeroCell3 C ↔ zeroCell2 (C (Fin.last r)).2 := by
      constructor
      · intro hC
        exact hC (Fin.last r)
      · intro hlast i
        exact zeroCell2_of_le (C i) (C (Fin.last r))
          (C.monotone (Fin.le_last i)) hlast
    have zeroCell3_face3 {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1))
        (C : Cell3 n r) (hC : zeroCell3 C) : zeroCell3 (face3 b C) := by
      intro i
      exact hC (b i)
    have char3_mem_zero_of_zero (n r : ℕ) (C : Cell3 n r)
        (hC : zeroCell3 C) (u : Simplex r) :
        char3 n r C u ∈ Set.range (zeroIncl n) := by
      change char2 n (C (Fin.last r)).1 (C (Fin.last r)).2
        (chainBary _ r (flag3 C).1 u) ∈ Set.range (zeroIncl n)
      exact char2_mem_zero_of_zero n (C (Fin.last r)).1 (C (Fin.last r)).2
        ((zeroCell3_iff_last C).mp hC) (chainBary _ r (flag3 C).1 u)
    have char3_positive_mem_zero_iff (n r : ℕ) (C : Cell3 n r)
        (u : Simplex r) (hu : ∀ i, 0 < u.1 i) :
        char3 n r C u ∈ Set.range (zeroIncl n) ↔ zeroCell3 C := by
      change char2 n (C (Fin.last r)).1 (C (Fin.last r)).2
        (chainBary _ r (flag3 C).1 u) ∈ Set.range (zeroIncl n) ↔ zeroCell3 C
      exact (char2_positive_mem_zero_iff n (C (Fin.last r)).1 (C (Fin.last r)).2
        (chainBary _ r (flag3 C).1 u)
        (flagBary_positive (C (Fin.last r)).1 r (flag3 C) u hu)).trans
          (zeroCell3_iff_last C).symm
    have zero_char3_positive_rep (n : ℕ) (x : fatLevel n)
        (hx : x ∈ Set.range (zeroIncl n)) :
        ∃ r, ∃ C : Cell3 n r, ∃ u : Simplex r,
          zeroCell3 C ∧ (∀ i, 0 < u.1 i) ∧ char3 n r C u = x := by
      obtain ⟨r, C, u, hu, he⟩ := char3_positive_rep n x
      refine ⟨r, C, u, ?_, hu, he⟩
      apply (char3_positive_mem_zero_iff n r C u hu).mp
      rw [he]
      exact hx

    -- T7: each original closed simplex is a finite union of third-subdivision cells.
    let AllCell3 (n : ℕ) := Σ r, Cell3 n r
    have finite_chain_refinement (X : Type) (q : ℕ) (f : Simplex q → X)
        (Cells : ℕ → Type) (ch : ∀ r, Cells r → Simplex r → X)
        (cell : ∀ r (C : Fin (r + 1) → Face q),
          (∀ i j, i < j → (C i).1 ⊂ (C j).1) → Cells r)
        (hcell : ∀ r C hC u, ch r (cell r C hC) u = f (chainBary q r C u)) :
        ∃ F : Finset (Σ r, Cells r), Set.range f ⊆ ⋃ a ∈ F, Set.range (ch a.1 a.2) := by
      let g (c : ChainChoice q) : Σ r, Cells r := ⟨c.1.1, cell c.1.1 c.2.1 c.2.2⟩
      refine ⟨Finset.univ.image g, ?_⟩
      rintro x ⟨u, rfl⟩
      obtain ⟨r, C, v, hC, hv, he, _⟩ := simplex_threshold_chain q u
      let c : ChainChoice q := ⟨⟨r, Nat.lt_succ_of_le (chain_length_le q r C hC)⟩, ⟨C, hC⟩⟩
      apply Set.mem_iUnion_of_mem (g c)
      apply Set.mem_iUnion_of_mem (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
      refine ⟨v, ?_⟩
      change ch r (cell r C hC) v = f u
      rw [hcell r C hC v]
      exact congrArg f (Subtype.ext (funext he))
    have finite_cover_comp (X A B : Type) (S : Set X) (P : A → Set X) (Q : B → Set X)
        (hS : ∃ F : Finset A, S ⊆ ⋃ a ∈ F, P a)
        (hP : ∀ a, ∃ F : Finset B, P a ⊆ ⋃ b ∈ F, Q b) :
        ∃ F : Finset B, S ⊆ ⋃ b ∈ F, Q b := by
      obtain ⟨F, hF⟩ := hS
      choose G hG using hP
      refine ⟨F.biUnion G, ?_⟩
      intro x hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hF hx)
      obtain ⟨ha, hxa⟩ := Set.mem_iUnion.mp ha
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hG a hxa)
      obtain ⟨hbG, hxb⟩ := Set.mem_iUnion.mp hb
      exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr
        ⟨Finset.mem_biUnion.mpr ⟨a, ha, hbG⟩, hxb⟩⟩
    have char2_finite_third (n q : ℕ) (C : Cell2 n q) :
        ∃ F : Finset (AllCell3 n), Set.range (char2 n q C) ⊆
          ⋃ a ∈ F, Set.range (char3 n a.1 a.2) :=
      finite_chain_refinement (fatLevel n) q (char2 n q C) (Cell3 n) (char3 n)
        (fun _ D hD => chainCell3 C D hD) (fun _ D hD u => chainCell3_char C D hD u)
    have char1_finite_third (n q : ℕ) (cellA : Cell1 n q) :
        ∃ F : Finset (AllCell3 n), Set.range (char1 n q cellA) ⊆
          ⋃ a ∈ F, Set.range (char3 n a.1 a.2) := by
      apply finite_cover_comp (fatLevel n) (AllCell2 n) (AllCell3 n)
        (Set.range (char1 n q cellA))
        (fun a => Set.range (char2 n a.1 a.2)) (fun a => Set.range (char3 n a.1 a.2))
      · exact finite_chain_refinement (fatLevel n) q (char1 n q cellA) (Cell2 n) (char2 n)
          (fun _ C hC => chainCell2 cellA C hC) (fun _ C hC u => chainCell2_char cellA C hC u)
      · intro a
        exact char2_finite_third n a.1 a.2
    have fatProjection_finite_third (n q : ℕ) (z : K n q) :
        ∃ F : Finset (AllCell3 n), Set.range (fatProjection n q z) ⊆
          ⋃ a ∈ F, Set.range (char3 n a.1 a.2) := by
      apply finite_cover_comp (fatLevel n) (AllCell1 n) (AllCell3 n)
        (Set.range (fatProjection n q z))
        (fun a => Set.range (char1 n a.1 a.2)) (fun a => Set.range (char3 n a.1 a.2))
      · exact finite_chain_refinement (fatLevel n) q (fatProjection n q z) (Cell1 n) (char1 n)
          (fun r C hC => chainCell1 n q r z C hC) (fun r C hC u => chainCell1_char n q r z C hC u)
      · intro a
        exact char1_finite_third n a.1 a.2
    -- An open original label inside a closed original simplex is an actual face label.
    have fat_positive_label_face (n p q : ℕ) (z : K n p) (w : K n q)
        (u : Simplex p) (hu : ∀ i, 0 < u.1 i)
        (hx : fatProjection n p z u ∈ Set.range (fatProjection n q w)) :
        ∃ a : Fin (p + 1) ↪o Fin (q + 1), pull a.toOrderHom w = z := by
      obtain ⟨t, ht⟩ := hx
      obtain ⟨r, a, v, hv, hmap⟩ := simplex_support q t
      have hface : fatProjection n r (pull a.toOrderHom w) v =
          fatProjection n p z u := by
        rw [fatProjection_face a.toOrderHom a.injective w v, hmap]
        exact ht
      have hlabel := fat_label_unique n r p (pull a.toOrderHom w) z v u hv hu hface
      have hrp : r = p := congrArg Sigma.fst hlabel
      subst r
      refine ⟨a, ?_⟩
      exact eq_of_heq (Sigma.mk.inj_iff.mp hlabel).2
    have fat_positive_label_dim_le (n p q : ℕ) (z : K n p) (w : K n q)
        (u : Simplex p) (hu : ∀ i, 0 < u.1 i)
        (hx : fatProjection n p z u ∈ Set.range (fatProjection n q w)) : p ≤ q := by
      obtain ⟨a, _⟩ := fat_positive_label_face n p q z w u hu hx
      have hcard := Fintype.card_le_of_injective a a.injective
      simp only [Fintype.card_fin] at hcard
      omega
    -- The existing finiteness of K n p makes a dimension bound sufficient.
    have fat_labels_bounded_finite (n q : ℕ) :
        {a : Σ p : ℕ, K n p | a.1 ≤ q}.Finite := by
      letI (p : ℕ) : Finite (K n p) := labels_finite n p
      let B := Σ p : Fin (q + 1), K n p.1
      letI : Finite B := by
        dsimp only [B]
        infer_instance
      have hf := Set.finite_range (fun a : B => (⟨a.1.1, a.2⟩ : Σ p : ℕ, K n p))
      apply hf.subset
      rintro ⟨p, z⟩ hp
      change p ≤ q at hp
      exact ⟨⟨⟨p, Nat.lt_succ_of_le hp⟩, z⟩, rfl⟩

    -- T7: compact subsets meet finitely many original open labels, hence lie
    -- in finitely many of the corresponding actual fatProjection ranges.
    have fat_compact_finite_labels (n : ℕ) (C : Set (fatLevel n)) (hC : IsCompact C) :
        ∃ F : Finset (Σ q : ℕ, K n q),
          C ⊆ ⋃ a ∈ F, Set.range (fatProjection n a.1 a.2) := by
      classical
      letI : T2Space (fatLevel n) := fat_t2 n
      let Labels := Σ q : ℕ, K n q
      let J : Set Labels := {a |
        (C ∩ fatProjection n a.1 a.2 '' {u : Simplex a.1 | ∀ i, 0 < u.1 i}).Nonempty}
      choose p hp using (fun a : J => a.2)
      have hlabel (a : J) (b : Labels)
          (h : p a ∈ fatProjection n b.1 b.2 '' {u : Simplex b.1 | ∀ i, 0 < u.1 i}) :
          a.1 = b := by
        obtain ⟨u, hu, heu⟩ := (hp a).2
        obtain ⟨v, hv, hev⟩ := h
        exact fat_label_unique n a.1.1 b.1 a.1.2 b.2 u v hu hv (heu.trans hev.symm)
      have hinj : Function.Injective p := by
        intro a b he
        apply Subtype.ext
        apply hlabel a b.1
        rw [he]
        exact (hp b).2
      have hclosed (T : Set (fatLevel n)) (hT : T ⊆ Set.range p) : IsClosed T := by
        apply isQuotientMap_quot_mk.isCoinducing.isClosed_preimage.mp
        apply isClosed_sigma_iff.mpr
        intro q
        apply isClosed_sigma_iff.mpr
        intro z
        change IsClosed ((fatProjection n q z) ⁻¹' T)
        have hb : {a : J | a.1.1 ≤ q}.Finite := by
          exact Set.Finite.preimage (f := fun a : J => a.1)
            Subtype.val_injective.injOn (fat_labels_bounded_finite n q)
        have hfinite : (T ∩ Set.range (fatProjection n q z)).Finite := by
          apply (hb.image p).subset
          rintro x hx
          obtain ⟨a, rfl⟩ := hT hx.1
          refine ⟨a, ?_, rfl⟩
          obtain ⟨u, hu, he⟩ := (hp a).2
          have huclosed : fatProjection n a.1.1 a.1.2 u ∈
              Set.range (fatProjection n q z) := by
            rw [he]
            exact hx.2
          exact fat_positive_label_dim_le n a.1.1 q a.1.2 z u hu huclosed
        have hh := hfinite.isClosed.preimage (fatProjection_continuous n q z)
        simpa only [Set.preimage_inter, Set.preimage_range, Set.inter_univ] using hh
      have hcompact : IsCompact (Set.range p) :=
        hC.of_isClosed_subset (hclosed _ Set.Subset.rfl) (by
          rintro _ ⟨a, rfl⟩
          exact (hp a).1)
      have hdiscrete : IsDiscrete (Set.range p) :=
        isDiscrete_iff_forall_mem_exists_isClosed.mpr (by
          intro T hT
          exact ⟨T, hclosed T hT, Set.inter_eq_left.mpr hT⟩)
      have hfinite : Finite J := (Set.finite_range_iff hinj).mp (hcompact.finite hdiscrete)
      have hJ : J.Finite := Set.finite_coe_iff.mp hfinite
      refine ⟨hJ.toFinset, ?_⟩
      intro x hx
      obtain ⟨q, z, u, hu, he⟩ := fat_positive_rep n x
      refine Set.mem_iUnion.mpr ⟨⟨q, z⟩, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · apply hJ.mem_toFinset.mpr
        exact ⟨x, hx, ⟨u, hu, he⟩⟩
      · exact ⟨u, he⟩

    have chainWeight_positive_iff {V : Type} (r : ℕ) (C : Fin (r + 1) → V)
        (hC : Function.Injective C) (u : Simplex r) (hu : ∀ i, 0 < u.1 i) (x : V) :
        0 < chainWeight r C u x ↔ x ∈ Set.range C := by
      constructor
      · intro hx
        by_contra hn
        rw [chainWeight_outside r C u x hn] at hx
        exact (lt_irrefl (0 : ℝ)) hx
      · rintro ⟨i, rfl⟩
        rw [chainWeight_image r C hC u i]
        exact hu i
    have chainWeight_positive_unique (V : Type) [PartialOrder V] (r s : ℕ)
        (C : Fin (r + 1) ↪o V) (D : Fin (s + 1) ↪o V)
        (u : Simplex r) (v : Simplex s) (hu : ∀ i, 0 < u.1 i) (hv : ∀ i, 0 < v.1 i)
        (he : chainWeight r C u = chainWeight s D v) :
        (⟨r, (C, u)⟩ : Σ k, (Fin (k + 1) ↪o V) × Simplex k) = ⟨s, (D, v)⟩ := by
      have hRange : Set.range C = Set.range D := by
        ext x
        calc
          x ∈ Set.range C ↔ 0 < chainWeight r C u x :=
            (chainWeight_positive_iff r C C.injective u hu x).symm
          _ ↔ 0 < chainWeight s D v x := by rw [he]
          _ ↔ x ∈ Set.range D := chainWeight_positive_iff s D D.injective v hv x
      have himage : Finset.univ.image C = Finset.univ.image D := by
        ext x
        simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using
          Set.ext_iff.mp hRange x
      have hrs : r = s := by
        have hcard := congrArg Finset.card himage
        rw [Finset.card_image_of_injective _ C.injective,
          Finset.card_image_of_injective _ D.injective] at hcard
        simp only [Finset.card_univ, Fintype.card_fin] at hcard
        omega
      subst s
      have hCD : C = D := by
        apply DFunLike.ext
        intro i
        exact congrFun ((C.strictMono.range_inj D.strictMono).mp hRange) i
      subst D
      have huv : u = v := by
        apply Subtype.ext
        funext i
        calc
          u.1 i = chainWeight r C u (C i) :=
            (chainWeight_image r C C.injective u i).symm
          _ = chainWeight r C v (C i) := congrFun he (C i)
          _ = v.1 i := chainWeight_image r C C.injective v i
      subst v
      rfl
    -- A chain-weight model with the weak (chart-final) topology.
    let OrderedRealization (V : Type) [PartialOrder V] :=
      {w : V → ℝ // ∃ r : ℕ, ∃ C : Fin (r + 1) ↪o V, ∃ u : Simplex r,
        w = chainWeight r C u}
    let OrderedRaw (V : Type) [PartialOrder V] :=
      Σ r : ℕ, Σ C : Fin (r + 1) ↪o V, Simplex r
    letI (V : Type) [PartialOrder V] : TopologicalSpace (OrderedRaw V) := by
      dsimp only [OrderedRaw]
      infer_instance
    let orderedChart {V : Type} [PartialOrder V] (r : ℕ)
        (C : Fin (r + 1) ↪o V) (u : Simplex r) : OrderedRealization V :=
      ⟨chainWeight r C u, ⟨r, C, u, rfl⟩⟩
    let orderedProjection (V : Type) [PartialOrder V] : OrderedRaw V → OrderedRealization V :=
      fun a => orderedChart a.1 a.2.1 a.2.2
    -- This instance is essential: continuity below uses the final topology of all charts.
    letI (V : Type) [PartialOrder V] : TopologicalSpace (OrderedRealization V) :=
      TopologicalSpace.coinduced (orderedProjection V) inferInstance
    have orderedProjection_quotient (V : Type) [PartialOrder V] :
        IsQuotientMap (orderedProjection V) := by
      refine ⟨⟨rfl⟩, ?_⟩
      intro w
      obtain ⟨r, C, u, hw⟩ := w.2
      refine ⟨⟨r, C, u⟩, ?_⟩
      exact Subtype.ext hw.symm
    have orderedChart_continuous {V : Type} [PartialOrder V] (r : ℕ)
        (C : Fin (r + 1) ↪o V) : Continuous (orderedChart r C) :=
      (orderedProjection_quotient V).continuous.comp
        (continuous_sigmaMk.comp continuous_sigmaMk)
    have orderedChart_face {V : Type} [PartialOrder V] {r s : ℕ}
        (b : Fin (s + 1) ↪o Fin (r + 1)) (C : Fin (r + 1) ↪o V) (u : Simplex s) :
        orderedChart s (b.comp C) u = orderedChart r C (simplexMap b.toOrderHom u) := by
      apply Subtype.ext
      funext v
      exact chainWeight_face b C u v
    have orderedRealization_final (V Z : Type) [PartialOrder V] [TopologicalSpace Z]
        (f : OrderedRealization V → Z)
        (hf : ∀ r C, Continuous (f ∘ orderedChart r C)) : Continuous f := by
      apply (orderedProjection_quotient V).continuous_iff.mpr
      exact continuous_sigma (fun r => continuous_sigma (fun C => hf r C))
    have orderedCoordinate_continuous (V : Type) [PartialOrder V] (v : V) :
        Continuous (fun w : OrderedRealization V => w.1 v) := by
      apply orderedRealization_final V ℝ
      intro r C
      exact chainWeight_continuous r C v
    have orderedChart_injective {V : Type} [PartialOrder V] (r : ℕ)
        (C : Fin (r + 1) ↪o V) : Function.Injective (orderedChart r C) := by
      intro u v he
      apply Subtype.ext
      funext i
      have h := congrArg (fun w : OrderedRealization V => w.1 (C i)) he
      change chainWeight r C u (C i) = chainWeight r C v (C i) at h
      rw [chainWeight_image r C C.injective u i, chainWeight_image r C C.injective v i] at h
      exact h
    have orderedRealization_t2 (V : Type) [PartialOrder V] : T2Space (OrderedRealization V) := by
      apply T2Space.of_injective_continuous
        (f := fun w : OrderedRealization V => w.1) Subtype.val_injective
      apply continuous_pi
      intro v
      exact orderedCoordinate_continuous V v
    letI (V : Type) [PartialOrder V] : T2Space (OrderedRealization V) := orderedRealization_t2 V
    have orderedRealization_homeomorph (V X : Type) [PartialOrder V] [TopologicalSpace X]
        (ch : ∀ r, (Fin (r + 1) ↪o V) → Simplex r → X)
        (hcont : ∀ r C, Continuous (ch r C))
        (hface : ∀ {r s} (b : Fin (s + 1) ↪o Fin (r + 1))
          (C : Fin (r + 1) ↪o V) (u : Simplex s),
          ch s (b.comp C) u = ch r C (simplexMap b.toOrderHom u))
        (hrep : ∀ x : X, ∃ r, ∃ C : Fin (r + 1) ↪o V, ∃ u : Simplex r,
          (∀ i, 0 < u.1 i) ∧ ch r C u = x)
        (hunique : ∀ r s (C : Fin (r + 1) ↪o V) (D : Fin (s + 1) ↪o V)
          (u : Simplex r) (v : Simplex s), (∀ i, 0 < u.1 i) → (∀ i, 0 < v.1 i) →
          ch r C u = ch s D v →
          (⟨r, (C, u)⟩ : Σ k, (Fin (k + 1) ↪o V) × Simplex k) = ⟨s, (D, v)⟩)
        (hfinal : ∀ (Z : Type) [TopologicalSpace Z] (f : X → Z),
          (∀ r C, Continuous (f ∘ ch r C)) → Continuous f) :
        ∃ e : OrderedRealization V ≃ₜ X,
          ∀ r C u, e (orderedChart r C u) = ch r C u := by
      obtain ⟨coord, hcoord, _⟩ := chain_coordinate_data V X ch hface hrep hunique
        (fun f hf => hfinal ℝ f hf)
      let F (x : X) : OrderedRealization V :=
        ⟨coord x, by
          obtain ⟨r, C, u, hu, hx⟩ := hrep x
          refine ⟨r, C, u, ?_⟩
          rw [← hx]
          funext v
          exact hcoord r C u v⟩
      have hFchart (r : ℕ) (C : Fin (r + 1) ↪o V) (u : Simplex r) :
          F (ch r C u) = orderedChart r C u := by
        apply Subtype.ext
        funext v
        exact hcoord r C u v
      have hFinj : Function.Injective F := by
        intro x y hxy
        obtain ⟨r, C, u, hu, hx⟩ := hrep x
        obtain ⟨s, D, v, hv, hy⟩ := hrep y
        have hcharts : orderedChart r C u = orderedChart s D v := by
          rw [← hFchart r C u, ← hFchart s D v, hx, hy]
          exact hxy
        have hparams := chainWeight_positive_unique V r s C D u v hu hv
          (congrArg Subtype.val hcharts)
        have hvalues := congrArg
          (fun a : Σ k, (Fin (k + 1) ↪o V) × Simplex k => ch a.1 a.2.1 a.2.2) hparams
        exact hx.symm.trans (hvalues.trans hy)
      have hFsurj : Function.Surjective F := by
        intro w
        obtain ⟨r, C, u, hw⟩ := w.2
        exact ⟨ch r C u, (hFchart r C u).trans (Subtype.ext hw.symm)⟩
      have hFcont : Continuous F := by
        apply hfinal (OrderedRealization V) F
        intro r C
        exact (orderedChart_continuous r C).congr (fun u => (hFchart r C u).symm)
      let e : X ≃ OrderedRealization V := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
      have hinv_chart (r : ℕ) (C : Fin (r + 1) ↪o V) (u : Simplex r) :
          e.symm (orderedChart r C u) = ch r C u := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact (hFchart r C u).symm
      have hinv_cont : Continuous e.symm := by
        apply orderedRealization_final V X e.symm
        intro r C
        exact (hcont r C).congr (fun u => (hinv_chart r C u).symm)
      let H : OrderedRealization V ≃ₜ X :=
        { toEquiv := e.symm
          continuous_toFun := hinv_cont
          continuous_invFun := hFcont }
      exact ⟨H, hinv_chart⟩
    -- T1: the third abstract order complex has exactly the given fat topology.
    have third_homeomorph_data (n : ℕ) :
        ∃ e : OrderedRealization (AllCell2 n) ≃ₜ fatLevel n,
          ∀ r (C : Cell3 n r) u, e (orderedChart r C u) = char3 n r C u :=
      orderedRealization_homeomorph (AllCell2 n) (fatLevel n) (char3 n)
        (char3_continuous n) (fun b C u => char3_face b C u)
        (char3_positive_rep n) (char3_positive_unique n) (char3_final n)
    have fat_compact_finite_third (n : ℕ) (C : Set (fatLevel n)) (hC : IsCompact C) :
        ∃ F : Finset (AllCell3 n), C ⊆ ⋃ a ∈ F, Set.range (char3 n a.1 a.2) := by
      apply finite_cover_comp (fatLevel n) (Σ q, K n q) (AllCell3 n) C
        (fun a => Set.range (fatProjection n a.1 a.2))
        (fun a => Set.range (char3 n a.1 a.2)) (fat_compact_finite_labels n C hC)
      intro a
      exact fatProjection_finite_third n a.1 a.2
    have fat_compact_finite_vertices (n : ℕ) (S : Set (fatLevel n)) (hS : IsCompact S) :
        ∃ V : Finset (AllCell2 n), ∀ x ∈ S,
          ∃ r, ∃ C : Cell3 n r, ∃ u : Simplex r,
            (∀ i, C i ∈ V) ∧ (∀ i, 0 < u.1 i) ∧ char3 n r C u = x := by
      obtain ⟨F, hF⟩ := fat_compact_finite_third n S hS
      let V : Finset (AllCell2 n) := F.biUnion (fun a => Finset.univ.image a.2)
      refine ⟨V, ?_⟩
      intro x hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hF hx)
      obtain ⟨ha, u, hu⟩ := Set.mem_iUnion.mp ha
      obtain ⟨s, b, v, hv, hmap⟩ := simplex_support a.1 u
      refine ⟨s, face3 b a.2, v, ?_, hv, ?_⟩
      · intro i
        exact Finset.mem_biUnion.mpr ⟨a, ha,
          Finset.mem_image.mpr ⟨b i, Finset.mem_univ _, rfl⟩⟩
      · rw [char3_face b a.2 v, hmap]
        exact hu
    have ordered_positive_rep (V : Type) [PartialOrder V] (w : OrderedRealization V) :
        ∃ r, ∃ C : Fin (r + 1) ↪o V, ∃ u : Simplex r,
          (∀ i, 0 < u.1 i) ∧ orderedChart r C u = w := by
      obtain ⟨r, C, u, hw⟩ := w.2
      obtain ⟨s, b, v, hv, he⟩ := simplex_support r u
      refine ⟨s, b.comp C, v, hv, ?_⟩
      rw [orderedChart_face b C v, he]
      exact Subtype.ext hw.symm
    choose thirdHomeomorph thirdHomeomorph_chart using third_homeomorph_data
    have thirdHomeomorph_zero_iff (n : ℕ) (w : OrderedRealization (AllCell2 n)) :
        thirdHomeomorph n w ∈ Set.range (zeroIncl n) ↔
          ∀ v : AllCell2 n, 0 < w.1 v → zeroCell2 v.2 := by
      obtain ⟨r, C, u, hu, hw⟩ := ordered_positive_rep (AllCell2 n) w
      rw [← hw, thirdHomeomorph_chart n r C u, char3_positive_mem_zero_iff n r C u hu]
      constructor
      · intro hC v hv
        change 0 < chainWeight r C u v at hv
        obtain ⟨i, rfl⟩ := (chainWeight_positive_iff r C C.injective u hu v).mp hv
        exact hC i
      · intro h i
        apply h (C i)
        change 0 < chainWeight r C u (C i)
        rw [chainWeight_image r C C.injective u i]
        exact hu i
    have ordered_nonneg (V : Type) [PartialOrder V] (w : OrderedRealization V) (v : V) :
        0 ≤ w.1 v := by
      obtain ⟨r, C, u, hw⟩ := w.2
      rw [hw]
      exact chainWeight_nonneg r C u v
    have ordered_positive_support (V : Type) [PartialOrder V] (w : OrderedRealization V) :
        ∃ S : Finset V,
          (∀ v, v ∈ S ↔ 0 < w.1 v) ∧
          (∑ v ∈ S, w.1 v) = 1 ∧
          (∀ v ∈ S, ∀ z ∈ S, v ≤ z ∨ z ≤ v) := by
      obtain ⟨r, C, u, hu, hw⟩ := ordered_positive_rep V w
      refine ⟨Finset.univ.image C, ?_, ?_, ?_⟩
      · intro v
        rw [← hw]
        change v ∈ Finset.univ.image C ↔ 0 < chainWeight r C u v
        rw [chainWeight_positive_iff r C C.injective u hu v]
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
      · rw [← hw, Finset.sum_image (fun i _ j _ he => C.injective he)]
        change (∑ i, chainWeight r C u (C i)) = 1
        simp_rw [chainWeight_image r C C.injective u]
        exact u.2.2
      · intro v hv z hz
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
        rcases le_total i j with hij | hji
        · exact Or.inl (C.monotone hij)
        · exact Or.inr (C.monotone hji)
    have ordered_support_finite (V : Type) [PartialOrder V] (w : OrderedRealization V) :
        {v | 0 < w.1 v}.Finite := by
      obtain ⟨S, hS, _⟩ := ordered_positive_support V w
      have he : {v | 0 < w.1 v} = (S : Set V) := by
        ext v
        exact (hS v).symm
      rw [he]
      exact S.finite_toSet
    have ordered_has_positive (V : Type) [PartialOrder V] (w : OrderedRealization V) :
        ∃ v, 0 < w.1 v := by
      obtain ⟨r, C, u, hu, hw⟩ := ordered_positive_rep V w
      refine ⟨C 0, ?_⟩
      rw [← hw]
      change 0 < chainWeight r C u (C 0)
      rw [chainWeight_image r C C.injective u 0]
      exact hu 0
    have ordered_star_open (V : Type) [PartialOrder V] (v : V) :
        IsOpen {w : OrderedRealization V | 0 < w.1 v} :=
      isOpen_lt continuous_const (orderedCoordinate_continuous V v)
    have orderedRealization_compact (V : Type) [PartialOrder V] [Finite V] :
        CompactSpace (OrderedRealization V) := by
      classical
      letI : Fintype V := Fintype.ofFinite V
      letI (r : ℕ) : CompactSpace (Simplex r) := simplex_compact r
      have hbound (r : ℕ) (C : Fin (r + 1) ↪o V) : r < Fintype.card V := by
        have hcard := Fintype.card_le_of_injective C C.injective
        simp only [Fintype.card_fin] at hcard
        omega
      let Cells : Type := Σ r : Fin (Fintype.card V), Fin (r.1 + 1) ↪o V
      letI : Fintype Cells := by
        dsimp only [Cells]
        infer_instance
      have hc : IsCompact (⋃ c : Cells, Set.range (orderedChart c.1.1 c.2)) :=
        isCompact_iUnion (fun c => isCompact_range (orderedChart_continuous c.1.1 c.2))
      have he : (⋃ c : Cells, Set.range (orderedChart c.1.1 c.2)) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro w
        obtain ⟨r, C, u, hw⟩ := w.2
        exact Set.mem_iUnion.mpr ⟨⟨⟨r, hbound r C⟩, C⟩, u, Subtype.ext hw.symm⟩
      exact ⟨he ▸ hc⟩
    -- Finite induced subcomplexes carry the same chart-final topology.
    letI (V : Type) [PartialOrder V] [Finite V] : CompactSpace (OrderedRealization V) :=
      orderedRealization_compact V

    -- Extension by zero along an order embedding preserves chain weights.
    have chainWeight_extend {V W : Type} [PartialOrder V] [PartialOrder W]
        (e : V ↪o W) (r : ℕ) (C : Fin (r + 1) ↪o V) (u : Simplex r) :
        Function.extend e (chainWeight r C u) (fun _ => (0 : ℝ)) =
          chainWeight r (C.comp e) u := by
      funext w
      by_cases hw : w ∈ Set.range e
      · obtain ⟨v, rfl⟩ := hw
        rw [e.injective.extend_apply (chainWeight r C u) (fun _ => (0 : ℝ)) v]
        change (∑ i, if C i = v then u.1 i else 0) =
          ∑ i, if e (C i) = e v then u.1 i else 0
        simp only [e.injective.eq_iff]
      · rw [Function.extend_apply' (chainWeight r C u) (fun _ => (0 : ℝ)) w hw]
        exact (chainWeight_outside r (C.comp e) u w (by
          rintro ⟨i, hi⟩
          exact hw ⟨C i, hi⟩)).symm
    let orderedMap {V W : Type} [PartialOrder V] [PartialOrder W]
        (e : V ↪o W) (w : OrderedRealization V) : OrderedRealization W :=
      ⟨Function.extend e w.1 (fun _ => (0 : ℝ)), by
        obtain ⟨r, C, u, hw⟩ := w.2
        refine ⟨r, C.comp e, u, ?_⟩
        rw [hw]
        exact chainWeight_extend e r C u⟩
    have orderedMap_chart {V W : Type} [PartialOrder V] [PartialOrder W]
        (e : V ↪o W) (r : ℕ) (C : Fin (r + 1) ↪o V) (u : Simplex r) :
        orderedMap e (orderedChart r C u) = orderedChart r (C.comp e) u := by
      exact Subtype.ext (chainWeight_extend e r C u)
    have orderedMap_apply_image {V W : Type} [PartialOrder V] [PartialOrder W]
        (e : V ↪o W) (w : OrderedRealization V) (v : V) :
        (orderedMap e w).1 (e v) = w.1 v :=
      e.injective.extend_apply w.1 (fun _ => (0 : ℝ)) v
    have orderedMap_apply_outside {V W : Type} [PartialOrder V] [PartialOrder W]
        (e : V ↪o W) (w : OrderedRealization V) (x : W) (hx : x ∉ Set.range e) :
        (orderedMap e w).1 x = 0 :=
      Function.extend_apply' w.1 (fun _ => (0 : ℝ)) x hx
    have orderedMap_continuous {V W : Type} [PartialOrder V] [PartialOrder W]
        (e : V ↪o W) : Continuous (orderedMap e) := by
      apply orderedRealization_final V (OrderedRealization W) (orderedMap e)
      intro r C
      exact (orderedChart_continuous r (C.comp e)).congr
        (fun u => (orderedMap_chart e r C u).symm)
    have orderedMap_injective {V W : Type} [PartialOrder V] [PartialOrder W]
        (e : V ↪o W) : Function.Injective (orderedMap e) := by
      intro w w' he
      apply Subtype.ext
      funext v
      have h := congrArg (fun z : OrderedRealization W => z.1 (e v)) he
      rw [orderedMap_apply_image e w v, orderedMap_apply_image e w' v] at h
      exact h
    have orderedMap_isClosedEmbedding {V W : Type} [PartialOrder V] [PartialOrder W]
        [Finite V] (e : V ↪o W) : IsClosedEmbedding (orderedMap e) := by
      letI : CompactSpace (OrderedRealization V) := orderedRealization_compact V
      letI : T2Space (OrderedRealization W) := orderedRealization_t2 W
      exact (orderedMap_continuous e).isClosedEmbedding (orderedMap_injective e)

    have orderedMap_range_iff {V W : Type} [PartialOrder V] [PartialOrder W]
        (e : V ↪o W) (w : OrderedRealization W) :
        w ∈ Set.range (orderedMap e) ↔ ∀ v, 0 < w.1 v → v ∈ Set.range e := by
      constructor
      · rintro ⟨u, rfl⟩ v hv
        by_contra hn
        rw [orderedMap_apply_outside e u v hn] at hv
        exact (lt_irrefl (0 : ℝ)) hv
      · intro hw
        obtain ⟨r, C, u, hu, he⟩ := ordered_positive_rep W w
        have hpre (i : Fin (r + 1)) : ∃ v : V, e v = C i := by
          apply hw (C i)
          rw [← he]
          change 0 < chainWeight r C u (C i)
          rw [chainWeight_image r C C.injective u i]
          exact hu i
        choose f hf using hpre
        let D : Fin (r + 1) ↪o V := OrderEmbedding.ofStrictMono f (by
          intro i j hij
          apply e.lt_iff_lt.mp
          rw [hf i, hf j]
          exact C.strictMono hij)
        have hD : D.comp e = C := by
          apply DFunLike.ext
          intro i
          exact hf i
        refine ⟨orderedChart r D u, ?_⟩
        rw [orderedMap_chart e r D u, hD, he]
    let finiteThirdMap (n : ℕ) (V : Finset (AllCell2 n)) :
        OrderedRealization {v : AllCell2 n // v ∈ V} → fatLevel n :=
      (thirdHomeomorph n) ∘ orderedMap (OrderEmbedding.subtype (fun v : AllCell2 n => v ∈ V))
    have finiteThirdMap_isClosedEmbedding (n : ℕ) (V : Finset (AllCell2 n)) :
        IsClosedEmbedding (finiteThirdMap n V) :=
      (thirdHomeomorph n).isClosedEmbedding.comp
        (orderedMap_isClosedEmbedding (OrderEmbedding.subtype (fun v : AllCell2 n => v ∈ V)))
    have fat_compact_finite_subcomplex (n : ℕ) (S : Set (fatLevel n)) (hS : IsCompact S) :
        ∃ V : Finset (AllCell2 n), S ⊆ Set.range (finiteThirdMap n V) := by
      obtain ⟨V, hV⟩ := fat_compact_finite_vertices n S hS
      refine ⟨V, ?_⟩
      intro x hx
      obtain ⟨r, C, u, hC, hu, he⟩ := hV x hx
      let D : Fin (r + 1) ↪o {v : AllCell2 n // v ∈ V} :=
        OrderEmbedding.ofStrictMono (fun i => ⟨C i, hC i⟩) (fun _ _ hij => C.strictMono hij)
      let e := OrderEmbedding.subtype (fun v : AllCell2 n => v ∈ V)
      have hD : D.comp e = C := by
        apply DFunLike.ext
        intro i
        rfl
      refine ⟨orderedChart r D u, ?_⟩
      change thirdHomeomorph n (orderedMap e (orderedChart r D u)) = x
      rw [orderedMap_chart e r D u, hD, thirdHomeomorph_chart n r C u]
      exact he
    have compact_map_finite_factor (n : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X]
        (f : C(X, fatLevel n)) :
        ∃ V : Finset (AllCell2 n), ∃ g : C(X, OrderedRealization {v : AllCell2 n // v ∈ V}),
          ∀ x, finiteThirdMap n V (g x) = f x := by
      obtain ⟨V, hV⟩ := fat_compact_finite_subcomplex n (Set.range f) (isCompact_range f.continuous)
      have hpre (x : X) : ∃ y, finiteThirdMap n V y = f x := hV ⟨x, rfl⟩
      choose g hg using hpre
      have hcont : Continuous g := by
        apply (finiteThirdMap_isClosedEmbedding n V).isEmbedding.isInducing.continuous_iff.mpr
        exact f.continuous.congr (fun x => (hg x).symm)
      exact ⟨V, ⟨g, hcont⟩, hg⟩
    -- T9: the last-vertex label of the first subdivision respects actual faces.
    let lastFace {q : ℕ} (S : Face q) : Fin (q + 1) := S.1.max' S.2
    have lastFace_mono {q : ℕ} (S T : Face q) (hST : S.1 ⊆ T.1) :
        lastFace S ≤ lastFace T := Finset.max'_subset S.2 hST
    have lastFace_natural {p q : ℕ} (a : Fin (p + 1) ↪o Fin (q + 1)) (S : Face p) :
        a (lastFace S) = lastFace (faceImage a S) := by
      apply le_antisymm
      · exact Finset.le_max' _ _ (Finset.mem_map.mpr ⟨lastFace S, Finset.max'_mem S.1 S.2, rfl⟩)
      · apply Finset.max'_le
        intro j hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
        exact a.monotone (Finset.le_max' S.1 i hi)
    let lastFlag {q r : ℕ} (C : Flag q r) : Fin (r + 1) →o Fin (q + 1) :=
      ⟨fun i => lastFace (C.1 i), fun i j hij =>
        lastFace_mono (C.1 i) (C.1 j) (chain_mono q r C.1 C.2.1 i j hij)⟩
    have lastFlag_restrict {q r s : ℕ} (C : Flag q r) (b : Fin (s + 1) ↪o Fin (r + 1)) :
        (faceEnum (C.1 (b (Fin.last s)))).toOrderHom.comp (lastFlag (restrictFlag C b)) =
          (lastFlag C).comp b.toOrderHom := by
      apply DFunLike.ext
      intro i
      exact (lastFace_natural (faceEnum (C.1 (b (Fin.last s)))) ((restrictFlag C b).1 i)).trans
        (congrArg lastFace (restrictFlag_map C b i))
    let label1 {n r : ℕ} (cellA : Cell1 n r) : K n r :=
      pull (lastFlag cellA.2.2) cellA.2.1
    have label1_face {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1)) (cellA : Cell1 n r) :
        label1 (face1 b cellA) = pull b.toOrderHom (label1 cellA) := by
      obtain ⟨q, z, C⟩ := cellA
      change pull (lastFlag (restrictFlag C b))
        (pull (faceEnum (C.1 (b (Fin.last s)))).toOrderHom z) =
          pull b.toOrderHom (pull (lastFlag C) z)
      rw [pull_comp, pull_comp, lastFlag_restrict C b]
    have label1_zero {n r : ℕ} (cellA : Cell1 n r)
        (hA : zeroCell1 (⟨r, cellA⟩ : AllCell1 n)) : label1 cellA = zero n r := by
      change cellA.2.1 = zero n cellA.1 at hA
      change pull (lastFlag cellA.2.2) cellA.2.1 = zero n r
      rw [hA, pull_zero]
    -- T8: a finite barycentric subdivision reduces the mesh by d/(d+1).
    have finite_mean_nested_dist {ι E : Type}
        [SeminormedAddCommGroup E] [NormedSpace ℝ E]
        (S T : Finset ι) (f : ι → E)
        (hS : S.Nonempty) (hST : S ⊆ T) (D : ℝ)
        (hD : ∀ i ∈ T, ∀ j ∈ T, dist (f i) (f j) ≤ D) :
        dist (S.centerMass (fun _ => (1 : ℝ)) f)
          (T.centerMass (fun _ => (1 : ℝ)) f) ≤
          (1 - (S.card : ℝ) / (T.card : ℝ)) * D := by
      classical
      let avg (U : Finset ι) : E := U.centerMass (fun _ => (1 : ℝ)) f
      change dist (avg S) (avg T) ≤ _
      have hT : T.Nonempty := hS.mono hST
      have hSpos : 0 < (S.card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr hS)
      have hTpos : 0 < (T.card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr hT)
      have hS0 : (S.card : ℝ) ≠ 0 := ne_of_gt hSpos
      have hT0 : (T.card : ℝ) ≠ 0 := ne_of_gt hTpos
      have hinv : 0 ≤ (T.card : ℝ)⁻¹ := inv_nonneg.mpr hTpos.le
      have havg (U : Finset ι) :
          avg U = (U.card : ℝ)⁻¹ • ∑ i ∈ U, f i := by
        simp [avg, Finset.centerMass]
      have hmem : avg S ∈ convexHull ℝ (f '' (T : Set ι)) := by
        change S.centerMass (fun _ => (1 : ℝ)) f ∈ _
        refine S.centerMass_mem_convexHull (fun _ _ => zero_le_one) ?_ ?_
        · simpa using hSpos
        · intro i hi
          exact ⟨i, hST hi, rfl⟩
      have hpoint (i : ι) (hi : i ∈ T) : ‖f i - avg S‖ ≤ D := by
        obtain ⟨x, ⟨j, hj, rfl⟩, hx⟩ := convexHull_exists_dist_ge hmem (f i)
        simpa only [dist_eq_norm'] using hx.trans (hD j hj i hi)
      have hsumS : (∑ i ∈ S, (f i - avg S)) = 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_const,
          ← Nat.cast_smul_eq_nsmul ℝ, havg S, smul_smul,
          mul_inv_cancel₀ hS0, one_smul, sub_self]
      have hres : (∑ i ∈ T \ S, (f i - avg S)) =
          (∑ i ∈ T, f i) - (T.card : ℝ) • avg S := by
        calc
          (∑ i ∈ T \ S, (f i - avg S)) =
              ∑ i ∈ T, (f i - avg S) := by
            have h := Finset.sum_sdiff (f := fun i => f i - avg S) hST
            simpa only [hsumS, add_zero] using h
          _ = (∑ i ∈ T, f i) - (T.card : ℝ) • avg S := by
            rw [Finset.sum_sub_distrib, Finset.sum_const,
              ← Nat.cast_smul_eq_nsmul ℝ]
      have hid : avg T - avg S =
          (T.card : ℝ)⁻¹ • ∑ i ∈ T \ S, (f i - avg S) := by
        rw [hres, smul_sub, smul_smul, inv_mul_cancel₀ hT0, one_smul, havg T]
      have hcadd : ((T \ S).card : ℝ) + (S.card : ℝ) = (T.card : ℝ) := by
        exact_mod_cast (Finset.card_sdiff_add_card_eq_card hST)
      have hcsub : ((T \ S).card : ℝ) = (T.card : ℝ) - (S.card : ℝ) := by
        linarith
      have hcoeff : (T.card : ℝ)⁻¹ * ((T \ S).card : ℝ) =
          1 - (S.card : ℝ) / (T.card : ℝ) := by
        rw [hcsub, mul_sub, inv_mul_cancel₀ hT0, div_eq_mul_inv]
        ring
      calc
        dist (avg S) (avg T) = ‖avg T - avg S‖ := dist_eq_norm' _ _
        _ = (T.card : ℝ)⁻¹ * ‖∑ i ∈ T \ S, (f i - avg S)‖ := by
          rw [hid, norm_smul_of_nonneg hinv]
        _ ≤ (T.card : ℝ)⁻¹ * ∑ i ∈ T \ S, ‖f i - avg S‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hinv
        _ ≤ (T.card : ℝ)⁻¹ * ∑ _i ∈ T \ S, D := by
          apply mul_le_mul_of_nonneg_left _ hinv
          exact Finset.sum_le_sum (fun i hi => hpoint i (Finset.mem_sdiff.mp hi).1)
        _ = (1 - (S.card : ℝ) / (T.card : ℝ)) * D := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hcoeff]

    have finite_mean_nested_dist_dim {ι E : Type}
        [SeminormedAddCommGroup E] [NormedSpace ℝ E]
        (S T : Finset ι) (f : ι → E)
        (hS : S.Nonempty) (hST : S ⊆ T)
        (d : ℕ) (hcard : T.card ≤ d + 1) (D : ℝ)
        (hD : ∀ i ∈ T, ∀ j ∈ T, dist (f i) (f j) ≤ D) :
        dist (S.centerMass (fun _ => (1 : ℝ)) f)
          (T.centerMass (fun _ => (1 : ℝ)) f) ≤
          ((d : ℝ) / ((d : ℝ) + 1)) * D := by
      have hT : T.Nonempty := hS.mono hST
      have hTpos : 0 < (T.card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr hT)
      have hSone : (1 : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast (Finset.one_le_card.mpr hS)
      have hdim : (T.card : ℝ) ≤ (d : ℝ) + 1 := by
        exact_mod_cast hcard
      have hdpos : 0 < (d : ℝ) + 1 := by positivity
      have hD0 : 0 ≤ D := by
        obtain ⟨i, hi⟩ := hS
        simpa only [dist_self] using hD i (hST hi) i (hST hi)
      have hratio : 1 / ((d : ℝ) + 1) ≤ (S.card : ℝ) / (T.card : ℝ) :=
        (one_div_le_one_div_of_le hTpos hdim).trans
          (div_le_div_of_nonneg_right hSone hTpos.le)
      have hcoeff : 1 - (S.card : ℝ) / (T.card : ℝ) ≤
          (d : ℝ) / ((d : ℝ) + 1) := by
        calc
          1 - (S.card : ℝ) / (T.card : ℝ) ≤
              1 - 1 / ((d : ℝ) + 1) := sub_le_sub_left hratio 1
          _ = (d : ℝ) / ((d : ℝ) + 1) := by
            field_simp [ne_of_gt hdpos] <;> ring
      exact (finite_mean_nested_dist S T f hS hST D hD).trans
        (mul_le_mul_of_nonneg_right hcoeff hD0)
    have barycenter_eq_centerMass (q : ℕ) (S : Face q) :
        (barycenter q S).1 =
          S.1.centerMass (fun _ => (1 : ℝ)) (fun i => (vertex q i).1) := by
      funext j
      change (if j ∈ S.1 then (S.1.card : ℝ)⁻¹ else 0) =
        (((∑ i ∈ S.1, (1 : ℝ))⁻¹) •
          ∑ i ∈ S.1, (1 : ℝ) • (vertex q i).1) j
      simp [vertex, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite]

    let last2Upper {n r : ℕ} (C : Cell2 n r) (cellB : AllCell1 n)
        (hCB : C (Fin.last r) ≤ cellB) : Fin (r + 1) →o Fin (cellB.1 + 1) :=
      ⟨fun i => lastFace (cell1Face (C i) cellB ((C.monotone (Fin.le_last i)).trans hCB)), by
        intro i j hij
        apply lastFace_mono
        exact cell1Face_subset (C i) (C j) cellB
          ((C.monotone (Fin.le_last i)).trans hCB)
          ((C.monotone (Fin.le_last j)).trans hCB) (C.monotone hij)⟩
    have last2Upper_natural {n r : ℕ} (C : Cell2 n r) (cellB : AllCell1 n)
        (hCB : C (Fin.last r) ≤ cellB) :
        (occ1 (C (Fin.last r)) cellB hCB).toOrderHom.comp (lastFlag (flag2 C)) =
          last2Upper C cellB hCB := by
      apply DFunLike.ext
      intro i
      exact (lastFace_natural (occ1 (C (Fin.last r)) cellB hCB) ((flag2 C).1 i)).trans
        (congrArg lastFace (cell1Face_natural (C i) (C (Fin.last r)) cellB
          (C.monotone (Fin.le_last i)) hCB))
    let label2 {n r : ℕ} (C : Cell2 n r) : K n r :=
      pull (lastFlag (flag2 C)) (label1 (C (Fin.last r)).2)
    have label2_in_upper {n r : ℕ} (C : Cell2 n r) (cellB : AllCell1 n)
        (hCB : C (Fin.last r) ≤ cellB) :
        label2 C = pull (last2Upper C cellB hCB) (label1 cellB.2) := by
      have hlabel := label1_face (occ1 (C (Fin.last r)) cellB hCB) cellB.2
      rw [face1_occ1 (C (Fin.last r)) cellB hCB] at hlabel
      change pull (lastFlag (flag2 C)) (label1 (C (Fin.last r)).2) = _
      rw [hlabel, pull_comp, last2Upper_natural C cellB hCB]
    have label2_face {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1)) (C : Cell2 n r) :
        label2 (face2 b C) = pull b.toOrderHom (label2 C) := by
      calc
        label2 (face2 b C) =
            pull (last2Upper (face2 b C) (C (Fin.last r)) (C.monotone (Fin.le_last _)))
              (label1 (C (Fin.last r)).2) :=
          label2_in_upper (face2 b C) (C (Fin.last r)) (C.monotone (Fin.le_last _))
        _ = pull ((lastFlag (flag2 C)).comp b.toOrderHom) (label1 (C (Fin.last r)).2) := by
          apply congrArg (fun a : Fin (s + 1) →o Fin ((C (Fin.last r)).1 + 1) =>
            pull a (label1 (C (Fin.last r)).2))
          apply DFunLike.ext
          intro i
          rfl
        _ = pull b.toOrderHom (label2 C) :=
          (pull_comp b.toOrderHom (lastFlag (flag2 C)) (label1 (C (Fin.last r)).2)).symm
    have label2_zero {n r : ℕ} (C : Cell2 n r) (hC : zeroCell2 C) : label2 C = zero n r := by
      change pull (lastFlag (flag2 C)) (label1 (C (Fin.last r)).2) = zero n r
      rw [label1_zero (C (Fin.last r)).2 (hC (Fin.last r)), pull_zero]
    let last3Upper {n r : ℕ} (C : Cell3 n r) (cellB : AllCell2 n)
        (hCB : C (Fin.last r) ≤ cellB) : Fin (r + 1) →o Fin (cellB.1 + 1) :=
      ⟨fun i => lastFace (cell2Face (C i) cellB ((C.monotone (Fin.le_last i)).trans hCB)), by
        intro i j hij
        apply lastFace_mono
        exact cell2Face_subset (C i) (C j) cellB
          ((C.monotone (Fin.le_last i)).trans hCB)
          ((C.monotone (Fin.le_last j)).trans hCB) (C.monotone hij)⟩
    have last3Upper_natural {n r : ℕ} (C : Cell3 n r) (cellB : AllCell2 n)
        (hCB : C (Fin.last r) ≤ cellB) :
        (occ2 (C (Fin.last r)) cellB hCB).toOrderHom.comp (lastFlag (flag3 C)) =
          last3Upper C cellB hCB := by
      apply DFunLike.ext
      intro i
      exact (lastFace_natural (occ2 (C (Fin.last r)) cellB hCB) ((flag3 C).1 i)).trans
        (congrArg lastFace (cell2Face_natural (C i) (C (Fin.last r)) cellB
          (C.monotone (Fin.le_last i)) hCB))
    let label3 {n r : ℕ} (C : Cell3 n r) : K n r :=
      pull (lastFlag (flag3 C)) (label2 (C (Fin.last r)).2)
    have label3_in_upper {n r : ℕ} (C : Cell3 n r) (cellB : AllCell2 n)
        (hCB : C (Fin.last r) ≤ cellB) :
        label3 C = pull (last3Upper C cellB hCB) (label2 cellB.2) := by
      have hlabel := label2_face (occ2 (C (Fin.last r)) cellB hCB) cellB.2
      rw [face2_occ2 (C (Fin.last r)) cellB hCB] at hlabel
      change pull (lastFlag (flag3 C)) (label2 (C (Fin.last r)).2) = _
      rw [hlabel, pull_comp, last3Upper_natural C cellB hCB]
    have label3_face {n r s : ℕ} (b : Fin (s + 1) ↪o Fin (r + 1)) (C : Cell3 n r) :
        label3 (face3 b C) = pull b.toOrderHom (label3 C) := by
      calc
        label3 (face3 b C) =
            pull (last3Upper (face3 b C) (C (Fin.last r)) (C.monotone (Fin.le_last _)))
              (label2 (C (Fin.last r)).2) :=
          label3_in_upper (face3 b C) (C (Fin.last r)) (C.monotone (Fin.le_last _))
        _ = pull ((lastFlag (flag3 C)).comp b.toOrderHom) (label2 (C (Fin.last r)).2) := by
          apply congrArg (fun a : Fin (s + 1) →o Fin ((C (Fin.last r)).1 + 1) =>
            pull a (label2 (C (Fin.last r)).2))
          apply DFunLike.ext
          intro i
          rfl
        _ = pull b.toOrderHom (label3 C) :=
          (pull_comp b.toOrderHom (lastFlag (flag3 C)) (label2 (C (Fin.last r)).2)).symm
    have label3_zero {n r : ℕ} (C : Cell3 n r) (hC : zeroCell3 C) : label3 C = zero n r := by
      change pull (lastFlag (flag3 C)) (label2 (C (Fin.last r)).2) = zero n r
      rw [label2_zero (C (Fin.last r)).2 (hC (Fin.last r)), pull_zero]
    -- B1: evaluating the last-vertex labels gives the universal relative cocycle.
    let universalCochain (n : ℕ) (C : Cell3 n n) : ZMod 2 := (label3 C).1 OrderHom.id
    have universalCochain_closed (n : ℕ) (C : Cell3 n (n + 1)) :
        (∑ i : Fin (n + 2), universalCochain n (face3 i.succAboveOrderEmb C)) = 0 := by
      have he (i : Fin (n + 2)) :
          universalCochain n (face3 i.succAboveOrderEmb C) = (label3 C).1 (face n i) := by
        change (label3 (face3 i.succAboveOrderEmb C)).1 OrderHom.id = _
        rw [label3_face]
        rfl
      simp_rw [he]
      exact (label3 C).2.2 OrderHom.id
    have universalCochain_zero (n : ℕ) (C : Cell3 n n) (hC : zeroCell3 C) :
        universalCochain n C = 0 := by
      change (label3 C).1 OrderHom.id = 0
      rw [label3_zero C hC]
    have finiteThirdMap_zero_iff (n : ℕ) (V : Finset (AllCell2 n))
        (w : OrderedRealization {v : AllCell2 n // v ∈ V}) :
        finiteThirdMap n V w ∈ Set.range (zeroIncl n) ↔
          ∀ v : {v : AllCell2 n // v ∈ V}, 0 < w.1 v → zeroCell2 v.1.2 := by
      let e := OrderEmbedding.subtype (fun v : AllCell2 n => v ∈ V)
      change thirdHomeomorph n (orderedMap e w) ∈ Set.range (zeroIncl n) ↔ _
      rw [thirdHomeomorph_zero_iff]
      constructor
      · intro h v hv
        apply h (e v)
        rw [orderedMap_apply_image e w v]
        exact hv
      · intro h v hv
        have hrange := (orderedMap_range_iff e (orderedMap e w)).mp ⟨w, rfl⟩ v hv
        obtain ⟨a, rfl⟩ := hrange
        rw [orderedMap_apply_image e w a] at hv
        exact h a hv
    have orderedCoordinate_embedding (V : Type) [PartialOrder V] [Finite V] :
        IsEmbedding (fun w : OrderedRealization V => w.1) := by
      have hc : Continuous (fun w : OrderedRealization V => w.1) :=
        continuous_pi (fun v => orderedCoordinate_continuous V v)
      exact (hc.isClosedEmbedding Subtype.val_injective).isEmbedding
    letI (V : Type) [PartialOrder V] [Fintype V] : MetricSpace (OrderedRealization V) :=
      Topology.IsEmbedding.comapMetricSpace (fun w : OrderedRealization V => w.1)
        (orderedCoordinate_embedding V)
    have ordered_dist_eq (V : Type) [PartialOrder V] [Fintype V]
        (w z : OrderedRealization V) : dist w z = dist w.1 z.1 := rfl
    have finite_chain_mesh {E : Type} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
        (q r : ℕ) (f : Fin (q + 1) → E) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) (D : ℝ)
        (hD : ∀ i j, dist (f i) (f j) ≤ D) (u v : Simplex r) :
        dist (∑ i, u.1 i • (C i).1.centerMass (fun _ => (1 : ℝ)) f)
          (∑ i, v.1 i • (C i).1.centerMass (fun _ => (1 : ℝ)) f) ≤
          ((q : ℝ) / ((q : ℝ) + 1)) * D := by
      let g (i : Fin (r + 1)) : E := (C i).1.centerMass (fun _ => (1 : ℝ)) f
      have hvertices (i j : Fin (r + 1)) : dist (g i) (g j) ≤
          ((q : ℝ) / ((q : ℝ) + 1)) * D := by
        rcases le_total i j with hij | hji
        · exact finite_mean_nested_dist_dim (C i).1 (C j).1 f (C i).2
            (chain_mono q r C hC i j hij) q
            (by simpa only [Fintype.card_fin] using (Finset.card_le_univ (C j).1)) D
            (fun a _ b _ => hD a b)
        · rw [dist_comm]
          exact finite_mean_nested_dist_dim (C j).1 (C i).1 f (C j).2
            (chain_mono q r C hC j i hji) q
            (by simpa only [Fintype.card_fin] using (Finset.card_le_univ (C i).1)) D
            (fun a _ b _ => hD a b)
      have hconv (w : Simplex r) : (∑ i, w.1 i • g i) ∈ convexHull ℝ (Set.range g) :=
        (convex_convexHull ℝ (Set.range g)).sum_mem (fun i _ => w.2.1 i) w.2.2
          (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)
      obtain ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, hxy⟩ := convexHull_exists_dist_ge2 (hconv u) (hconv v)
      exact hxy.trans (hvertices i j)
    have mesh_power_small (d : ℕ) (hd : 0 < d) (D δ : ℝ) (hδ : 0 < δ) :
        ∃ k : ℕ, 2 * D * ((d : ℝ) / ((d : ℝ) + 1)) ^ k < δ := by
      have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
      have hd1pos : 0 < (d : ℝ) + 1 := by positivity
      let a : ℝ := 1 / (d : ℝ)
      let ρ : ℝ := (d : ℝ) / ((d : ℝ) + 1)
      have ha : 0 < a := one_div_pos.mpr hdpos
      have hρ : 0 < ρ := div_pos hdpos hd1pos
      obtain ⟨k, hk⟩ := exists_nat_gt ((2 * D / δ) / a)
      have hka : 2 * D / δ < (k : ℝ) * a := (div_lt_iff₀ ha).mp hk
      have hbase : 2 * D < δ * (1 + (k : ℝ) * a) := by
        have hh := (div_lt_iff₀ hδ).mp hka
        nlinarith
      have hidentity : ρ * (1 + a) = 1 := by
        dsimp only [ρ, a]
        field_simp [ne_of_gt hdpos, ne_of_gt hd1pos]
      have hproduct : ρ ^ k * (1 + a) ^ k = 1 := by
        rw [← mul_pow, hidentity, one_pow]
      have hbound : ρ ^ k * (1 + (k : ℝ) * a) ≤ 1 := by
        have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ a by linarith) k
        have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg hρ.le k)
        rwa [hproduct] at hm
      refine ⟨k, ?_⟩
      change 2 * D * ρ ^ k < δ
      calc
        2 * D * ρ ^ k < (δ * (1 + (k : ℝ) * a)) * ρ ^ k :=
          mul_lt_mul_of_pos_right hbase (pow_pos hρ k)
        _ = δ * (ρ ^ k * (1 + (k : ℝ) * a)) := by ring
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hbound hδ.le
        _ = δ := mul_one δ
    let OrderedFace (V : Type) [PartialOrder V] :=
      {S : Finset V // S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, x ≤ y ∨ y ≤ x}
    letI (V : Type) [PartialOrder V] : PartialOrder (OrderedFace V) := by
      dsimp only [OrderedFace]
      infer_instance
    have orderedFace_le_iff {V : Type} [PartialOrder V] (S T : OrderedFace V) :
        S ≤ T ↔ S.1 ⊆ T.1 := Iff.rfl
    have orderedFace_isChain {V : Type} [PartialOrder V] (S : OrderedFace V) :
        IsChain (· ≤ ·) (S.1 : Set V) := by
      intro x hx y hy _
      exact S.2.2 x hx y hy
    have orderedFace_card_pos {V : Type} [PartialOrder V] (S : OrderedFace V) :
        0 < S.1.card := Finset.card_pos.mpr S.2.1
    let orderedFaceDim {V : Type} [PartialOrder V] (S : OrderedFace V) : ℕ :=
      S.1.card - 1
    have orderedFace_card {V : Type} [PartialOrder V] (S : OrderedFace V) :
        S.1.card = orderedFaceDim S + 1 := by
      have hpos := orderedFace_card_pos S
      dsimp only [orderedFaceDim]
      omega
    have orderedFace_card_mono {V : Type} [PartialOrder V] (S T : OrderedFace V)
        (hST : S ≤ T) : S.1.card ≤ T.1.card := Finset.card_le_card hST
    have orderedFace_card_lt {V : Type} [PartialOrder V] (S T : OrderedFace V)
        (hST : S < T) : S.1.card < T.1.card := by
      apply Finset.card_lt_card
      exact ⟨le_of_lt hST, fun hTS => (not_le_of_gt hST) hTS⟩

    -- First construct an increasing enumeration. Its uniqueness below makes the choice canonical.
    have orderedFace_enumeration {V : Type} [PartialOrder V] (S : OrderedFace V) :
        ∃ e : Fin S.1.card ↪o V, Set.range e = (S.1 : Set V) := by
      classical
      letI : LinearOrder ↥S.1 := (orderedFace_isChain S).linearOrder
      let e : Fin S.1.card ≃o ↥S.1 :=
        Fintype.orderIsoFinOfCardEq ↥S.1 (Fintype.card_coe S.1)
      refine ⟨e.toOrderEmbedding.comp (OrderEmbedding.subtype (fun x : V => x ∈ S.1)), ?_⟩
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).2
      · intro hx
        refine ⟨e.symm ⟨x, hx⟩, ?_⟩
        exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    let faceVertices {V : Type} [PartialOrder V] (S : OrderedFace V) : Fin S.1.card ↪o V :=
      Classical.choose (orderedFace_enumeration S)
    have faceVertices_range {V : Type} [PartialOrder V] (S : OrderedFace V) :
        Set.range (faceVertices S) = (S.1 : Set V) :=
      Classical.choose_spec (orderedFace_enumeration S)
    have faceVertices_mem {V : Type} [PartialOrder V] (S : OrderedFace V)
        (i : Fin S.1.card) : faceVertices S i ∈ S.1 := by
      have h : faceVertices S i ∈ Set.range (faceVertices S) := ⟨i, rfl⟩
      rw [faceVertices_range S] at h
      exact h
    have faceVertices_image {V : Type} [PartialOrder V] (S : OrderedFace V) :
        Finset.univ.image (faceVertices S) = S.1 := by
      classical
      ext x
      simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range,
        Finset.mem_coe] using Set.ext_iff.mp (faceVertices_range S) x
    have faceVertices_unique {V : Type} [PartialOrder V] (S : OrderedFace V)
        (e : Fin S.1.card ↪o V) (he : Set.range e = (S.1 : Set V)) :
        e = faceVertices S :=
      OrderEmbedding.range_eq_iff.mp (he.trans (faceVertices_range S).symm)

    -- A face inclusion has a unique increasing map between the canonical enumerations.
    have faceFactor_exists {V : Type} [PartialOrder V] (S T : OrderedFace V)
        (hST : S ≤ T) :
        ∃ a : Fin S.1.card ↪o Fin T.1.card,
          a.comp (faceVertices T) = faceVertices S := by
      have hex (i : Fin S.1.card) : ∃ j, faceVertices T j = faceVertices S i := by
        change faceVertices S i ∈ Set.range (faceVertices T)
        rw [faceVertices_range T]
        exact hST (faceVertices_mem S i)
      let f (i : Fin S.1.card) : Fin T.1.card := Classical.choose (hex i)
      have hf (i : Fin S.1.card) : faceVertices T (f i) = faceVertices S i :=
        Classical.choose_spec (hex i)
      let a : Fin S.1.card ↪o Fin T.1.card := OrderEmbedding.ofMapLEIff f (by
        intro i j
        calc
          f i ≤ f j ↔ faceVertices T (f i) ≤ faceVertices T (f j) :=
            (faceVertices T).le_iff_le.symm
          _ ↔ faceVertices S i ≤ faceVertices S j := by rw [hf i, hf j]
          _ ↔ i ≤ j := (faceVertices S).le_iff_le)
      refine ⟨a, ?_⟩
      apply DFunLike.ext
      intro i
      exact hf i
    let faceFactor {V : Type} [PartialOrder V] (S T : OrderedFace V) (hST : S ≤ T) :
        Fin S.1.card ↪o Fin T.1.card := Classical.choose (faceFactor_exists S T hST)
    have faceFactor_spec {V : Type} [PartialOrder V] (S T : OrderedFace V) (hST : S ≤ T) :
        (faceFactor S T hST).comp (faceVertices T) = faceVertices S :=
      Classical.choose_spec (faceFactor_exists S T hST)
    have faceFactor_apply {V : Type} [PartialOrder V] (S T : OrderedFace V)
        (hST : S ≤ T) (i : Fin S.1.card) :
        faceVertices T (faceFactor S T hST i) = faceVertices S i :=
      congrArg (fun a : Fin S.1.card ↪o V => a i) (faceFactor_spec S T hST)
    have faceFactor_unique {V : Type} [PartialOrder V] (S T : OrderedFace V)
        (hST : S ≤ T) (a : Fin S.1.card ↪o Fin T.1.card)
        (ha : a.comp (faceVertices T) = faceVertices S) : a = faceFactor S T hST := by
      apply DFunLike.ext
      intro i
      apply (faceVertices T).injective
      exact (congrArg (fun b : Fin S.1.card ↪o V => b i) ha).trans
        (faceFactor_apply S T hST i).symm
    have faceFactor_self {V : Type} [PartialOrder V] (S : OrderedFace V) :
        faceFactor S S le_rfl = OrderEmbedding.id (Fin S.1.card) :=
      (faceFactor_unique S S le_rfl (OrderEmbedding.id _) (by rfl)).symm
    have faceFactor_comp {V : Type} [PartialOrder V] (S T U : OrderedFace V)
        (hST : S ≤ T) (hTU : T ≤ U) :
        (faceFactor S T hST).comp (faceFactor T U hTU) =
          faceFactor S U (hST.trans hTU) := by
      apply faceFactor_unique S U (hST.trans hTU)
      apply DFunLike.ext
      intro i
      change faceVertices U (faceFactor T U hTU (faceFactor S T hST i)) = faceVertices S i
      rw [faceFactor_apply T U hTU, faceFactor_apply S T hST]
    have faceFactor_range {V : Type} [PartialOrder V] (S T : OrderedFace V) (hST : S ≤ T) :
        Set.range (faceFactor S T hST) = {i | faceVertices T i ∈ S.1} := by
      ext j
      constructor
      · rintro ⟨i, rfl⟩
        change faceVertices T (faceFactor S T hST i) ∈ S.1
        rw [faceFactor_apply S T hST i]
        exact faceVertices_mem S i
      · intro hj
        have hex : faceVertices T j ∈ Set.range (faceVertices S) := by
          rw [faceVertices_range S]
          exact hj
        obtain ⟨i, hi⟩ := hex
        exact ⟨i, (faceVertices T).injective ((faceFactor_apply S T hST i).trans hi)⟩

    -- Convert the simplex index to the cardinality index: dim + 1 -> card.
    -- The given equality orderedFace_card S has the opposite direction.
    let faceIndexN {V : Type} [PartialOrder V] (S : OrderedFace V) :
        Fin (orderedFaceDim S + 1) ≃o Fin S.1.card :=
      Fin.castOrderIso (orderedFace_card S).symm
    let faceVerticesN {V : Type} [PartialOrder V] (S : OrderedFace V) :
        Fin (orderedFaceDim S + 1) ↪o V :=
      (faceIndexN S).toOrderEmbedding.comp (faceVertices S)
    have faceVerticesN_mem {V : Type} [PartialOrder V] (S : OrderedFace V)
        (i : Fin (orderedFaceDim S + 1)) : faceVerticesN S i ∈ S.1 :=
      faceVertices_mem S (faceIndexN S i)
    have faceVerticesN_range {V : Type} [PartialOrder V] (S : OrderedFace V) :
        Set.range (faceVerticesN S) = (S.1 : Set V) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact faceVerticesN_mem S i
      · intro hx
        have hex : x ∈ Set.range (faceVertices S) := by
          rw [faceVertices_range S]
          exact hx
        obtain ⟨i, hi⟩ := hex
        refine ⟨(faceIndexN S).symm i, ?_⟩
        change faceVertices S (faceIndexN S ((faceIndexN S).symm i)) = x
        rw [(faceIndexN S).apply_symm_apply i]
        exact hi

    have faceVerticesN_image {V : Type} [PartialOrder V] (S : OrderedFace V) :
        Finset.univ.image (faceVerticesN S) = S.1 := by
      classical
      ext x
      simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range,
        Finset.mem_coe] using Set.ext_iff.mp (faceVerticesN_range S) x

    -- Conjugate a face inclusion by the two index isomorphisms.
    let faceFactorN {V : Type} [PartialOrder V] (S T : OrderedFace V) (hST : S ≤ T) :
        Fin (orderedFaceDim S + 1) ↪o Fin (orderedFaceDim T + 1) :=
      ((faceIndexN S).toOrderEmbedding.comp (faceFactor S T hST)).comp
        (faceIndexN T).symm.toOrderEmbedding
    have faceFactorN_apply {V : Type} [PartialOrder V] (S T : OrderedFace V)
        (hST : S ≤ T) (i : Fin (orderedFaceDim S + 1)) :
        faceVerticesN T (faceFactorN S T hST i) = faceVerticesN S i := by
      change faceVertices T
          (faceIndexN T ((faceIndexN T).symm (faceFactor S T hST (faceIndexN S i)))) =
        faceVertices S (faceIndexN S i)
      rw [(faceIndexN T).apply_symm_apply (faceFactor S T hST (faceIndexN S i)),
        faceFactor_apply S T hST (faceIndexN S i)]
    have faceFactorN_spec {V : Type} [PartialOrder V] (S T : OrderedFace V)
        (hST : S ≤ T) :
        (faceFactorN S T hST).comp (faceVerticesN T) = faceVerticesN S := by
      apply DFunLike.ext
      intro i
      exact faceFactorN_apply S T hST i
    have faceFactorN_unique {V : Type} [PartialOrder V] (S T : OrderedFace V)
        (hST : S ≤ T) (a : Fin (orderedFaceDim S + 1) ↪o Fin (orderedFaceDim T + 1))
        (ha : a.comp (faceVerticesN T) = faceVerticesN S) :
        a = faceFactorN S T hST := by
      apply DFunLike.ext
      intro i
      apply (faceVerticesN T).injective
      exact (congrArg (fun b : Fin (orderedFaceDim S + 1) ↪o V => b i) ha).trans
        (faceFactorN_apply S T hST i).symm
    have faceFactorN_self {V : Type} [PartialOrder V] (S : OrderedFace V) :
        faceFactorN S S le_rfl = OrderEmbedding.id (Fin (orderedFaceDim S + 1)) :=
      (faceFactorN_unique S S le_rfl (OrderEmbedding.id _) (by rfl)).symm
    have faceFactorN_comp {V : Type} [PartialOrder V] (S T U : OrderedFace V)
        (hST : S ≤ T) (hTU : T ≤ U) :
        (faceFactorN S T hST).comp (faceFactorN T U hTU) =
          faceFactorN S U (hST.trans hTU) := by
      apply faceFactorN_unique S U (hST.trans hTU)
      apply DFunLike.ext
      intro i
      change faceVerticesN U (faceFactorN T U hTU (faceFactorN S T hST i)) =
        faceVerticesN S i
      rw [faceFactorN_apply T U hTU (faceFactorN S T hST i), faceFactorN_apply S T hST i]

    let faceSubset {V : Type} [PartialOrder V] (S T : OrderedFace V) (hST : S ≤ T) :
        Face (orderedFaceDim T) :=
      faceImage (faceFactorN S T hST) (fullFace (orderedFaceDim S))
    have faceSubset_card_dim {V : Type} [PartialOrder V] (S T : OrderedFace V) (hST : S ≤ T) :
        (faceSubset S T hST).1.card = orderedFaceDim S + 1 := by
      simp only [faceSubset, faceImage, fullFace, Finset.card_map, Finset.card_univ,
        Fintype.card_fin]
    have faceSubset_card {V : Type} [PartialOrder V] (S T : OrderedFace V) (hST : S ≤ T) :
        (faceSubset S T hST).1.card = S.1.card :=
      (faceSubset_card_dim S T hST).trans (orderedFace_card S).symm
    have faceSubset_self {V : Type} [PartialOrder V] (S : OrderedFace V) :
        faceSubset S S le_rfl = fullFace (orderedFaceDim S) := by
      apply Subtype.ext
      change Finset.univ.map (faceFactorN S S le_rfl).toEmbedding = Finset.univ
      rw [faceFactorN_self S]
      exact Finset.map_refl
    have faceSubset_natural {V : Type} [PartialOrder V] (S T U : OrderedFace V)
        (hST : S ≤ T) (hTU : T ≤ U) :
        faceImage (faceFactorN T U hTU) (faceSubset S T hST) =
          faceSubset S U (hST.trans hTU) := by
      change faceImage (faceFactorN T U hTU)
        (faceImage (faceFactorN S T hST) (fullFace (orderedFaceDim S))) =
          faceImage (faceFactorN S U (hST.trans hTU)) (fullFace (orderedFaceDim S))
      rw [faceImage_comp (faceFactorN S T hST) (faceFactorN T U hTU)
        (fullFace (orderedFaceDim S)), faceFactorN_comp S T U hST hTU]
    have faceSubset_mem {V : Type} [PartialOrder V] (S T : OrderedFace V)
        (hST : S ≤ T) (j : Fin (orderedFaceDim T + 1)) :
        j ∈ (faceSubset S T hST).1 ↔ faceVerticesN T j ∈ S.1 := by
      change j ∈ Finset.univ.map (faceFactorN S T hST).toEmbedding ↔ _
      constructor
      · intro hj
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
        change faceVerticesN T (faceFactorN S T hST i) ∈ S.1
        rw [faceFactorN_apply S T hST i]
        exact faceVerticesN_mem S i
      · intro hj
        have hex : faceVerticesN T j ∈ Set.range (faceVerticesN S) := by
          rw [faceVerticesN_range S]
          exact hj
        obtain ⟨i, hi⟩ := hex
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i,
          (faceVerticesN T).injective ((faceFactorN_apply S T hST i).trans hi)⟩
    have faceSubset_subset {V : Type} [PartialOrder V] (S U T : OrderedFace V)
        (hST : S ≤ T) (hUT : U ≤ T) (hSU : S ≤ U) :
        (faceSubset S T hST).1 ⊆ (faceSubset U T hUT).1 := by
      intro j hj
      exact (faceSubset_mem U T hUT j).mpr (hSU ((faceSubset_mem S T hST j).mp hj))
    have faceSubset_strict {V : Type} [PartialOrder V] (S U T : OrderedFace V)
        (hST : S ≤ T) (hUT : U ≤ T) (hSU : S < U) :
        (faceSubset S T hST).1 ⊂ (faceSubset U T hUT).1 := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨faceSubset_subset S U T hST hUT hSU.le, ?_⟩
      intro he
      have hcard := congrArg Finset.card he
      rw [faceSubset_card S T hST, faceSubset_card U T hUT] at hcard
      exact (ne_of_lt (orderedFace_card_lt S U hSU)) hcard
    have faceSubset_injective {V : Type} [PartialOrder V] (S U T : OrderedFace V)
        (hST : S ≤ T) (hUT : U ≤ T)
        (he : faceSubset S T hST = faceSubset U T hUT) : S = U := by
      apply Subtype.ext
      ext x
      constructor
      · intro hx
        have hxT : x ∈ Set.range (faceVerticesN T) := by
          rw [faceVerticesN_range T]
          exact hST hx
        obtain ⟨j, rfl⟩ := hxT
        apply (faceSubset_mem U T hUT j).mp
        rw [← he]
        exact (faceSubset_mem S T hST j).mpr hx
      · intro hx
        have hxT : x ∈ Set.range (faceVerticesN T) := by
          rw [faceVerticesN_range T]
          exact hUT hx
        obtain ⟨j, rfl⟩ := hxT
        apply (faceSubset_mem S T hST j).mp
        rw [he]
        exact (faceSubset_mem U T hUT j).mpr hx

    -- The barycentric chart of a chain of nonempty finite ordered faces.
    let sdFlag {V : Type} [PartialOrder V] {r : ℕ}
        (C : Fin (r + 1) ↪o OrderedFace V) : Flag (orderedFaceDim (C (Fin.last r))) r :=
      ⟨fun i => faceSubset (C i) (C (Fin.last r)) (C.monotone (Fin.le_last i)),
        fun i j hij => faceSubset_strict (C i) (C j) (C (Fin.last r))
          (C.monotone (Fin.le_last i)) (C.monotone (Fin.le_last j)) (C.strictMono hij),
        faceSubset_self (C (Fin.last r))⟩
    let sdChart {V : Type} [PartialOrder V] {r : ℕ}
        (C : Fin (r + 1) ↪o OrderedFace V) (u : Simplex r) : OrderedRealization V :=
      orderedChart (orderedFaceDim (C (Fin.last r))) (faceVerticesN (C (Fin.last r)))
        (chainBary _ r (sdFlag C).1 u)
    have sdChart_continuous {V : Type} [PartialOrder V] {r : ℕ}
        (C : Fin (r + 1) ↪o OrderedFace V) : Continuous (sdChart C) :=
      (orderedChart_continuous _ (faceVerticesN (C (Fin.last r)))).comp
        (chainBary_continuous _ r (sdFlag C).1)
    have sdFlag_face {V : Type} [PartialOrder V] {r s : ℕ}
        (b : Fin (s + 1) ↪o Fin (r + 1)) (C : Fin (r + 1) ↪o OrderedFace V)
        (i : Fin (s + 1)) :
        faceImage (faceFactorN (C (b (Fin.last s))) (C (Fin.last r))
          (C.monotone (Fin.le_last _))) ((sdFlag (b.comp C)).1 i) = (sdFlag C).1 (b i) :=
      faceSubset_natural (C (b i)) (C (b (Fin.last s))) (C (Fin.last r))
        (C.monotone (b.monotone (Fin.le_last i))) (C.monotone (Fin.le_last _))
    have sdChart_face {V : Type} [PartialOrder V] {r s : ℕ}
        (b : Fin (s + 1) ↪o Fin (r + 1)) (C : Fin (r + 1) ↪o OrderedFace V)
        (u : Simplex s) : sdChart (b.comp C) u = sdChart C (simplexMap b.toOrderHom u) := by
      let A := C (b (Fin.last s))
      let B := C (Fin.last r)
      have hAB : A ≤ B := C.monotone (Fin.le_last _)
      let a := faceFactorN A B hAB
      have ha : a.comp (faceVerticesN B) = faceVerticesN A := faceFactorN_spec A B hAB
      change orderedChart (orderedFaceDim A) (faceVerticesN A)
        (chainBary (orderedFaceDim A) s (sdFlag (b.comp C)).1 u) =
          orderedChart (orderedFaceDim B) (faceVerticesN B)
            (chainBary (orderedFaceDim B) r (sdFlag C).1 (simplexMap b.toOrderHom u))
      rw [← ha, orderedChart_face a (faceVerticesN B)
        (chainBary (orderedFaceDim A) s (sdFlag (b.comp C)).1 u)]
      apply congrArg (orderedChart (orderedFaceDim B) (faceVerticesN B))
      rw [← chainBary_face a (sdFlag (b.comp C)).1 u, chainBary_chainface b (sdFlag C).1 u]
      congr 1
      funext i
      exact sdFlag_face b C i
    have sdChart_in_upper {V : Type} [PartialOrder V] {r : ℕ}
        (C : Fin (r + 1) ↪o OrderedFace V) (B : OrderedFace V)
        (hCB : C (Fin.last r) ≤ B) (u : Simplex r) :
        sdChart C u = orderedChart (orderedFaceDim B) (faceVerticesN B)
          (chainBary (orderedFaceDim B) r
            (fun i => faceSubset (C i) B ((C.monotone (Fin.le_last i)).trans hCB)) u) := by
      let A := C (Fin.last r)
      let a := faceFactorN A B hCB
      have ha : a.comp (faceVerticesN B) = faceVerticesN A := faceFactorN_spec A B hCB
      change orderedChart (orderedFaceDim A) (faceVerticesN A)
        (chainBary (orderedFaceDim A) r (sdFlag C).1 u) = _
      rw [← ha, orderedChart_face a (faceVerticesN B)
        (chainBary (orderedFaceDim A) r (sdFlag C).1 u)]
      apply congrArg (orderedChart (orderedFaceDim B) (faceVerticesN B))
      rw [← chainBary_face a (sdFlag C).1 u]
      congr 1
      funext i
      exact faceSubset_natural (C i) A B (C.monotone (Fin.le_last i)) hCB

    have ordered_of_face_weights (V : Type) [PartialOrder V] (S : OrderedFace V)
        (w : V → ℝ) (h0 : ∀ v, 0 ≤ w v) (hs : ∑ v ∈ S.1, w v = 1)
        (hout : ∀ v, v ∉ S.1 → w v = 0) :
        ∃ z : OrderedRealization V, z.1 = w := by
      let e := faceVerticesN S
      have hsum : (∑ i, w (e i)) = 1 := by
        calc
          (∑ i, w (e i)) = ∑ v ∈ Finset.univ.image e, w v :=
            (Finset.sum_image (fun i _ j _ he => e.injective he)).symm
          _ = ∑ v ∈ S.1, w v := by rw [faceVerticesN_image S]
          _ = 1 := hs
      let u : Simplex (orderedFaceDim S) := ⟨fun i => w (e i), fun i => h0 (e i), hsum⟩
      refine ⟨orderedChart (orderedFaceDim S) e u, ?_⟩
      funext v
      change chainWeight (orderedFaceDim S) e u v = w v
      by_cases hv : v ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hv
        exact chainWeight_image (orderedFaceDim S) e e.injective u i
      · rw [chainWeight_outside (orderedFaceDim S) e u v hv]
        symm
        apply hout v
        intro hvS
        apply hv
        rw [faceVerticesN_range S]
        exact hvS
    have ordered_zero_of_not_pos (V : Type) [PartialOrder V] (w : OrderedRealization V)
        (v : V) (hv : ¬ 0 < w.1 v) : w.1 v = 0 :=
      le_antisymm (le_of_not_gt hv) (ordered_nonneg V w v)
    have ordered_convex_combo (V : Type) [PartialOrder V] (w z : OrderedRealization V)
        (hcompat : ∀ a b, 0 < w.1 a → 0 < z.1 b → a ≤ b ∨ b ≤ a) (t : I) :
        ∃ y : OrderedRealization V, ∀ v, y.1 v = (1 - (t : ℝ)) * w.1 v + (t : ℝ) * z.1 v := by
      obtain ⟨S, hS, hsumS, hchainS⟩ := ordered_positive_support V w
      obtain ⟨T, hT, hsumT, hchainT⟩ := ordered_positive_support V z
      have hne : (S ∪ T).Nonempty := by
        obtain ⟨a, ha⟩ := ordered_has_positive V w
        exact ⟨a, Finset.mem_union_left T ((hS a).mpr ha)⟩
      let U : OrderedFace V := ⟨S ∪ T, hne, by
        intro a ha b hb
        rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb
        · exact hchainS a ha b hb
        · exact hcompat a b ((hS a).mp ha) ((hT b).mp hb)
        · exact (hcompat b a ((hS b).mp hb) ((hT a).mp ha)).symm
        · exact hchainT a ha b hb⟩
      have hw0 (a : V) (ha : a ∉ S) : w.1 a = 0 :=
        ordered_zero_of_not_pos V w a (fun h => ha ((hS a).mpr h))
      have hz0 (a : V) (ha : a ∉ T) : z.1 a = 0 :=
        ordered_zero_of_not_pos V z a (fun h => ha ((hT a).mpr h))
      have hsumw : (∑ a ∈ U.1, w.1 a) = 1 := by
        calc
          (∑ a ∈ U.1, w.1 a) = ∑ a ∈ S, w.1 a :=
            (Finset.sum_subset Finset.subset_union_left (fun a _ ha => hw0 a ha)).symm
          _ = 1 := hsumS
      have hsumz : (∑ a ∈ U.1, z.1 a) = 1 := by
        calc
          (∑ a ∈ U.1, z.1 a) = ∑ a ∈ T, z.1 a :=
            (Finset.sum_subset Finset.subset_union_right (fun a _ ha => hz0 a ha)).symm
          _ = 1 := hsumT
      obtain ⟨y, hy⟩ := ordered_of_face_weights V U
        (fun a => (1 - (t : ℝ)) * w.1 a + (t : ℝ) * z.1 a)
        (fun a => add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (ordered_nonneg V w a))
          (mul_nonneg t.2.1 (ordered_nonneg V z a)))
        (by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsumw, hsumz]; ring)
        (by
          intro a ha
          have hS' : a ∉ S := fun h => ha (Finset.mem_union_left T h)
          have hT' : a ∉ T := fun h => ha (Finset.mem_union_right S h)
          rw [hw0 a hS', hz0 a hT', mul_zero, mul_zero, add_zero])
      exact ⟨y, fun v => congrFun hy v⟩
    have ordered_convex_preserves_full (V : Type) [PartialOrder V] (P : V → Prop)
        (w z y : OrderedRealization V) (t : I)
        (hy : ∀ v, y.1 v = (1 - (t : ℝ)) * w.1 v + (t : ℝ) * z.1 v)
        (hw : ∀ v, 0 < w.1 v → P v) (hz : ∀ v, 0 < z.1 v → P v) :
        ∀ v, 0 < y.1 v → P v := by
      intro v hv
      by_contra hn
      have hwv := ordered_zero_of_not_pos V w v (fun h => hn (hw v h))
      have hzv := ordered_zero_of_not_pos V z v (fun h => hn (hz v h))
      rw [hy v, hwv, hzv, mul_zero, mul_zero, add_zero] at hv
      exact (lt_irrefl (0 : ℝ)) hv
    have ordered_line_homotopy (V X : Type) [PartialOrder V] [Fintype V]
        [TopologicalSpace X] (f g : C(X, OrderedRealization V))
        (hcompat : ∀ x a b, 0 < (f x).1 a → 0 < (g x).1 b → a ≤ b ∨ b ≤ a) :
        ∃ H : C(I × X, OrderedRealization V),
          (∀ x, H (0, x) = f x) ∧ (∀ x, H (1, x) = g x) ∧
          (∀ t x v, (H (t, x)).1 v = (1 - (t : ℝ)) * (f x).1 v + (t : ℝ) * (g x).1 v) := by
      choose h hh using (fun p : I × X => ordered_convex_combo V (f p.2) (g p.2)
        (hcompat p.2) p.1)
      have hc : Continuous h := by
        apply (orderedCoordinate_embedding V).continuous_iff.mpr
        apply continuous_pi
        intro v
        have he : (fun p : I × X => (h p).1 v) =
            fun p => (1 - (p.1 : ℝ)) * (f p.2).1 v + (p.1 : ℝ) * (g p.2).1 v :=
          funext (fun p => hh p v)
        change Continuous (fun p : I × X => (h p).1 v)
        rw [he]
        exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          ((orderedCoordinate_continuous V v).comp (f.continuous.comp continuous_snd))).add
          ((continuous_subtype_val.comp continuous_fst).mul
            ((orderedCoordinate_continuous V v).comp (g.continuous.comp continuous_snd)))
      refine ⟨⟨h, hc⟩, ?_, ?_, ?_⟩
      · intro x
        apply Subtype.ext
        funext v
        simpa using hh (0, x) v
      · intro x
        apply Subtype.ext
        funext v
        simpa using hh (1, x) v
      · intro t x v
        exact hh (t, x) v
    have ordered_total_weight (V : Type) [PartialOrder V] [Fintype V]
        (w : OrderedRealization V) : ∑ v, w.1 v = 1 := by
      obtain ⟨S, hS, hs, _⟩ := ordered_positive_support V w
      calc
        (∑ v, w.1 v) = ∑ v ∈ S, w.1 v :=
          (Finset.sum_subset (Finset.subset_univ S) (fun v _ hv =>
            ordered_zero_of_not_pos V w v (fun hp => hv ((hS v).mpr hp)))).symm
        _ = 1 := hs
    have ordered_vertex_image (V W : Type) [PartialOrder V] [PartialOrder W] [Fintype V]
        (a : V → W) (ha : ∀ v z, v ≤ z ∨ z ≤ v → a v ≤ a z ∨ a z ≤ a v)
        (w : OrderedRealization V) :
        ∃ z : OrderedRealization W, ∀ b, z.1 b = ∑ v, if a v = b then w.1 v else 0 := by
      obtain ⟨S, hS, hs, hchain⟩ := ordered_positive_support V w
      have hw0 (v : V) (hv : v ∉ S) : w.1 v = 0 :=
        ordered_zero_of_not_pos V w v (fun hp => hv ((hS v).mpr hp))
      have hne : (S.image a).Nonempty := by
        obtain ⟨v, hv⟩ := ordered_has_positive V w
        exact ⟨a v, Finset.mem_image.mpr ⟨v, (hS v).mpr hv, rfl⟩⟩
      let T : OrderedFace W := ⟨S.image a, hne, by
        intro b hb c hc
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
        exact ha v z (hchain v hv z hz)⟩
      have hsum (v : V) : (∑ b ∈ T.1, if a v = b then w.1 v else 0) = w.1 v := by
        by_cases hv : v ∈ S
        · have hav : a v ∈ T.1 := Finset.mem_image.mpr ⟨v, hv, rfl⟩
          simp [hav]
        · simp [hw0 v hv]
      obtain ⟨z, hz⟩ := ordered_of_face_weights W T
        (fun b => ∑ v, if a v = b then w.1 v else 0)
        (fun b => Finset.sum_nonneg (fun v _ => by
          split_ifs <;> first | exact ordered_nonneg V w v | exact le_rfl))
        (by
          rw [Finset.sum_comm]
          simp_rw [hsum]
          exact ordered_total_weight V w)
        (by
          intro b hb
          apply Finset.sum_eq_zero
          intro v _
          by_cases hav : a v = b
          · rw [if_pos hav]
            apply hw0 v
            intro hv
            exact hb (Finset.mem_image.mpr ⟨v, hv, hav⟩)
          · rw [if_neg hav])
      exact ⟨z, fun b => congrFun hz b⟩
    have ordered_vertex_image_positive (V W : Type) [PartialOrder V] [PartialOrder W]
        [Fintype V] (a : V → W) (w : OrderedRealization V) (z : OrderedRealization W)
        (hz : ∀ b, z.1 b = ∑ v, if a v = b then w.1 v else 0) (b : W) :
        0 < z.1 b ↔ ∃ v, 0 < w.1 v ∧ a v = b := by
      rw [hz b, Finset.sum_pos_iff_of_nonneg (fun v _ =>
        show 0 ≤ (if a v = b then w.1 v else 0) from by
          split_ifs <;> first | exact ordered_nonneg V w v | exact le_rfl)]
      constructor
      · rintro ⟨v, _, hv⟩
        by_cases hav : a v = b
        · exact ⟨v, by simpa [hav] using hv, hav⟩
        · simp [hav] at hv
      · rintro ⟨v, hv, hav⟩
        exact ⟨v, Finset.mem_univ v, by simpa [hav] using hv⟩
    have ordered_vertex_map (V W : Type) [PartialOrder V] [PartialOrder W]
        [Fintype V] [Fintype W] (a : V → W)
        (ha : ∀ v z, v ≤ z ∨ z ≤ v → a v ≤ a z ∨ a z ≤ a v) :
        ∃ f : C(OrderedRealization V, OrderedRealization W),
          ∀ w b, (f w).1 b = ∑ v, if a v = b then w.1 v else 0 := by
      choose f hf using ordered_vertex_image V W a ha
      have hc : Continuous f := by
        apply (orderedCoordinate_embedding W).continuous_iff.mpr
        apply continuous_pi
        intro b
        have he : (fun w : OrderedRealization V => (f w).1 b) =
            fun w => ∑ v, if a v = b then w.1 v else 0 := funext (fun w => hf w b)
        change Continuous (fun w : OrderedRealization V => (f w).1 b)
        rw [he]
        apply continuous_finsetSum
        intro v _
        by_cases hav : a v = b
        · simp only [if_pos hav]
          exact orderedCoordinate_continuous V v
        · simp only [if_neg hav]
          exact continuous_const
      exact ⟨⟨f, hc⟩, hf⟩
    have ordered_face_point (V : Type) [PartialOrder V] (S : OrderedFace V) :
        ∃ w : OrderedRealization V, ∀ v, 0 < w.1 v ↔ v ∈ S.1 := by
      let q := orderedFaceDim S
      let u := barycenter q (fullFace q)
      have hu (i : Fin (q + 1)) : 0 < u.1 i :=
        (barycenter_positive q (fullFace q) i).mpr (Finset.mem_univ i)
      refine ⟨orderedChart q (faceVerticesN S) u, ?_⟩
      intro v
      change 0 < chainWeight q (faceVerticesN S) u v ↔ v ∈ S.1
      rw [chainWeight_positive_iff q (faceVerticesN S) (faceVerticesN S).injective u hu v]
      rw [faceVerticesN_range S]
      rfl
    have ordered_positive_comparable (V : Type) [PartialOrder V]
        (w : OrderedRealization V) (a b : V) (ha : 0 < w.1 a) (hb : 0 < w.1 b) :
        a ≤ b ∨ b ≤ a := by
      obtain ⟨S, hS, _, hchain⟩ := ordered_positive_support V w
      exact hchain a ((hS a).mpr ha) b ((hS b).mpr hb)
    have ordered_star_comparable (V W : Type) [PartialOrder V] [PartialOrder W]
        (f : OrderedRealization V → OrderedRealization W) (a : V → W)
        (hstar : ∀ v x, 0 < x.1 v → 0 < (f x).1 (a v)) :
        ∀ v z, v ≤ z ∨ z ≤ v → a v ≤ a z ∨ a z ≤ a v := by
      intro v z hvz
      let S : OrderedFace V := ⟨{v, z}, ⟨v, Finset.mem_insert_self v {z}⟩, by
        intro b hb c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb hc
        rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
        · exact Or.inl le_rfl
        · exact hvz
        · exact hvz.symm
        · exact Or.inl le_rfl⟩
      obtain ⟨x, hx⟩ := ordered_face_point V S
      exact ordered_positive_comparable W (f x) (a v) (a z)
        (hstar v x ((hx v).mpr (Finset.mem_insert_self v {z})))
        (hstar z x ((hx z).mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))))
    have ordered_star_homotopy (V W : Type) [PartialOrder V] [PartialOrder W]
        [Fintype V] [Fintype W] (f : C(OrderedRealization V, OrderedRealization W))
        (a : V → W) (hstar : ∀ v x, 0 < x.1 v → 0 < (f x).1 (a v)) :
        ∃ g : C(OrderedRealization V, OrderedRealization W),
        ∃ H : C(I × OrderedRealization V, OrderedRealization W),
          (∀ x b, (g x).1 b = ∑ v, if a v = b then x.1 v else 0) ∧
          (∀ x, H (0, x) = f x) ∧ (∀ x, H (1, x) = g x) ∧
          (∀ t x b, 0 < (H (t, x)).1 b → 0 < (f x).1 b) := by
      obtain ⟨g, hg⟩ := ordered_vertex_map V W a (ordered_star_comparable V W f a hstar)
      have hsupport (x : OrderedRealization V) (b : W) (hb : 0 < (g x).1 b) :
          0 < (f x).1 b := by
        obtain ⟨v, hv, rfl⟩ := (ordered_vertex_image_positive V W a x (g x) (hg x) b).mp hb
        exact hstar v x hv
      have hcompat (x : OrderedRealization V) (b c : W)
          (hb : 0 < (f x).1 b) (hc : 0 < (g x).1 c) : b ≤ c ∨ c ≤ b :=
        ordered_positive_comparable W (f x) b c hb (hsupport x c hc)
      obtain ⟨H, h0, h1, hH⟩ := ordered_line_homotopy W (OrderedRealization V) f g hcompat
      refine ⟨g, H, hg, h0, h1, ?_⟩
      intro t x b hb
      exact ordered_convex_preserves_full W (fun b => 0 < (f x).1 b)
        (f x) (g x) (H (t, x)) t (hH t x) (fun _ h => h) (hsupport x) b hb
    -- All statements use the existing chart-final topology on OrderedRealization.

    have sdChart_positive_iff {V : Type} [PartialOrder V] {r : ℕ}
        (C : Fin (r + 1) ↪o OrderedFace V) (u : Simplex r)
        (hu : ∀ i, 0 < u.1 i) (x : V) :
        0 < (sdChart C u).1 x ↔ x ∈ (C (Fin.last r)).1 := by
      change 0 < chainWeight (orderedFaceDim (C (Fin.last r)))
        (faceVerticesN (C (Fin.last r))) (chainBary _ r (sdFlag C).1 u) x ↔ _
      exact (chainWeight_positive_iff _ (faceVerticesN (C (Fin.last r)))
        (faceVerticesN (C (Fin.last r))).injective (chainBary _ r (sdFlag C).1 u)
        (flagBary_positive _ r (sdFlag C) u hu) x).trans
          (Set.ext_iff.mp (faceVerticesN_range (C (Fin.last r))) x)
    have sdChart_positive_unique (V : Type) [PartialOrder V] (r s : ℕ)
        (C : Fin (r + 1) ↪o OrderedFace V) (D : Fin (s + 1) ↪o OrderedFace V)
        (u : Simplex r) (v : Simplex s) (hu : ∀ i, 0 < u.1 i) (hv : ∀ i, 0 < v.1 i)
        (he : sdChart C u = sdChart D v) :
        (⟨r, (C, u)⟩ : Σ k, (Fin (k + 1) ↪o OrderedFace V) × Simplex k) = ⟨s, (D, v)⟩ := by
      have htop : C (Fin.last r) = D (Fin.last s) := by
        apply Subtype.ext
        ext x
        calc
          x ∈ (C (Fin.last r)).1 ↔ 0 < (sdChart C u).1 x :=
            (sdChart_positive_iff C u hu x).symm
          _ ↔ 0 < (sdChart D v).1 x := by rw [he]
          _ ↔ x ∈ (D (Fin.last s)).1 := sdChart_positive_iff D v hv x
      let B := C (Fin.last r)
      have hDB : D (Fin.last s) ≤ B := le_of_eq htop.symm
      have hCi (i : Fin (r + 1)) : C i ≤ B := C.monotone (Fin.le_last i)
      have hDi (i : Fin (s + 1)) : D i ≤ B := (D.monotone (Fin.le_last i)).trans hDB
      let P : Fin (r + 1) → Face (orderedFaceDim B) := fun i => faceSubset (C i) B (hCi i)
      let Q : Fin (s + 1) → Face (orderedFaceDim B) := fun i => faceSubset (D i) B (hDi i)
      have hP : ∀ i j, i < j → (P i).1 ⊂ (P j).1 := fun i j hij =>
        faceSubset_strict (C i) (C j) B (hCi i) (hCi j) (C.strictMono hij)
      have hQ : ∀ i j, i < j → (Q i).1 ⊂ (Q j).1 := fun i j hij =>
        faceSubset_strict (D i) (D j) B (hDi i) (hDi j) (D.strictMono hij)
      have hchar :
          orderedChart (orderedFaceDim B) (faceVerticesN B) (chainBary (orderedFaceDim B) r P u) =
            orderedChart (orderedFaceDim B) (faceVerticesN B)
              (chainBary (orderedFaceDim B) s Q v) :=
        (sdChart_in_upper C B le_rfl u).symm.trans (he.trans (sdChart_in_upper D B hDB v))
      have hcoord : chainBary (orderedFaceDim B) r P u = chainBary (orderedFaceDim B) s Q v :=
        orderedChart_injective (orderedFaceDim B) (faceVerticesN B) hchar
      have hchain := chainBary_positive_unique (orderedFaceDim B) r s P Q hP hQ u v hu hv hcoord
      have hrs : r = s := congrArg Sigma.fst hchain
      subst s
      have hpairs : (P, u) = (Q, v) := eq_of_heq (Sigma.mk.inj_iff.mp hchain).2
      have hCD : C = D := by
        apply DFunLike.ext
        intro i
        exact faceSubset_injective (C i) (D i) B (hCi i) (hDi i)
          (congrFun (congrArg Prod.fst hpairs) i)
      have huv : u = v := congrArg Prod.snd hpairs
      subst D
      subst v
      rfl

    -- Besides that block, this uses chainWeight_image/outside, chainBary_apply,
    -- simplex_threshold_chain, and ordered_positive_rep from candidate-face-saved.lean.

    -- A coordinate formula independent of the enumeration of the largest face.
    have sdChart_apply {V : Type} [PartialOrder V] {r : ℕ}
        (C : Fin (r + 1) ↪o OrderedFace V) (u : Simplex r) (x : V) :
        (sdChart C u).1 x =
          ∑ i, if x ∈ (C i).1 then u.1 i / ((C i).1.card : ℝ) else 0 := by
      let B := C (Fin.last r)
      by_cases hx : x ∈ B.1
      · have hex : x ∈ Set.range (faceVerticesN B) := by
          rw [faceVerticesN_range B]
          exact hx
        obtain ⟨j, rfl⟩ := hex
        change chainWeight (orderedFaceDim B) (faceVerticesN B)
          (chainBary (orderedFaceDim B) r (sdFlag C).1 u) (faceVerticesN B j) = _
        rw [chainWeight_image (orderedFaceDim B) (faceVerticesN B)
          (faceVerticesN B).injective (chainBary (orderedFaceDim B) r (sdFlag C).1 u) j,
          chainBary_apply (orderedFaceDim B) r (sdFlag C).1 u j]
        apply Finset.sum_congr rfl
        intro i _
        change (if j ∈ (faceSubset (C i) B (C.monotone (Fin.le_last i))).1 then
            u.1 i / ((faceSubset (C i) B (C.monotone (Fin.le_last i))).1.card : ℝ) else 0) =
          (if faceVerticesN B j ∈ (C i).1 then u.1 i / ((C i).1.card : ℝ) else 0)
        simp only [faceSubset_mem (C i) B (C.monotone (Fin.le_last i)) j,
          faceSubset_card (C i) B (C.monotone (Fin.le_last i))]
      · have hout : x ∉ Set.range (faceVerticesN B) := by
          rw [faceVerticesN_range B]
          exact hx
        change chainWeight (orderedFaceDim B) (faceVerticesN B)
          (chainBary (orderedFaceDim B) r (sdFlag C).1 u) x = _
        rw [chainWeight_outside (orderedFaceDim B) (faceVerticesN B)
          (chainBary (orderedFaceDim B) r (sdFlag C).1 u) x hout]
        symm
        apply Finset.sum_eq_zero
        intro i _
        exact if_neg (fun hi => hx ((C.monotone (Fin.le_last i)) hi))

    -- Map a nonempty standard face into the ordered vertex set along a chain.
    let orderedFaceImage {V : Type} [PartialOrder V] {q : ℕ}
        (A : Fin (q + 1) ↪o V) (S : Face q) : OrderedFace V :=
      ⟨S.1.map A.toEmbedding, S.2.map, by
        intro x hx y hy
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hy
        change A i ≤ A j ∨ A j ≤ A i
        exact (le_total i j).imp (fun h => A.monotone h) (fun h => A.monotone h)⟩
    have orderedFaceImage_mem {V : Type} [PartialOrder V] {q : ℕ}
        (A : Fin (q + 1) ↪o V) (S : Face q) (i : Fin (q + 1)) :
        A i ∈ (orderedFaceImage A S).1 ↔ i ∈ S.1 :=
      Finset.mem_map' A.toEmbedding
    have orderedFaceImage_card {V : Type} [PartialOrder V] {q : ℕ}
        (A : Fin (q + 1) ↪o V) (S : Face q) :
        (orderedFaceImage A S).1.card = S.1.card := by
      simp only [orderedFaceImage, Finset.card_map]
    have orderedFaceImage_strict {V : Type} [PartialOrder V] {q : ℕ}
        (A : Fin (q + 1) ↪o V) (S T : Face q) (hST : S.1 ⊂ T.1) :
        orderedFaceImage A S < orderedFaceImage A T := by
      change S.1.map A.toEmbedding ⊂ T.1.map A.toEmbedding
      exact Finset.map_ssubset_map.mpr hST
    let sdChain {V : Type} [PartialOrder V] {q r : ℕ}
        (A : Fin (q + 1) ↪o V) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) :
        Fin (r + 1) ↪o OrderedFace V :=
      OrderEmbedding.ofStrictMono (fun i => orderedFaceImage A (C i))
        (fun i j hij => orderedFaceImage_strict A (C i) (C j) (hC i j hij))
    have sdChain_char {V : Type} [PartialOrder V] {q r : ℕ}
        (A : Fin (q + 1) ↪o V) (C : Fin (r + 1) → Face q)
        (hC : ∀ i j, i < j → (C i).1 ⊂ (C j).1) (u : Simplex r) :
        sdChart (sdChain A C hC) u = orderedChart q A (chainBary q r C u) := by
      apply Subtype.ext
      funext x
      rw [sdChart_apply (sdChain A C hC) u x]
      change (∑ i, if x ∈ (orderedFaceImage A (C i)).1 then
          u.1 i / ((orderedFaceImage A (C i)).1.card : ℝ) else 0) =
        chainWeight q A (chainBary q r C u) x
      by_cases hx : x ∈ Set.range A
      · obtain ⟨j, rfl⟩ := hx
        rw [chainWeight_image q A A.injective (chainBary q r C u) j,
          chainBary_apply q r C u j]
        apply Finset.sum_congr rfl
        intro i _
        simp only [orderedFaceImage_mem A (C i) j, orderedFaceImage_card A (C i)]
      · rw [chainWeight_outside q A (chainBary q r C u) x hx]
        apply Finset.sum_eq_zero
        intro i _
        apply if_neg
        intro hi
        obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi
        exact hx ⟨j, hj⟩
    have sdChart_positive_rep (V : Type) [PartialOrder V] (w : OrderedRealization V) :
        ∃ r : ℕ, ∃ C : Fin (r + 1) ↪o OrderedFace V, ∃ u : Simplex r,
          (∀ i, 0 < u.1 i) ∧ sdChart C u = w := by
      obtain ⟨q, A, v, _, hw⟩ := ordered_positive_rep V w
      obtain ⟨r, C, u, hC, hu, hcoord, _⟩ := simplex_threshold_chain q v
      refine ⟨r, sdChain A C hC, u, hu, ?_⟩
      rw [sdChain_char A C hC u,
        show chainBary q r C u = v from Subtype.ext (funext hcoord)]
      exact hw

    -- The standard chart decomposition immediately identifies the final topology.
    -- This part uses sdChain / sdChain_char from the coverage block above.
    have sdChart_final (V Z : Type) [PartialOrder V] [TopologicalSpace Z]
        (f : OrderedRealization V → Z)
        (hf : ∀ r (C : Fin (r + 1) ↪o OrderedFace V), Continuous (f ∘ sdChart C)) :
        Continuous f := by
      apply orderedRealization_final V Z f
      intro q A
      apply continuous_of_chainBary q Z (f ∘ orderedChart q A)
      intro r C hC
      have he : (f ∘ orderedChart q A) ∘ chainBary q r C = f ∘ sdChart (sdChain A C hC) := by
        funext u
        exact congrArg f (sdChain_char A C hC u).symm
      rw [he]
      exact hf r (sdChain A C hC)
    have orderedSubdivisionHomeomorph_exists (V : Type) [PartialOrder V] :
        ∃ e : OrderedRealization (OrderedFace V) ≃ₜ OrderedRealization V,
          ∀ r (C : Fin (r + 1) ↪o OrderedFace V) (u : Simplex r),
            e (orderedChart r C u) = sdChart C u := by
      apply orderedRealization_homeomorph (OrderedFace V) (OrderedRealization V)
        (fun _ C u => sdChart C u)
      · intro r C
        exact sdChart_continuous C
      · intro r s b C u
        exact sdChart_face b C u
      · exact sdChart_positive_rep V
      · intro r s C D u v hu hv he
        exact sdChart_positive_unique V r s C D u v hu hv he
      · intro Z _ f hf
        exact sdChart_final V Z f hf
    let orderedSubdivisionHomeomorph (V : Type) [PartialOrder V] :
        OrderedRealization (OrderedFace V) ≃ₜ OrderedRealization V :=
      Classical.choose (orderedSubdivisionHomeomorph_exists V)
    have orderedSubdivisionHomeomorph_chart (V : Type) [PartialOrder V] (r : ℕ)
        (C : Fin (r + 1) ↪o OrderedFace V) (u : Simplex r) :
        orderedSubdivisionHomeomorph V (orderedChart r C u) = sdChart C u :=
      Classical.choose_spec (orderedSubdivisionHomeomorph_exists V) r C u
    have orderedSubdivisionHomeomorph_full (V : Type) [PartialOrder V] (P : V → Prop)
        (w : OrderedRealization (OrderedFace V)) :
        (∀ v, 0 < (orderedSubdivisionHomeomorph V w).1 v → P v) ↔
          (∀ S, 0 < w.1 S → ∀ v ∈ S.1, P v) := by
      obtain ⟨r, C, u, hu, hw⟩ := ordered_positive_rep (OrderedFace V) w
      rw [← hw, orderedSubdivisionHomeomorph_chart V r C u]
      constructor
      · intro h S hS v hv
        change 0 < chainWeight r C u S at hS
        obtain ⟨i, rfl⟩ := (chainWeight_positive_iff r C C.injective u hu S).mp hS
        exact h v ((sdChart_positive_iff C u hu v).mpr
          ((C.monotone (Fin.le_last i)) hv))
      · intro h v hv
        have hlast : 0 < (orderedChart r C u).1 (C (Fin.last r)) := by
          change 0 < chainWeight r C u (C (Fin.last r))
          rw [chainWeight_image r C C.injective u (Fin.last r)]
          exact hu (Fin.last r)
        exact h (C (Fin.last r)) hlast v ((sdChart_positive_iff C u hu v).mp hv)
    let vertexChain {V : Type} [PartialOrder V] (v : V) : Fin 1 ↪o V :=
      OrderEmbedding.ofMapLEIff (fun _ => v) (by
        intro i j
        exact iff_of_true le_rfl (le_of_eq (Subsingleton.elim i j)))
    let orderedVertex (V : Type) [PartialOrder V] (v : V) : OrderedRealization V :=
      orderedChart 0 (vertexChain v) (barycenter 0 (fullFace 0))
    have orderedVertex_apply (V : Type) [PartialOrder V] (v b : V) :
        (orderedVertex V v).1 b = if v = b then 1 else 0 := by
      have hu : (barycenter 0 (fullFace 0)).1 0 = 1 := by
        have hs := (barycenter 0 (fullFace 0)).2.2
        change (∑ i : Fin 1, (barycenter 0 (fullFace 0)).1 i) = 1 at hs
        simpa only [Fin.sum_univ_one] using hs
      change (∑ i : Fin 1, if v = b then (barycenter 0 (fullFace 0)).1 i else 0) = _
      rw [Fin.sum_univ_one, hu]
    have orderedVertex_positive (V : Type) [PartialOrder V] (v b : V) :
        0 < (orderedVertex V v).1 b ↔ v = b := by
      rw [orderedVertex_apply V v b]
      by_cases h : v = b <;> simp [h]
    have orderedChart_affine (V : Type) [PartialOrder V] (r : ℕ)
        (C : Fin (r + 1) ↪o V) (u : Simplex r) :
        (orderedChart r C u).1 = ∑ i, u.1 i • (orderedVertex V (C i)).1 := by
      funext b
      change (∑ i, if C i = b then u.1 i else 0) = _
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [orderedVertex_apply V (C i) b]
      by_cases h : C i = b <;> simp [h]
    -- T8: a uniform radius for the inverse images of target open stars.
    -- Read-only source verification: Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean:120.
    -- The imported theorem has [PseudoMetricSpace X], an arbitrary Sort-indexed
    -- open cover of a compact set s, and conclusion:
    --   ∃ δ > 0, ∀ x ∈ s, ∃ i, Metric.ball x δ ⊆ c i.
    have ordered_star_lebesgue (X W : Type) [PseudoMetricSpace X] [CompactSpace X]
        [PartialOrder W] (f : C(X, OrderedRealization W)) :
        ∃ δ : ℝ, 0 < δ ∧ ∀ x : X, ∃ w : W,
          ∀ y : X, dist y x < δ → 0 < (f y).1 w := by
      let U : W → Set X := fun w => {x | 0 < (f x).1 w}
      have hU : ∀ w, IsOpen (U w) := by
        intro w
        exact (ordered_star_open W w).preimage f.continuous
      have hcover : (Set.univ : Set X) ⊆ ⋃ w, U w := by
        intro x _
        obtain ⟨w, hw⟩ := ordered_has_positive W (f x)
        exact Set.mem_iUnion.mpr ⟨w, hw⟩
      obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
        (s := (Set.univ : Set X)) (c := U) isCompact_univ hU hcover
      refine ⟨δ, hδ, ?_⟩
      intro x
      obtain ⟨w, hw⟩ := hball x (Set.mem_univ x)
      refine ⟨w, ?_⟩
      intro y hy
      exact hw (Metric.mem_ball.mpr hy)

    -- Use the radius supplied by ordered_star_lebesgue.
    -- The metric ball convention is dist (g x) (g (p v)) < δ.
    -- The caller supplies its actual vertex-point function p; its singleton
    -- property is not needed by this selection argument.
    -- For a finite source this is precisely the small-image-open-star condition.
    -- The selection argument itself remains valid without any finiteness assumption.
    have ordered_star_selection_of_small_stars
        (V X W : Type) [PartialOrder V] [PseudoMetricSpace X] [PartialOrder W]
        (f : C(X, OrderedRealization W)) (g : C(OrderedRealization V, X))
        (p : V → OrderedRealization V) (δ : ℝ)
        (hcover : ∀ x : X, ∃ w : W,
          ∀ y : X, dist y x < δ → 0 < (f y).1 w)
        (hsmall : ∀ (v : V) (x : OrderedRealization V), 0 < x.1 v →
          dist (g x) (g (p v)) < δ) :
        ∃ a : V → W, ∀ (v : V) (x : OrderedRealization V),
          0 < x.1 v → 0 < (f (g x)).1 (a v) := by
      classical
      choose a ha using (fun v : V => hcover (g (p v)))
      refine ⟨a, ?_⟩
      intro v x hx
      exact ha v (g x) (hsmall v x hx)

    -- finite_mean_nested_dist_dim from mesh-shrink-block / the existing candidate.
    -- W needs only PartialOrder; neither Finite W nor Nonempty W is assumed.
    -- For the requested target V -> Real, instantiate E := V -> Real with [Fintype V].

    let orderedAffine {W E : Type} [PartialOrder W] [AddCommGroup E] [Module ℝ E]
        (f : OrderedRealization W → E) (g : W → E) : Prop :=
      ∀ q (A : Fin (q + 1) ↪o W) (u : Simplex q),
        f (orderedChart q A u) = ∑ i, u.1 i • g (A i)
    let orderedFaceMean {W E : Type} [PartialOrder W] [AddCommGroup E] [Module ℝ E]
        (g : W → E) (S : OrderedFace W) : E :=
      S.1.centerMass (fun _ => (1 : ℝ)) g

    -- A uniform chain-length bound is exactly the dimension hypothesis needed below.
    have orderedFace_card_bound {W : Type} [PartialOrder W] (d : ℕ)
        (hdim : ∀ q (A : Fin (q + 1) ↪o W), q ≤ d) (S : OrderedFace W) :
        S.1.card ≤ d + 1 := by
      rw [orderedFace_card S]
      exact Nat.add_le_add_right (hdim (orderedFaceDim S) (faceVerticesN S)) 1
    have orderedFace_dimension_bound {W : Type} [PartialOrder W] (d : ℕ)
        (hdim : ∀ q (A : Fin (q + 1) ↪o W), q ≤ d) :
        ∀ r (C : Fin (r + 1) ↪o OrderedFace W), r ≤ d := by
      intro r C
      exact (chain_length_le (orderedFaceDim (C (Fin.last r))) r
        (sdFlag C).1 (sdFlag C).2.1).trans
          (hdim (orderedFaceDim (C (Fin.last r))) (faceVerticesN (C (Fin.last r))))

    have barycenter_affine_sum {E : Type} [AddCommGroup E] [Module ℝ E]
        (q : ℕ) (S : Face q) (g : Fin (q + 1) → E) :
        (∑ j, (barycenter q S).1 j • g j) = S.1.centerMass (fun _ => (1 : ℝ)) g := by
      simp [barycenter, Finset.centerMass, ite_smul, Finset.sum_ite, ← Finset.smul_sum]
    have chainBary_affine_sum {E : Type} [AddCommGroup E] [Module ℝ E]
        (q r : ℕ) (C : Fin (r + 1) → Face q) (u : Simplex r) (g : Fin (q + 1) → E) :
        (∑ j, (chainBary q r C u).1 j • g j) =
          ∑ i, u.1 i • (C i).1.centerMass (fun _ => (1 : ℝ)) g := by
      change (∑ j, (∑ i, u.1 i * (barycenter q (C i)).1 j) • g j) = _
      simp_rw [Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ j, (u.1 i * (barycenter q (C i)).1 j) • g j) =
            u.1 i • ∑ j, (barycenter q (C i)).1 j • g j := by
          simp only [Finset.smul_sum, smul_smul]
        _ = u.1 i • (C i).1.centerMass (fun _ => (1 : ℝ)) g :=
          congrArg (fun z : E => u.1 i • z) (barycenter_affine_sum q (C i) g)

    -- Reindexing the finite mean from the upper simplex back to its actual vertices.
    have faceSubset_image_vertices {W : Type} [PartialOrder W] (S T : OrderedFace W)
        (hST : S ≤ T) :
        (faceSubset S T hST).1.map (faceVerticesN T).toEmbedding = S.1 := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
        exact (faceSubset_mem S T hST j).mp hj
      · intro hx
        have hr : x ∈ Set.range (faceVerticesN T) := by
          rw [faceVerticesN_range T]
          exact hST hx
        obtain ⟨j, rfl⟩ := hr
        exact Finset.mem_map.mpr ⟨j, (faceSubset_mem S T hST j).mpr hx, rfl⟩
    have faceSubset_centerMass {W E : Type} [PartialOrder W] [AddCommGroup E] [Module ℝ E]
        (S T : OrderedFace W) (hST : S ≤ T) (g : W → E) :
        (faceSubset S T hST).1.centerMass (fun _ => (1 : ℝ)) (fun j => g (faceVerticesN T j)) =
          orderedFaceMean g S := by
      have h := congrArg (fun U : Finset W => U.centerMass (fun _ => (1 : ℝ)) g)
        (faceSubset_image_vertices S T hST)
      simpa only [orderedFaceMean, Finset.centerMass, Finset.sum_map, RelEmbedding.coe_toEmbedding] using h

    have orderedAffine_sdChart {W E : Type} [PartialOrder W] [AddCommGroup E] [Module ℝ E]
        (f : OrderedRealization W → E) (g : W → E) (hf : orderedAffine f g)
        {r : ℕ} (C : Fin (r + 1) ↪o OrderedFace W) (u : Simplex r) :
        f (sdChart C u) = ∑ i, u.1 i • orderedFaceMean g (C i) := by
      let B := C (Fin.last r)
      change f (orderedChart (orderedFaceDim B) (faceVerticesN B)
        (chainBary (orderedFaceDim B) r (sdFlag C).1 u)) = _
      rw [hf (orderedFaceDim B) (faceVerticesN B) (chainBary (orderedFaceDim B) r (sdFlag C).1 u),
        chainBary_affine_sum (orderedFaceDim B) r (sdFlag C).1 u (fun j => g (faceVerticesN B j))]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : E => u.1 i • z)
        (faceSubset_centerMass (C i) B (C.monotone (Fin.le_last i)) g)
    have orderedAffine_subdivision {W E : Type} [PartialOrder W] [AddCommGroup E] [Module ℝ E]
        (f : OrderedRealization W → E) (g : W → E) (hf : orderedAffine f g) :
        orderedAffine (f ∘ orderedSubdivisionHomeomorph W) (orderedFaceMean g) := by
      intro r C u
      change f (orderedSubdivisionHomeomorph W (orderedChart r C u)) = _
      rw [orderedSubdivisionHomeomorph_chart W r C u]
      exact orderedAffine_sdChart f g hf C u
    have orderedAffine_continuous {W E : Type} [PartialOrder W]
        [SeminormedAddCommGroup E] [NormedSpace ℝ E]
        (f : OrderedRealization W → E) (g : W → E) (hf : orderedAffine f g) : Continuous f := by
      apply orderedRealization_final W E f
      intro q A
      have he : f ∘ orderedChart q A = fun u : Simplex q => ∑ i, u.1 i • g (A i) :=
        funext (fun u => hf q A u)
      rw [he]
      apply continuous_finsetSum
      intro i _
      exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const

    -- Mesh is expressed intrinsically on comparable vertices. This property iterates
    -- with g' = orderedFaceMean g, W' = OrderedFace W, D' = (d/(d+1))*D.
    have orderedFaceMean_mesh {W E : Type} [PartialOrder W]
        [SeminormedAddCommGroup E] [NormedSpace ℝ E]
        (d : ℕ) (hdim : ∀ q (A : Fin (q + 1) ↪o W), q ≤ d)
        (g : W → E) (D : ℝ)
        (hmesh : ∀ a b : W, a ≤ b ∨ b ≤ a → dist (g a) (g b) ≤ D)
        (S T : OrderedFace W) (hST : S ≤ T ∨ T ≤ S) :
        dist (orderedFaceMean g S) (orderedFaceMean g T) ≤
          ((d : ℝ) / ((d : ℝ) + 1)) * D := by
      rcases hST with hST | hTS
      · exact finite_mean_nested_dist_dim S.1 T.1 g S.2.1 hST d
          (orderedFace_card_bound d hdim T) D (fun a ha b hb => hmesh a b (T.2.2 a ha b hb))
      · rw [dist_comm]
        exact finite_mean_nested_dist_dim T.1 S.1 g T.2.1 hTS d
          (orderedFace_card_bound d hdim S) D (fun a ha b hb => hmesh a b (S.2.2 a ha b hb))

    -- A bound for every pair of points in one new simplex, using the verified finite_chain_mesh.
    have orderedAffine_sdChart_mesh {W E : Type} [PartialOrder W]
        [SeminormedAddCommGroup E] [NormedSpace ℝ E]
        (d : ℕ) (hdim : ∀ q (A : Fin (q + 1) ↪o W), q ≤ d)
        (f : OrderedRealization W → E) (g : W → E) (hf : orderedAffine f g)
        (D : ℝ) (hmesh : ∀ a b : W, a ≤ b ∨ b ≤ a → dist (g a) (g b) ≤ D)
        {r : ℕ} (C : Fin (r + 1) ↪o OrderedFace W) (u v : Simplex r) :
        dist (f (sdChart C u)) (f (sdChart C v)) ≤
          ((d : ℝ) / ((d : ℝ) + 1)) * D := by
      let B := C (Fin.last r)
      let q := orderedFaceDim B
      let A := faceVerticesN B
      have hA (i j : Fin (q + 1)) : dist (g (A i)) (g (A j)) ≤ D :=
        hmesh (A i) (A j) ((le_total i j).imp (fun h => A.monotone h) (fun h => A.monotone h))
      have he (w : Simplex r) : f (sdChart C w) =
          ∑ i, w.1 i • ((sdFlag C).1 i).1.centerMass (fun _ => (1 : ℝ)) (fun j => g (A j)) := by
        change f (orderedChart q A (chainBary q r (sdFlag C).1 w)) = _
        rw [hf q A (chainBary q r (sdFlag C).1 w),
          chainBary_affine_sum q r (sdFlag C).1 w (fun j => g (A j))]
      rw [he u, he v]
      have hm := finite_chain_mesh q r (fun j => g (A j)) (sdFlag C).1 (sdFlag C).2.1 D hA u v
      have hq : q ≤ d := hdim q A
      have hD0 : 0 ≤ D := by simpa only [dist_self] using hA 0 0
      have hratio : (q : ℝ) / ((q : ℝ) + 1) ≤ (d : ℝ) / ((d : ℝ) + 1) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have hqd : (q : ℝ) ≤ (d : ℝ) := by exact_mod_cast hq
        nlinarith
      exact hm.trans (mul_le_mul_of_nonneg_right hratio hD0)

    -- A single recursive package: dimension, affine charts, and vertex mesh all persist.
    have orderedSubdivision_step {W E : Type} [PartialOrder W]
        [SeminormedAddCommGroup E] [NormedSpace ℝ E]
        (d : ℕ) (hdim : ∀ q (A : Fin (q + 1) ↪o W), q ≤ d)
        (f : OrderedRealization W → E) (g : W → E) (hf : orderedAffine f g)
        (D : ℝ) (hmesh : ∀ a b : W, a ≤ b ∨ b ≤ a → dist (g a) (g b) ≤ D) :
        (∀ r (C : Fin (r + 1) ↪o OrderedFace W), r ≤ d) ∧
        orderedAffine (f ∘ orderedSubdivisionHomeomorph W) (orderedFaceMean g) ∧
        (∀ S T : OrderedFace W, S ≤ T ∨ T ≤ S →
          dist (orderedFaceMean g S) (orderedFaceMean g T) ≤
            ((d : ℝ) / ((d : ℝ) + 1)) * D) :=
      ⟨orderedFace_dimension_bound d hdim, orderedAffine_subdivision f g hf,
        fun S T hST => orderedFaceMean_mesh d hdim g D hmesh S T hST⟩

    -- No global finiteness is needed for this algebraic identity. Norm/mesh specialization
    -- to E = (V -> Real) requires [Fintype V] for the standard sup-norm instance.
    -- Nonnegativity of D is inferred locally from a vertex; there is no extra D >= 0 premise.
    -- The case d = 0 is retained and gives the factor 0 without any division by d.
    have orderedAffine_vertex {W E : Type} [PartialOrder W] [AddCommGroup E] [Module ℝ E]
        (f : OrderedRealization W → E) (g : W → E) (hf : orderedAffine f g) (v : W) :
        f (orderedVertex W v) = g v := by
      have hu : (barycenter 0 (fullFace 0)).1 0 = 1 := by
        have hs := (barycenter 0 (fullFace 0)).2.2
        change (∑ i : Fin 1, (barycenter 0 (fullFace 0)).1 i) = 1 at hs
        simpa only [Fin.sum_univ_one] using hs
      have h := hf 0 (vertexChain v) (barycenter 0 (fullFace 0))
      rw [Fin.sum_univ_one, hu, one_smul] at h
      exact h
    have orderedAffine_star_dist {W E : Type} [PartialOrder W]
        [SeminormedAddCommGroup E] [NormedSpace ℝ E]
        (f : OrderedRealization W → E) (g : W → E) (hf : orderedAffine f g)
        (D : ℝ) (hmesh : ∀ a b : W, a ≤ b ∨ b ≤ a → dist (g a) (g b) ≤ D)
        (w : OrderedRealization W) (v : W) (hv : 0 < w.1 v) :
        dist (f w) (g v) ≤ D := by
      obtain ⟨r, C, u, hu, hw⟩ := ordered_positive_rep W w
      rw [← hw] at hv ⊢
      change 0 < chainWeight r C u v at hv
      obtain ⟨i, rfl⟩ := (chainWeight_positive_iff r C C.injective u hu v).mp hv
      rw [hf r C u]
      have hconv : (∑ j, u.1 j • g (C j)) ∈ convexHull ℝ (Set.range (fun j => g (C j))) :=
        (convex_convexHull ℝ _).sum_mem (fun j _ => u.2.1 j) u.2.2
          (fun j _ => subset_convexHull ℝ _ ⟨j, rfl⟩)
      obtain ⟨x, ⟨j, rfl⟩, hx⟩ := convexHull_exists_dist_ge hconv (g (C i))
      exact hx.trans (hmesh (C j) (C i) ((le_total j i).imp (fun h => C.monotone h) (fun h => C.monotone h)))
    have mesh_power_small_all (d : ℕ) (D δ : ℝ) (hD : 0 ≤ D) (hδ : 0 < δ) :
        ∃ k : ℕ, D * ((d : ℝ) / ((d : ℝ) + 1)) ^ k < δ := by
      by_cases hd : d = 0
      · subst d
        exact ⟨1, by simpa using hδ⟩
      · obtain ⟨k, hk⟩ := mesh_power_small d (Nat.pos_of_ne_zero hd) D δ hδ
        have hp : 0 ≤ ((d : ℝ) / ((d : ℝ) + 1)) ^ k := pow_nonneg (by positivity) k
        refine ⟨k, ?_⟩
        nlinarith [mul_nonneg hD hp]
    have ordered_dimension_bound (V : Type) [PartialOrder V] [Fintype V] :
        ∀ q (A : Fin (q + 1) ↪o V), q ≤ Fintype.card V := by
      intro q A
      have h := Fintype.card_le_of_injective A A.injective
      simp only [Fintype.card_fin] at h
      omega
    have orderedVertex_dist_le_one (V : Type) [PartialOrder V] [Fintype V] (a b : V) :
        dist (orderedVertex V a).1 (orderedVertex V b).1 ≤ 1 := by
      apply (dist_pi_le_iff zero_le_one).mpr
      intro v
      rw [orderedVertex_apply V a v, orderedVertex_apply V b v]
      by_cases ha : a = v <;> by_cases hb : b = v <;> simp [ha, hb, Real.dist_eq]
    -- The quantified type W stays in Type 0; its order and Fintype are explicit data.
    -- No relative/subcomplex data or approximation statement is included here.
    have orderedSubdivision_iterate (V : Type) [PartialOrder V] [Fintype V]
        (d : ℕ) (hdim : ∀ q (A : Fin (q + 1) ↪o V), q ≤ d)
        (D : ℝ)
        (hmesh : ∀ a b : V, a ≤ b ∨ b ≤ a →
          dist (orderedVertex V a).1 (orderedVertex V b).1 ≤ D)
        (k : ℕ) :
        ∃ W : Type, ∃ o : PartialOrder W, ∃ ft : Fintype W,
          letI : PartialOrder W := o
          letI : Fintype W := ft
          ∃ h : OrderedRealization W ≃ₜ OrderedRealization V,
          ∃ g : W → (V → ℝ),
            (∀ q (A : Fin (q + 1) ↪o W), q ≤ d) ∧
            orderedAffine (fun w : OrderedRealization W => (h w).1) g ∧
            (∀ a b : W, a ≤ b ∨ b ≤ a →
              dist (g a) (g b) ≤ D * ((d : ℝ) / ((d : ℝ) + 1)) ^ k) := by
      classical
      induction k with
      | zero =>
          refine ⟨V, inferInstance, inferInstance, ?_⟩
          refine ⟨Homeomorph.refl (OrderedRealization V),
            (fun v : V => (orderedVertex V v).1), hdim, ?_, ?_⟩
          · change orderedAffine (fun w : OrderedRealization V => w.1)
              (fun v : V => (orderedVertex V v).1)
            exact orderedChart_affine V
          · intro a b hab
            simpa only [pow_zero, mul_one] using hmesh a b hab
      | succ k ih =>
          obtain ⟨W, o, ft, hdata⟩ := ih
          letI : PartialOrder W := o
          letI : Fintype W := ft
          obtain ⟨h, g, hdimW, hAffineW, hmeshW⟩ := hdata
          letI : Fintype (OrderedFace W) := by
            dsimp only [OrderedFace]
            infer_instance
          have hstep := orderedSubdivision_step d hdimW
            (fun w : OrderedRealization W => (h w).1) g hAffineW
            (D * ((d : ℝ) / ((d : ℝ) + 1)) ^ k) hmeshW
          refine ⟨OrderedFace W, inferInstance, inferInstance, ?_⟩
          refine ⟨(orderedSubdivisionHomeomorph W).trans h, orderedFaceMean g,
            hstep.1, ?_, ?_⟩
          · change orderedAffine
              ((fun w : OrderedRealization W => (h w).1) ∘ orderedSubdivisionHomeomorph W)
              (orderedFaceMean g)
            exact hstep.2.1
          · intro S T hST
            calc
              dist (orderedFaceMean g S) (orderedFaceMean g T) ≤
                  ((d : ℝ) / ((d : ℝ) + 1)) *
                    (D * ((d : ℝ) / ((d : ℝ) + 1)) ^ k) := hstep.2.2 S T hST
              _ = D * ((d : ℝ) / ((d : ℝ) + 1)) ^ (k + 1) := by
                rw [pow_succ]
                ring

    -- This installs the exact instances carried by hdata before exposing its dependent terms.
    -- Fintype (OrderedFace W) is inferred from the finite Finset W type and its subtype predicate.
    -- No Nonempty V, positivity of d, or separate nonnegativity hypothesis on D is required.
    -- Keep the actual finite sequence of subdivisions available for the last-vertex pullbacks.
    let SubdivisionModel (V : Type) [PartialOrder V] :=
      Σ W : Type, Σ o : PartialOrder W, Σ ft : Fintype W,
        letI : PartialOrder W := o
        letI : Fintype W := ft
        OrderedRealization W ≃ₜ OrderedRealization V
    let subdivisionNext (V : Type) [PartialOrder V] (m : SubdivisionModel V) :
        SubdivisionModel V := by
      obtain ⟨W, o, ft, h⟩ := m
      letI : PartialOrder W := o
      letI : Fintype W := ft
      letI : Fintype (OrderedFace W) := by
        dsimp only [OrderedFace]
        infer_instance
      exact ⟨OrderedFace W, inferInstance, inferInstance, (orderedSubdivisionHomeomorph W).trans h⟩
    let subdivisionInitial (V : Type) [PartialOrder V] [Fintype V] : SubdivisionModel V :=
      ⟨V, inferInstance, inferInstance, Homeomorph.refl (OrderedRealization V)⟩
    let fixedSubdivision (V : Type) [PartialOrder V] [Fintype V] : ℕ → SubdivisionModel V :=
      Nat.rec (subdivisionInitial V) (fun _ m => subdivisionNext V m)
    let sdVertices (V : Type) [PartialOrder V] [Fintype V] (k : ℕ) : Type :=
      (fixedSubdivision V k).1
    letI (V : Type) [PartialOrder V] [Fintype V] (k : ℕ) : PartialOrder (sdVertices V k) :=
      (fixedSubdivision V k).2.1
    letI (V : Type) [PartialOrder V] [Fintype V] (k : ℕ) : Fintype (sdVertices V k) :=
      (fixedSubdivision V k).2.2.1
    let sdHomeomorph (V : Type) [PartialOrder V] [Fintype V] (k : ℕ) :
        OrderedRealization (sdVertices V k) ≃ₜ OrderedRealization V :=
      (fixedSubdivision V k).2.2.2
    have sdHomeomorph_zero (V : Type) [PartialOrder V] [Fintype V] :
        sdHomeomorph V 0 = Homeomorph.refl (OrderedRealization V) := rfl
    have sdHomeomorph_succ (V : Type) [PartialOrder V] [Fintype V] (k : ℕ) :
        sdHomeomorph V (k + 1) =
          (orderedSubdivisionHomeomorph (sdVertices V k)).trans (sdHomeomorph V k) := rfl
    have fixedSubdivision_mesh (V : Type) [PartialOrder V] [Fintype V]
        (d : ℕ) (hdim : ∀ q (A : Fin (q + 1) ↪o V), q ≤ d)
        (D : ℝ) (hmesh : ∀ a b : V, a ≤ b ∨ b ≤ a →
          dist (orderedVertex V a).1 (orderedVertex V b).1 ≤ D) (k : ℕ) :
        ∃ g : sdVertices V k → (V → ℝ),
          (∀ q (A : Fin (q + 1) ↪o sdVertices V k), q ≤ d) ∧
          orderedAffine (fun w : OrderedRealization (sdVertices V k) => (sdHomeomorph V k w).1) g ∧
          (∀ a b : sdVertices V k, a ≤ b ∨ b ≤ a →
            dist (g a) (g b) ≤ D * ((d : ℝ) / ((d : ℝ) + 1)) ^ k) := by
      induction k with
      | zero =>
          refine ⟨(fun v : V => (orderedVertex V v).1), hdim, ?_, ?_⟩
          · exact orderedChart_affine V
          · intro a b hab
            simpa only [pow_zero, mul_one] using hmesh a b hab
      | succ k ih =>
          obtain ⟨g, hdimW, hAffineW, hmeshW⟩ := ih
          have hstep := orderedSubdivision_step d hdimW
            (fun w : OrderedRealization (sdVertices V k) => (sdHomeomorph V k w).1)
            g hAffineW (D * ((d : ℝ) / ((d : ℝ) + 1)) ^ k) hmeshW
          refine ⟨orderedFaceMean g, hstep.1, ?_, ?_⟩
          · exact hstep.2.1
          · intro S T hST
            calc
              dist (orderedFaceMean g S) (orderedFaceMean g T) ≤
                  ((d : ℝ) / ((d : ℝ) + 1)) *
                    (D * ((d : ℝ) / ((d : ℝ) + 1)) ^ k) := hstep.2.2 S T hST
              _ = D * ((d : ℝ) / ((d : ℝ) + 1)) ^ (k + 1) := by
                rw [pow_succ]
                ring
    have fixedSubdivision_small_stars (V : Type) [PartialOrder V] [Fintype V]
        (δ : ℝ) (hδ : 0 < δ) :
        ∃ k : ℕ, ∀ v : sdVertices V k, ∀ x : OrderedRealization (sdVertices V k),
          0 < x.1 v → dist (sdHomeomorph V k x)
            (sdHomeomorph V k (orderedVertex (sdVertices V k) v)) < δ := by
      let d := Fintype.card V
      obtain ⟨k, hk⟩ := mesh_power_small_all d 1 δ zero_le_one hδ
      obtain ⟨g, _, hAffine, hmesh⟩ := fixedSubdivision_mesh V d (ordered_dimension_bound V) 1
        (fun a b _ => orderedVertex_dist_le_one V a b) k
      refine ⟨k, ?_⟩
      intro v x hx
      rw [ordered_dist_eq V, orderedAffine_vertex
        (fun w : OrderedRealization (sdVertices V k) => (sdHomeomorph V k w).1) g hAffine v]
      exact (orderedAffine_star_dist
        (fun w : OrderedRealization (sdVertices V k) => (sdHomeomorph V k w).1)
        g hAffine (1 * ((d : ℝ) / ((d : ℝ) + 1)) ^ k) hmesh x v hx).trans_lt hk
    have ordered_star_approximation (V W : Type) [PartialOrder V] [PartialOrder W]
        [Fintype V] [Fintype W] (f : C(OrderedRealization V, OrderedRealization W)) :
        ∃ k : ℕ, ∃ a : sdVertices V k → W,
        ∃ g : C(OrderedRealization (sdVertices V k), OrderedRealization W),
        ∃ H : C(I × OrderedRealization (sdVertices V k), OrderedRealization W),
          (∀ v x, 0 < x.1 v → 0 < (f (sdHomeomorph V k x)).1 (a v)) ∧
          (∀ x b, (g x).1 b = ∑ v, if a v = b then x.1 v else 0) ∧
          (∀ x, H (0, x) = f (sdHomeomorph V k x)) ∧ (∀ x, H (1, x) = g x) ∧
          (∀ t x b, 0 < (H (t, x)).1 b → 0 < (f (sdHomeomorph V k x)).1 b) := by
      letI : PseudoMetricSpace (OrderedRealization V) :=
        (Topology.IsEmbedding.comapMetricSpace (fun w : OrderedRealization V => w.1)
          (orderedCoordinate_embedding V)).toPseudoMetricSpace
      letI : CompactSpace (OrderedRealization V) := orderedRealization_compact V
      obtain ⟨δ, hδ, hcover⟩ := ordered_star_lebesgue (OrderedRealization V) W f
      obtain ⟨k, hk⟩ := fixedSubdivision_small_stars V δ hδ
      let h : C(OrderedRealization (sdVertices V k), OrderedRealization V) :=
        ⟨sdHomeomorph V k, (sdHomeomorph V k).continuous⟩
      obtain ⟨a, ha⟩ := ordered_star_selection_of_small_stars (sdVertices V k)
        (OrderedRealization V) W f h (orderedVertex (sdVertices V k)) δ hcover hk
      obtain ⟨g, H, hg, h0, h1, hsupport⟩ := ordered_star_homotopy (sdVertices V k) W (f.comp h) a ha
      exact ⟨k, a, g, H, ha, hg, h0, h1, hsupport⟩
    -- A6/C2: descending coordinate thresholds for the staircase cube.
    -- The sentinel 1 allows an empty first subset and handles r = 0 uniformly.
    have cube_positive_levels (r : ℕ) (x : Fin r → I) :
        ∃ k : ℕ, ∃ c : Fin (k + 1) → ℝ,
          StrictAnti c ∧ c 0 = 1 ∧ (∀ j, 0 < c j) ∧
          (∀ j, c j = 1 ∨ ∃ v : Fin r, (x v : ℝ) = c j) ∧
          (∀ v : Fin r, 0 < (x v : ℝ) → ∃ j, c j = (x v : ℝ)) := by
      classical
      let S : Finset ℝ :=
        insert 1 ((Finset.univ.image (fun v : Fin r => (x v : ℝ))).filter
          (fun t => 0 < t))
      have hone : (1 : ℝ) ∈ S := Finset.mem_insert_self _ _
      have hS : S.Nonempty := ⟨1, hone⟩
      have hbounds (t : ℝ) (ht : t ∈ S) : 0 < t ∧ t ≤ 1 := by
        rcases Finset.mem_insert.mp ht with h | h
        · subst t
          exact ⟨zero_lt_one, le_rfl⟩
        · obtain ⟨him, hp⟩ := Finset.mem_filter.mp h
          obtain ⟨v, _, hv⟩ := Finset.mem_image.mp him
          exact ⟨hp, hv ▸ (x v).2.2⟩
      let k := S.card - 1
      have hk : S.card = k + 1 := by
        have hcard := Finset.card_pos.mpr hS
        dsimp only [k]
        omega
      let e : Fin (k + 1) ↪o ℝ := S.orderEmbOfFin hk
      let c : Fin (k + 1) → ℝ := fun j => e j.rev
      have hmem (j : Fin (k + 1)) : c j ∈ S :=
        Finset.orderEmbOfFin_mem S hk j.rev
      have hanti : StrictAnti c := by
        intro i j hij
        exact e.strictMono (Fin.rev_lt_rev.mpr hij)
      have hcontains (t : ℝ) (ht : t ∈ S) : ∃ j, c j = t := by
        have hrange : t ∈ Set.range e := by
          rw [show Set.range e = (S : Set ℝ) from Finset.range_orderEmbOfFin S hk]
          exact ht
        obtain ⟨j, hj⟩ := hrange
        refine ⟨j.rev, ?_⟩
        simpa only [c, Fin.rev_rev] using hj
      have hzero : c 0 = 1 := by
        apply le_antisymm (hbounds _ (hmem 0)).2
        obtain ⟨j, hj⟩ := hcontains 1 hone
        rw [← hj]
        exact hanti.antitone (Fin.zero_le j)
      refine ⟨k, c, hanti, hzero, ?_, ?_, ?_⟩
      · intro j
        exact (hbounds _ (hmem j)).1
      · intro j
        rcases Finset.mem_insert.mp (hmem j) with h | h
        · exact Or.inl h
        · obtain ⟨v, _, hv⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
          exact Or.inr ⟨v, hv⟩
      · intro v hv
        apply hcontains
        exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩, hv⟩)

    -- The order embedding records strict nesting of subsets, including ∅ or univ.
    -- Unlike barycentric subdivision of a simplex, these weights have no card factor.
    have cube_threshold_chain (r : ℕ) (x : Fin r → I) :
        ∃ k : ℕ, ∃ C : Fin (k + 1) ↪o Finset (Fin r), ∃ u : Simplex k,
          (∀ j, 0 < u.1 j) ∧
          (∀ v : Fin r, (∑ j, if v ∈ C j then u.1 j else 0) = (x v : ℝ)) := by
      classical
      obtain ⟨k, c, hanti, hzero, hpos, hvalues, hcover⟩ := cube_positive_levels r x
      let faces : Fin (k + 1) → Finset (Fin r) :=
        fun j => Finset.univ.filter (fun v => c j ≤ (x v : ℝ))
      have hmem (j : Fin (k + 1)) (v : Fin r) :
          v ∈ faces j ↔ c j ≤ (x v : ℝ) := by
        simp only [faces, Finset.mem_filter, Finset.mem_univ, true_and]
      have hstrict : StrictMono faces := by
        intro i j hij
        have hsub : faces i ⊆ faces j := by
          intro v hv
          exact (hmem j v).mpr ((hanti hij).le.trans ((hmem i v).mp hv))
        apply (Finset.ssubset_iff_of_subset hsub).mpr
        have hjlt : c j < 1 := calc
          c j < c i := hanti hij
          _ ≤ c 0 := hanti.antitone (Fin.zero_le i)
          _ = 1 := hzero
        have hex : ∃ v : Fin r, (x v : ℝ) = c j := by
          rcases hvalues j with hone | hv
          · exact False.elim ((ne_of_lt hjlt) hone)
          · exact hv
        obtain ⟨v, hv⟩ := hex
        refine ⟨v, (hmem j v).mpr hv.ge, ?_⟩
        intro hiv
        have hle := (hmem i v).mp hiv
        rw [hv] at hle
        exact (not_le_of_gt (hanti hij)) hle
      let C : Fin (k + 1) ↪o Finset (Fin r) :=
        OrderEmbedding.ofStrictMono faces hstrict
      have hweights_pos (j : Fin (k + 1)) : 0 < thresholdGap k c j :=
        thresholdGap_pos k c hanti hpos j
      have hsum : (∑ j, thresholdGap k c j) = 1 := by
        calc
          (∑ j, thresholdGap k c j) = c 0 := by
            simpa only [Fin.zero_le, ↓reduceIte] using (thresholdGap_sum_ite k c 0)
          _ = 1 := hzero
      let u : Simplex k :=
        ⟨thresholdGap k c, ⟨fun j => (hweights_pos j).le, hsum⟩⟩
      refine ⟨k, C, u, hweights_pos, ?_⟩
      intro v
      change (∑ j, if v ∈ faces j then thresholdGap k c j else 0) = (x v : ℝ)
      by_cases hv : 0 < (x v : ℝ)
      · obtain ⟨i, hi⟩ := hcover v hv
        have htail (j : Fin (k + 1)) : v ∈ faces j ↔ i ≤ j := by
          rw [hmem j v, ← hi]
          exact hanti.le_iff_ge
        calc
          (∑ j, if v ∈ faces j then thresholdGap k c j else 0) =
              ∑ j, if i ≤ j then thresholdGap k c j else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [htail j]
          _ = c i := thresholdGap_sum_ite k c i
          _ = (x v : ℝ) := hi
      · have hz : (x v : ℝ) = 0 := le_antisymm (le_of_not_gt hv) (x v).2.1
        have hn (j : Fin (k + 1)) : v ∉ faces j := by
          intro hj
          have hle := (hmem j v).mp hj
          rw [hz] at hle
          exact (not_le_of_gt (hpos j)) hle
        rw [hz]
        apply Finset.sum_eq_zero
        intro j hj
        exact if_neg (hn j)
    let cubeCoordinate (r : ℕ) (w : OrderedRealization (Finset (Fin r))) (i : Fin r) : ℝ :=
      ∑ S : Finset (Fin r), if i ∈ S then w.1 S else 0
    have cubeCoordinate_nonneg (r : ℕ) (w : OrderedRealization (Finset (Fin r))) (i : Fin r) :
        0 ≤ cubeCoordinate r w i := by
      apply Finset.sum_nonneg
      intro S _
      split_ifs
      · exact ordered_nonneg (Finset (Fin r)) w S
      · exact le_rfl
    have cubeCoordinate_le_one (r : ℕ) (w : OrderedRealization (Finset (Fin r))) (i : Fin r) :
        cubeCoordinate r w i ≤ 1 := by
      calc
        cubeCoordinate r w i ≤ ∑ S : Finset (Fin r), w.1 S := by
          apply Finset.sum_le_sum
          intro S _
          split_ifs
          · exact le_rfl
          · exact ordered_nonneg (Finset (Fin r)) w S
        _ = 1 := ordered_total_weight (Finset (Fin r)) w
    have cubeCoordinate_continuous (r : ℕ) (i : Fin r) : Continuous (fun w => cubeCoordinate r w i) := by
      apply continuous_finsetSum
      intro S _
      by_cases hi : i ∈ S
      · simp only [if_pos hi]
        exact orderedCoordinate_continuous (Finset (Fin r)) S
      · simp only [if_neg hi]
        exact continuous_const
    let cubeMap (r : ℕ) : C(OrderedRealization (Finset (Fin r)), Fin r → I) :=
      ⟨fun w i => ⟨cubeCoordinate r w i, cubeCoordinate_nonneg r w i, cubeCoordinate_le_one r w i⟩,
        continuous_pi (fun i => (cubeCoordinate_continuous r i).subtype_mk _)⟩
    have cubeMap_chart (r q : ℕ) (C : Fin (q + 1) ↪o Finset (Fin r))
        (u : Simplex q) (i : Fin r) :
        (cubeMap r (orderedChart q C u) i : ℝ) = ∑ j, if i ∈ C j then u.1 j else 0 := by
      letI : DecidableEq (Finset (Fin r)) := Classical.decEq _
      dsimp only [cubeMap, ContinuousMap.coe_mk, cubeCoordinate, orderedChart, chainWeight]
      calc
        (∑ S : Finset (Fin r), if i ∈ S then (∑ j, if C j = S then u.1 j else 0) else 0) =
            ∑ S : Finset (Fin r), ∑ j, if C j = S then (if i ∈ S then u.1 j else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro S _
          by_cases hi : i ∈ S <;> simp [hi]
        _ = ∑ j, ∑ S : Finset (Fin r), if C j = S then (if i ∈ S then u.1 j else 0) else 0 :=
          Finset.sum_comm
        _ = ∑ j, if i ∈ C j then u.1 j else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          exact Fintype.sum_ite_eq (C j) (fun S => if i ∈ S then u.1 j else 0)
    have cubeMap_vertex (r : ℕ) (S : Finset (Fin r)) (i : Fin r) :
        (cubeMap r (orderedVertex (Finset (Fin r)) S) i : ℝ) = if i ∈ S then 1 else 0 := by
      letI : DecidableEq (Finset (Fin r)) := Classical.decEq _
      change (∑ T : Finset (Fin r), if i ∈ T then (orderedVertex (Finset (Fin r)) S).1 T else 0) = _
      simp_rw [orderedVertex_apply (Finset (Fin r)) S]
      have he (T : Finset (Fin r)) : (if i ∈ T then (if S = T then (1 : ℝ) else 0) else 0) =
          (if S = T then (if i ∈ T then 1 else 0) else 0) := by
        by_cases hi : i ∈ T <;> by_cases hST : S = T <;> simp [hi, hST]
      calc
        (∑ T : Finset (Fin r), if i ∈ T then (if S = T then (1 : ℝ) else 0) else 0) =
            ∑ T : Finset (Fin r), if S = T then (if i ∈ T then 1 else 0) else 0 :=
          Finset.sum_congr rfl (fun T _ => he T)
        _ = if i ∈ S then 1 else 0 := Fintype.sum_ite_eq S (fun T => if i ∈ T then (1 : ℝ) else 0)
    have cubeMap_positive_rep (r : ℕ) (x : Fin r → I) :
        ∃ q : ℕ, ∃ C : Fin (q + 1) ↪o Finset (Fin r), ∃ u : Simplex q,
          (∀ j, 0 < u.1 j) ∧ cubeMap r (orderedChart q C u) = x := by
      obtain ⟨q, C, u, hu, he⟩ := cube_threshold_chain r x
      refine ⟨q, C, u, hu, ?_⟩
      funext i
      apply Subtype.ext
      exact (cubeMap_chart r q C u i).trans (he i)
    have cubeMap_surjective (r : ℕ) : Function.Surjective (cubeMap r) := by
      intro x
      obtain ⟨q, C, u, _, he⟩ := cubeMap_positive_rep r x
      exact ⟨orderedChart q C u, he⟩
    have ordered_predicate_sum_zero (V : Type) [PartialOrder V] [Fintype V]
        (w : OrderedRealization V) (P : V → Prop) [decP : DecidablePred P] :
        (∑ v, if P v then w.1 v else 0) = 0 ↔ ∀ v, 0 < w.1 v → ¬ P v := by
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun v _ =>
        show 0 ≤ (if P v then w.1 v else 0) from by
          split_ifs <;> first | exact ordered_nonneg V w v | exact le_rfl)]
      constructor
      · intro h v hv hP
        have hz := h v (Finset.mem_univ v)
        rw [if_pos hP] at hz
        exact (ne_of_gt hv) hz
      · intro h v _
        by_cases hP : P v
        · rw [if_pos hP]
          exact ordered_zero_of_not_pos V w v (fun hv => h v hv hP)
        · exact if_neg hP
    have cubeMap_zero_iff (r : ℕ) (w : OrderedRealization (Finset (Fin r))) (i : Fin r) :
        (cubeMap r w i : ℝ) = 0 ↔ ∀ S, 0 < w.1 S → i ∉ S :=
      ordered_predicate_sum_zero (Finset (Fin r)) w (fun S => i ∈ S)
        (decP := fun S => inferInstanceAs (Decidable (i ∈ S)))
    have cubeMap_one_iff (r : ℕ) (w : OrderedRealization (Finset (Fin r))) (i : Fin r) :
        (cubeMap r w i : ℝ) = 1 ↔ ∀ S, 0 < w.1 S → i ∈ S := by
      let z : ℝ := ∑ S : Finset (Fin r), if i ∉ S then w.1 S else 0
      have hsum : (cubeMap r w i : ℝ) + z = 1 := by
        change (∑ S : Finset (Fin r), if i ∈ S then w.1 S else 0) +
          (∑ S : Finset (Fin r), if i ∉ S then w.1 S else 0) = 1
        rw [← Finset.sum_add_distrib]
        calc
          (∑ S : Finset (Fin r), ((if i ∈ S then w.1 S else 0) +
            (if i ∉ S then w.1 S else 0))) = ∑ S : Finset (Fin r), w.1 S := by
              apply Finset.sum_congr rfl
              intro S _
              by_cases hi : i ∈ S <;> simp [hi]
          _ = 1 := ordered_total_weight (Finset (Fin r)) w
      have hz : z = 0 ↔ ∀ S, 0 < w.1 S → i ∈ S := by
        simpa only [not_not] using ordered_predicate_sum_zero (Finset (Fin r)) w (fun S => i ∉ S)
          (decP := fun S => inferInstanceAs (Decidable (i ∉ S)))
      constructor
      · intro h
        apply hz.mp
        linarith
      · intro h
        have hh := hz.mpr h
        linarith
    have cubeMap_boundary_iff (r : ℕ) (w : OrderedRealization (Finset (Fin r))) :
        cubeMap r w ∈ Cube.boundary (Fin r) ↔
          ∃ i : Fin r, (∀ S, 0 < w.1 S → i ∉ S) ∨ (∀ S, 0 < w.1 S → i ∈ S) := by
      change (∃ i, cubeMap r w i = 0 ∨ cubeMap r w i = 1) ↔ _
      constructor
      · rintro ⟨i, hi | hi⟩
        · exact ⟨i, Or.inl ((cubeMap_zero_iff r w i).mp (congrArg Subtype.val hi))⟩
        · exact ⟨i, Or.inr ((cubeMap_one_iff r w i).mp (congrArg Subtype.val hi))⟩
      · rintro ⟨i, hi | hi⟩
        · exact ⟨i, Or.inl (Subtype.ext ((cubeMap_zero_iff r w i).mpr hi))⟩
        · exact ⟨i, Or.inr (Subtype.ext ((cubeMap_one_iff r w i).mpr hi))⟩
    -- A6/C2: uniqueness of a positive staircase-cube representation.
    -- Embed a cube vertex S into the nonempty simplex face {0} ∪ succ(S).
    -- Fin.cases avoids any separate image/cardinality bookkeeping.
    let cubeLiftFace (r : ℕ) (S : Finset (Fin r)) : Face r :=
      ⟨Finset.univ.filter (fun j => Fin.cases True (fun i : Fin r => i ∈ S) j), by
        refine ⟨0, ?_⟩
        simp⟩
    have cubeLiftFace_zero (r : ℕ) (S : Finset (Fin r)) :
        (0 : Fin (r + 1)) ∈ (cubeLiftFace r S).1 := by
      simp [cubeLiftFace]
    have cubeLiftFace_succ (r : ℕ) (S : Finset (Fin r)) (i : Fin r) :
        i.succ ∈ (cubeLiftFace r S).1 ↔ i ∈ S := by
      simp [cubeLiftFace]
    have cubeLiftFace_injective (r : ℕ) : Function.Injective (cubeLiftFace r) := by
      intro S T he
      ext i
      rw [← cubeLiftFace_succ r S i, he, cubeLiftFace_succ r T i]
    have cubeLiftFace_strict (r : ℕ) (S T : Finset (Fin r)) (hST : S ⊂ T) :
        (cubeLiftFace r S).1 ⊂ (cubeLiftFace r T).1 := by
      have hsub : (cubeLiftFace r S).1 ⊆ (cubeLiftFace r T).1 := by
        intro a
        refine Fin.cases ?_ (fun i => ?_) a
        · intro _
          exact cubeLiftFace_zero r T
        · intro hi
          exact (cubeLiftFace_succ r T i).mpr (hST.1 ((cubeLiftFace_succ r S i).mp hi))
      apply (Finset.ssubset_iff_of_subset hsub).mpr
      obtain ⟨i, hiT, hiS⟩ := Finset.exists_of_ssubset hST
      exact ⟨i.succ, (cubeLiftFace_succ r T i).mpr hiT,
        fun hi => hiS ((cubeLiftFace_succ r S i).mp hi)⟩

    -- Normalize the lifted face chain. The common point is (1,x)/(1+Σx).
    -- No order assumption on C is needed for this algebraic normalization.
    have cube_chain_normalize (r q : ℕ) (C : Fin (q + 1) → Finset (Fin r))
        (u : Simplex q) (hu : ∀ j, 0 < u.1 j)
        (x : Fin r → ℝ) (hx : ∀ i, 0 ≤ x i)
        (hcoord : ∀ i, (∑ j, if i ∈ C j then u.1 j else 0) = x i) :
        ∃ w : Simplex q,
          (∀ j, 0 < w.1 j) ∧
          (∀ j, w.1 j = ((cubeLiftFace r (C j)).1.card : ℝ) * u.1 j /
            (1 + ∑ i, x i)) ∧
          (∀ a : Fin (r + 1),
            (chainBary r q (fun j => cubeLiftFace r (C j)) w).1 a =
              Fin.cases (1 / (1 + ∑ i, x i)) (fun i => x i / (1 + ∑ i, x i)) a) := by
      classical
      let den : ℝ := 1 + ∑ i, x i
      have hden : 0 < den := by
        have hs : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx i)
        dsimp only [den]
        linarith
      have hden0 : den ≠ 0 := ne_of_gt hden
      let weights : Fin (q + 1) → ℝ :=
        fun j => ((cubeLiftFace r (C j)).1.card : ℝ) * u.1 j / den
      have hcard (j : Fin (q + 1)) : 0 < ((cubeLiftFace r (C j)).1.card : ℝ) :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr (cubeLiftFace r (C j)).2)
      have hpos (j : Fin (q + 1)) : 0 < weights j :=
        div_pos (mul_pos (hcard j) (hu j)) hden
      have hterm (j : Fin (q + 1)) (a : Fin (r + 1)) :
          weights j * (barycenter r (cubeLiftFace r (C j))).1 a =
            (if a ∈ (cubeLiftFace r (C j)).1 then u.1 j else 0) / den := by
        change (((cubeLiftFace r (C j)).1.card : ℝ) * u.1 j / den) *
            (if a ∈ (cubeLiftFace r (C j)).1 then
              (((cubeLiftFace r (C j)).1.card : ℝ))⁻¹ else 0) = _
        by_cases ha : a ∈ (cubeLiftFace r (C j)).1
        · rw [if_pos ha, if_pos ha]
          have hc0 := ne_of_gt (hcard j)
          field_simp [hc0, hden0] <;> ring
        · rw [if_neg ha, if_neg ha]
          simp
      have hpoint (a : Fin (r + 1)) :
          (∑ j, weights j * (barycenter r (cubeLiftFace r (C j))).1 a) =
            Fin.cases (1 / den) (fun i => x i / den) a := by
        refine Fin.cases ?_ (fun i => ?_) a
        · simp_rw [hterm, cubeLiftFace_zero, if_true]
          simp only [div_eq_mul_inv, ← Finset.sum_mul, u.2.2, Fin.cases_zero]
        · simp_rw [hterm, cubeLiftFace_succ]
          simp only [div_eq_mul_inv, ← Finset.sum_mul, hcoord i, Fin.cases_succ]
      have hsum : (∑ j, weights j) = 1 := by
        calc
          (∑ j, weights j) =
              ∑ j, ∑ a, weights j * (barycenter r (cubeLiftFace r (C j))).1 a := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.mul_sum, (barycenter r (cubeLiftFace r (C j))).2.2, mul_one]
          _ = ∑ a, ∑ j, weights j * (barycenter r (cubeLiftFace r (C j))).1 a :=
            Finset.sum_comm
          _ = ∑ a : Fin (r + 1), Fin.cases (1 / den) (fun i => x i / den) a := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hpoint a
          _ = 1 / den + ∑ i : Fin r, x i / den := by
            rw [Fin.sum_univ_succ]
            rfl
          _ = (1 + ∑ i, x i) / den := by
            simp only [div_eq_mul_inv, ← Finset.sum_mul, add_mul]
          _ = 1 := div_self hden0
      let w : Simplex q := ⟨weights, ⟨fun j => (hpos j).le, hsum⟩⟩
      refine ⟨w, hpos, (fun _ => rfl), ?_⟩
      intro a
      exact hpoint a

    -- Raw coordinate equality is deliberately the only cube interface required.
    -- cubeMap_chart can translate equality of actual cubeMap values into hcoord.
    have cube_chain_positive_unique (r p q : ℕ)
        (C : Fin (p + 1) ↪o Finset (Fin r)) (D : Fin (q + 1) ↪o Finset (Fin r))
        (u : Simplex p) (v : Simplex q)
        (hu : ∀ j, 0 < u.1 j) (hv : ∀ j, 0 < v.1 j)
        (hcoord : ∀ i : Fin r,
          (∑ j, if i ∈ C j then u.1 j else 0) =
            ∑ j, if i ∈ D j then v.1 j else 0) :
        (⟨p, (C, u)⟩ : Σ k, (Fin (k + 1) ↪o Finset (Fin r)) × Simplex k) =
          ⟨q, (D, v)⟩ := by
      classical
      let x : Fin r → ℝ := fun i => ∑ j, if i ∈ C j then u.1 j else 0
      have hx (i : Fin r) : 0 ≤ x i := by
        apply Finset.sum_nonneg
        intro j hj
        split_ifs
        · exact u.2.1 j
        · exact le_rfl
      obtain ⟨w, hwpos, hw, hpointC⟩ :=
        cube_chain_normalize r p C u hu x hx (fun _ => rfl)
      obtain ⟨z, hzpos, hz, hpointD⟩ :=
        cube_chain_normalize r q D v hv x hx (fun i => (hcoord i).symm)
      have hC : ∀ i j, i < j →
          (cubeLiftFace r (C i)).1 ⊂ (cubeLiftFace r (C j)).1 :=
        fun i j hij => cubeLiftFace_strict r (C i) (C j) (C.strictMono hij)
      have hD : ∀ i j, i < j →
          (cubeLiftFace r (D i)).1 ⊂ (cubeLiftFace r (D j)).1 :=
        fun i j hij => cubeLiftFace_strict r (D i) (D j) (D.strictMono hij)
      have he : chainBary r p (fun j => cubeLiftFace r (C j)) w =
          chainBary r q (fun j => cubeLiftFace r (D j)) z := by
        apply Subtype.ext
        funext a
        exact (hpointC a).trans (hpointD a).symm
      have hchain := chainBary_positive_unique r p q
        (fun j => cubeLiftFace r (C j)) (fun j => cubeLiftFace r (D j))
        hC hD w z hwpos hzpos he
      have hpq : p = q := congrArg Sigma.fst hchain
      subst q
      have hpairs : ((fun j => cubeLiftFace r (C j)), w) =
          ((fun j => cubeLiftFace r (D j)), z) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hchain).2
      have hCD : C = D := by
        apply DFunLike.ext
        intro j
        exact cubeLiftFace_injective r (congrFun (congrArg Prod.fst hpairs) j)
      have hwz : w = z := congrArg Prod.snd hpairs
      subst D
      have hden : (1 + ∑ i, x i : ℝ) ≠ 0 := by
        have hs : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx i)
        linarith
      have huv : u = v := by
        apply Subtype.ext
        funext j
        have hscaled :
            ((cubeLiftFace r (C j)).1.card : ℝ) * u.1 j / (1 + ∑ i, x i) =
              ((cubeLiftFace r (C j)).1.card : ℝ) * v.1 j / (1 + ∑ i, x i) :=
          (hw j).symm.trans ((congrArg (fun a : Simplex p => a.1 j) hwz).trans (hz j))
        have hscaled' : ((cubeLiftFace r (C j)).1.card : ℝ) * u.1 j =
            ((cubeLiftFace r (C j)).1.card : ℝ) * v.1 j := by
          simpa only [div_mul_cancel₀ _ hden] using
            congrArg (fun a : ℝ => a * (1 + ∑ i, x i)) hscaled
        exact mul_left_cancel₀
          (ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr (cubeLiftFace r (C j)).2))) hscaled'
      subst v
      rfl
    have cubeMap_injective (r : ℕ) : Function.Injective (cubeMap r) := by
      intro w z he
      obtain ⟨p, C, u, hu, hw⟩ := ordered_positive_rep (Finset (Fin r)) w
      obtain ⟨q, D, v, hv, hz⟩ := ordered_positive_rep (Finset (Fin r)) z
      have hcoord (i : Fin r) :
          (∑ j, if i ∈ C j then u.1 j else 0) = ∑ j, if i ∈ D j then v.1 j else 0 := by
        calc
          (∑ j, if i ∈ C j then u.1 j else 0) =
              (cubeMap r (orderedChart p C u) i : ℝ) := (cubeMap_chart r p C u i).symm
          _ = (cubeMap r (orderedChart q D v) i : ℝ) := by rw [hw, hz, he]
          _ = ∑ j, if i ∈ D j then v.1 j else 0 := cubeMap_chart r q D v i
      have hpairs := cube_chain_positive_unique r p q C D u v hu hv hcoord
      have hpq : p = q := congrArg Sigma.fst hpairs
      subst q
      have hpair : (C, u) = (D, v) := eq_of_heq (Sigma.mk.inj_iff.mp hpairs).2
      have hC : C = D := congrArg Prod.fst hpair
      have hu' : u = v := congrArg Prod.snd hpair
      rw [← hw, ← hz, hC, hu']
    let cubeHomeomorph (r : ℕ) : OrderedRealization (Finset (Fin r)) ≃ₜ (Fin r → I) :=
      Continuous.homeoOfEquivCompactToT2
        (f := Equiv.ofBijective (cubeMap r) ⟨cubeMap_injective r, cubeMap_surjective r⟩)
        (cubeMap r).continuous
    have cubeHomeomorph_apply (r : ℕ) (w : OrderedRealization (Finset (Fin r))) :
        cubeHomeomorph r w = cubeMap r w := rfl
    -- A6/C2/T8: the cube boundary becomes a full subcomplex after one subdivision.
    -- A face lies in the boundary when ONE coordinate is constant on ALL its vertices.
    let cubeBoundaryFace (r : ℕ) (S : OrderedFace (Finset (Fin r))) : Prop :=
      ∃ i : Fin r, (∀ T ∈ S.1, i ∉ T) ∨ (∀ T ∈ S.1, i ∈ T)

    have cubeBoundaryFace_of_le (r : ℕ) (S T : OrderedFace (Finset (Fin r)))
        (hST : S ≤ T) (hT : cubeBoundaryFace r T) : cubeBoundaryFace r S := by
      rcases hT with ⟨i, hi | hi⟩
      · exact ⟨i, Or.inl (fun U hU => hi U (hST hU))⟩
      · exact ⟨i, Or.inr (fun U hU => hi U (hST hU))⟩

    -- Strictly positive chart weights identify the support with the largest face.
    -- This retains the union of all coordinate faces, including r = 0.
    have cubeMap_sdChart_boundary_iff (r q : ℕ)
        (C : Fin (q + 1) ↪o OrderedFace (Finset (Fin r))) (u : Simplex q)
        (hu : ∀ j, 0 < u.1 j) :
        cubeMap r (sdChart C u) ∈ Cube.boundary (Fin r) ↔
          cubeBoundaryFace r (C (Fin.last q)) := by
      rw [cubeMap_boundary_iff]
      constructor
      · rintro ⟨i, hi | hi⟩
        · refine ⟨i, Or.inl ?_⟩
          intro T hT
          exact hi T ((sdChart_positive_iff C u hu T).mpr hT)
        · refine ⟨i, Or.inr ?_⟩
          intro T hT
          exact hi T ((sdChart_positive_iff C u hu T).mpr hT)
      · rintro ⟨i, hi | hi⟩
        · refine ⟨i, Or.inl ?_⟩
          intro T hT
          exact hi T ((sdChart_positive_iff C u hu T).mp hT)
        · refine ⟨i, Or.inr ?_⟩
          intro T hT
          exact hi T ((sdChart_positive_iff C u hu T).mp hT)

    have cubeSubdivision_boundary_iff (r : ℕ)
        (w : OrderedRealization (OrderedFace (Finset (Fin r)))) :
        cubeHomeomorph r (orderedSubdivisionHomeomorph (Finset (Fin r)) w)
            ∈ Cube.boundary (Fin r) ↔
          ∀ S, 0 < w.1 S → cubeBoundaryFace r S := by
      obtain ⟨q, C, u, hu, hw⟩ := ordered_positive_rep (OrderedFace (Finset (Fin r))) w
      rw [← hw, orderedSubdivisionHomeomorph_chart (Finset (Fin r)) q C u,
        cubeHomeomorph_apply, cubeMap_sdChart_boundary_iff r q C u hu]
      constructor
      · intro hlast S hS
        change 0 < chainWeight q C u S at hS
        obtain ⟨j, rfl⟩ := (chainWeight_positive_iff q C C.injective u hu S).mp hS
        exact cubeBoundaryFace_of_le r (C j) (C (Fin.last q))
          (C.monotone (Fin.le_last j)) hlast
      · intro h
        apply h (C (Fin.last q))
        change 0 < chainWeight q C u (C (Fin.last q))
        rw [chainWeight_image q C C.injective u (Fin.last q)]
        exact hu (Fin.last q)

    -- The reverse implication above uses the positive largest face itself.
    -- It does not exchange ∀ S, ∃ i with ∃ i, ∀ S; the chain supplies one common
    -- coordinate through its largest face, and downward closure handles the rest.

    -- T8: full subcomplexes stay full under the specified iterated subdivisions.
    let sdPredicate (V : Type) [PartialOrder V] [Fintype V] (P : V → Prop) :
        (k : ℕ) → sdVertices V k → Prop :=
      Nat.rec (motive := fun k => sdVertices V k → Prop) P
        (fun _ Q S => ∀ v ∈ S.1, Q v)
    have sdHomeomorph_full (V : Type) [PartialOrder V] [Fintype V] (P : V → Prop)
        (k : ℕ) (w : OrderedRealization (sdVertices V k)) :
        (∀ v, 0 < (sdHomeomorph V k w).1 v → P v) ↔
          (∀ S, 0 < w.1 S → sdPredicate V P k S) := by
      induction k with
      | zero => rfl
      | succ k ih =>
          change (∀ v, 0 < (sdHomeomorph V k
            (orderedSubdivisionHomeomorph (sdVertices V k) w)).1 v → P v) ↔ _
          rw [ih]
          exact orderedSubdivisionHomeomorph_full (sdVertices V k) (sdPredicate V P k) w
    let cubeTriHomeomorph (r k : ℕ) :
        OrderedRealization (sdVertices (OrderedFace (Finset (Fin r))) k) ≃ₜ (Fin r → I) :=
      ((sdHomeomorph (OrderedFace (Finset (Fin r))) k).trans
        (orderedSubdivisionHomeomorph (Finset (Fin r)))).trans (cubeHomeomorph r)
    let cubeBoundaryVertex (r k : ℕ) :
        sdVertices (OrderedFace (Finset (Fin r))) k → Prop :=
      sdPredicate (OrderedFace (Finset (Fin r))) (cubeBoundaryFace r) k
    have cubeTri_boundary_iff (r k : ℕ)
        (w : OrderedRealization (sdVertices (OrderedFace (Finset (Fin r))) k)) :
        cubeTriHomeomorph r k w ∈ Cube.boundary (Fin r) ↔
          ∀ v, 0 < w.1 v → cubeBoundaryVertex r k v := by
      change cubeHomeomorph r (orderedSubdivisionHomeomorph (Finset (Fin r))
        (sdHomeomorph (OrderedFace (Finset (Fin r))) k w)) ∈ Cube.boundary (Fin r) ↔ _
      rw [cubeSubdivision_boundary_iff]
      exact sdHomeomorph_full (OrderedFace (Finset (Fin r))) (cubeBoundaryFace r) k w
    have cubeTri_vertex_boundary (r k : ℕ)
        (v : sdVertices (OrderedFace (Finset (Fin r))) k) :
        cubeTriHomeomorph r k (orderedVertex _ v) ∈ Cube.boundary (Fin r) ↔
          cubeBoundaryVertex r k v := by
      rw [cubeTri_boundary_iff]
      constructor
      · intro h
        exact h v ((orderedVertex_positive _ v v).mpr rfl)
      · intro h b hb
        have he := (orderedVertex_positive _ v b).mp hb
        exact he ▸ h

    -- T7 and T8 together: all continuous maps from finite ordered realizations
    -- admit this approximation inside one finite subcomplex of the actual fat level.
    have fat_ordered_approximation (n : ℕ) (V : Type) [PartialOrder V] [Fintype V]
        (f : C(OrderedRealization V, fatLevel n)) :
        ∃ W : Finset (AllCell2 n),
        ∃ k : ℕ, ∃ a : sdVertices V k → {v : AllCell2 n // v ∈ W},
        ∃ g : C(OrderedRealization (sdVertices V k),
          OrderedRealization {v : AllCell2 n // v ∈ W}),
        ∃ H : C(I × OrderedRealization (sdVertices V k), fatLevel n),
          (∀ v w, v ≤ w ∨ w ≤ v → a v ≤ a w ∨ a w ≤ a v) ∧
          (∀ x b, (g x).1 b = ∑ v, if a v = b then x.1 v else 0) ∧
          (∀ x, H (0, x) = f (sdHomeomorph V k x)) ∧
          (∀ x, H (1, x) = finiteThirdMap n W (g x)) ∧
          (∀ t x, f (sdHomeomorph V k x) ∈ Set.range (zeroIncl n) →
            H (t, x) ∈ Set.range (zeroIncl n)) ∧
          (∀ v, f (sdHomeomorph V k (orderedVertex _ v)) ∈ Set.range (zeroIncl n) →
            zeroCell2 (a v).1.2) := by
      letI : CompactSpace (OrderedRealization V) := orderedRealization_compact V
      obtain ⟨W, f', hf'⟩ := compact_map_finite_factor n (OrderedRealization V) f
      obtain ⟨k, a, g, H, hstar, hg, h0, h1, hsupport⟩ :=
        ordered_star_approximation V {v : AllCell2 n // v ∈ W} f'
      let j : C(OrderedRealization {v : AllCell2 n // v ∈ W}, fatLevel n) :=
        ⟨finiteThirdMap n W, (finiteThirdMap_isClosedEmbedding n W).continuous⟩
      refine ⟨W, k, a, g, j.comp H, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ordered_star_comparable (sdVertices V k) {v : AllCell2 n // v ∈ W}
          (f'.comp ⟨sdHomeomorph V k, (sdHomeomorph V k).continuous⟩) a hstar
      · intro x b
        rw [hg]
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : a v = b <;> simp only [h, if_true, if_false]
      · intro x
        change finiteThirdMap n W (H (0, x)) = _
        rw [h0, hf']
      · intro x
        change finiteThirdMap n W (H (1, x)) = _
        rw [h1]
      · intro t x hx
        apply (finiteThirdMap_zero_iff n W (H (t, x))).mpr
        have hfzero := (finiteThirdMap_zero_iff n W (f' (sdHomeomorph V k x))).mp
          ((hf' (sdHomeomorph V k x)).symm ▸ hx)
        intro b hb
        exact hfzero b (hsupport t x b hb)
      · intro v hv
        have hfzero := (finiteThirdMap_zero_iff n W
          (f' (sdHomeomorph V k (orderedVertex _ v)))).mp
          ((hf' (sdHomeomorph V k (orderedVertex _ v))).symm ▸ hv)
        exact hfzero (a v) (hstar v (orderedVertex _ v)
          ((orderedVertex_positive _ v v).mpr rfl))
    have fat_cube_approximation (n r : ℕ) (f : C((Fin r → I), fatLevel n))
        (hf : ∀ x ∈ Cube.boundary (Fin r), f x ∈ Set.range (zeroIncl n)) :
        ∃ W : Finset (AllCell2 n),
        ∃ k : ℕ, ∃ a : sdVertices (OrderedFace (Finset (Fin r))) k →
          {v : AllCell2 n // v ∈ W},
        ∃ g : C(OrderedRealization (sdVertices (OrderedFace (Finset (Fin r))) k),
          OrderedRealization {v : AllCell2 n // v ∈ W}),
        ∃ H : C(I × OrderedRealization (sdVertices (OrderedFace (Finset (Fin r))) k),
          fatLevel n),
          (∀ v w, v ≤ w ∨ w ≤ v → a v ≤ a w ∨ a w ≤ a v) ∧
          (∀ x b, (g x).1 b = ∑ v, if a v = b then x.1 v else 0) ∧
          (∀ x, H (0, x) = f (cubeTriHomeomorph r k x)) ∧
          (∀ x, H (1, x) = finiteThirdMap n W (g x)) ∧
          (∀ t x, cubeTriHomeomorph r k x ∈ Cube.boundary (Fin r) →
            H (t, x) ∈ Set.range (zeroIncl n)) ∧
          (∀ v, cubeBoundaryVertex r k v → zeroCell2 (a v).1.2) := by
      let e := (orderedSubdivisionHomeomorph (Finset (Fin r))).trans (cubeHomeomorph r)
      obtain ⟨W, k, a, g, H, ha, hg, h0, h1, hzero, hvertex⟩ :=
        fat_ordered_approximation n (OrderedFace (Finset (Fin r)))
          (f.comp ⟨e, e.continuous⟩)
      refine ⟨W, k, a, g, H, ha, hg, h0, h1, ?_, ?_⟩
      · intro t x hx
        exact hzero t x (hf _ hx)
      · intro v hv
        exact hvertex v (hf _ ((cubeTri_vertex_boundary r k v).mpr hv))

    -- B1: a characteristic ball for the simplex prism.
    -- This map is not claimed to be injective on the boundary.
    let PrismBoundary (q : ℕ) : Set (Simplex q × I) :=
      {z | (∃ i : Fin (q + 1), z.1.1 i = 0) ∨ z.2 = 0 ∨ z.2 = 1}
    have ball_prism_data (q : ℕ) :
        ∃ f : C(Metric.closedBall (0 : Fin (q + 1) → ℝ) 1, Simplex q × I),
          Function.Surjective f ∧
          (∀ x : Metric.closedBall (0 : Fin (q + 1) → ℝ) 1,
            x.1 ∈ Metric.sphere 0 1 ↔ f x ∈ PrismBoundary q) ∧
          (∀ x y, f x = f y → f x ∉ PrismBoundary q → x = y) := by
      have htail : Continuous
          (fun x : Metric.closedBall (0 : Fin (q + 1) → ℝ) 1 =>
            fun i : Fin q => ballCube (q + 1) x i.succ) :=
        continuous_pi (fun i => (continuous_apply i.succ).comp (ballCube (q + 1)).continuous)
      have hhead : Continuous
          (fun x : Metric.closedBall (0 : Fin (q + 1) → ℝ) 1 =>
            ballCube (q + 1) x 0) :=
        (continuous_apply 0).comp (ballCube (q + 1)).continuous
      let f : C(Metric.closedBall (0 : Fin (q + 1) → ℝ) 1, Simplex q × I) :=
        ⟨fun x => (stick q (fun i => ballCube (q + 1) x i.succ), ballCube (q + 1) x 0),
          ((stick_continuous q).comp htail).prodMk hhead⟩
      have hsurj : Function.Surjective f := by
        rintro ⟨u, t⟩
        obtain ⟨v, hv⟩ := stick_surjective q u
        refine ⟨(ballCube (q + 1)).symm (Fin.cons t v), ?_⟩
        change (stick q (fun i =>
            ballCube (q + 1) ((ballCube (q + 1)).symm (Fin.cons t v)) i.succ),
          ballCube (q + 1) ((ballCube (q + 1)).symm (Fin.cons t v)) 0) = (u, t)
        rw [(ballCube (q + 1)).apply_symm_apply]
        simp only [Fin.cons_succ, Fin.cons_zero, hv]
      have hpositive (x : Metric.closedBall (0 : Fin (q + 1) → ℝ) 1) :
          x.1 ∈ Metric.ball 0 1 ↔
            (∀ i, 0 < (f x).1.1 i) ∧
              0 < ((f x).2 : ℝ) ∧ ((f x).2 : ℝ) < 1 := by
        rw [ballCube_interior (q + 1) x]
        constructor
        · intro h
          refine ⟨?_, (h 0).1, (h 0).2⟩
          exact (stick_positive q (fun i => ballCube (q + 1) x i.succ)).mpr
            (fun i => h i.succ)
        · rintro ⟨hs, h0, h1⟩
          have ht := (stick_positive q (fun i => ballCube (q + 1) x i.succ)).mp hs
          intro i
          exact Fin.cases ⟨h0, h1⟩ (fun j => ht j) i
      have hboundary (x : Metric.closedBall (0 : Fin (q + 1) → ℝ) 1) :
          x.1 ∈ Metric.sphere 0 1 ↔ f x ∈ PrismBoundary q := by
        rw [← Metric.closedBall_sdiff_ball]
        constructor
        · intro hx
          by_contra hb
          apply hx.2
          apply (hpositive x).mpr
          have hs : ∀ i, 0 < (f x).1.1 i := by
            intro i
            apply lt_of_le_of_ne ((f x).1.2.1 i)
            intro he
            exact hb (Or.inl ⟨i, he.symm⟩)
          have h0 : 0 < ((f x).2 : ℝ) := by
            apply lt_of_le_of_ne (f x).2.property.1
            intro he
            exact hb (Or.inr (Or.inl (Subtype.ext he.symm)))
          have h1 : ((f x).2 : ℝ) < 1 := by
            apply lt_of_le_of_ne (f x).2.property.2
            intro he
            exact hb (Or.inr (Or.inr (Subtype.ext he)))
          exact ⟨hs, h0, h1⟩
        · intro hx
          refine ⟨x.2, ?_⟩
          intro hxball
          obtain ⟨hs, h0, h1⟩ := (hpositive x).mp hxball
          rcases hx with ⟨i, hi⟩ | ht | ht
          · have h := hs i
            rw [hi] at h
            exact (lt_irrefl 0) h
          · have ht' : ((f x).2 : ℝ) = 0 := congrArg Subtype.val ht
            rw [ht'] at h0
            exact (lt_irrefl 0) h0
          · have ht' : ((f x).2 : ℝ) = 1 := congrArg Subtype.val ht
            rw [ht'] at h1
            exact (lt_irrefl 1) h1
      have hinj : Set.InjOn f
          {x : Metric.closedBall (0 : Fin (q + 1) → ℝ) 1 | x.1 ∈ Metric.ball 0 1} := by
        intro x hx y hy he
        have hxt := (ballCube_interior (q + 1) x).mp hx
        have hyt := (ballCube_interior (q + 1) y).mp hy
        have htailEq : (fun i : Fin q => ballCube (q + 1) x i.succ) =
            (fun i : Fin q => ballCube (q + 1) y i.succ) :=
          stick_injective_interior q (fun i => hxt i.succ) (fun i => hyt i.succ)
            (congrArg Prod.fst he)
        have hheadEq : ballCube (q + 1) x 0 = ballCube (q + 1) y 0 :=
          congrArg Prod.snd he
        apply (ballCube (q + 1)).injective
        funext i
        exact Fin.cases hheadEq (fun j => congrFun htailEq j) i
      have hball (x : Metric.closedBall (0 : Fin (q + 1) → ℝ) 1)
          (hx : f x ∉ PrismBoundary q) : x.1 ∈ Metric.ball 0 1 := by
        by_contra hn
        apply hx
        apply (hboundary x).mp
        rw [← Metric.closedBall_sdiff_ball]
        exact ⟨x.2, hn⟩
      refine ⟨f, hsurj, hboundary, ?_⟩
      intro x y he hx
      have hy : f y ∉ PrismBoundary q := by
        rw [← he]
        exact hx
      exact hinj (hball x hx) (hball y hy) he

    have realization_data :
        ∃ e : ∀ n, HomotopyGroup (Fin n) (level n) (level n).point ≃ ZMod 2,
          e 0 = pi0Coordinates ∧
          (∀ n, e n ⟦GenLoop.const⟧ = 0) ∧
          (∀ n (p : GenLoop (Fin n) (level n) (level n).point),
            e (n + 1) ⟦Prespectrum.stabilizeLoop cocycleSpectrum n n p⟧ = e n ⟦p⟧) ∧
          (∀ n r, r + 1 ≠ n →
            Subsingleton (HomotopyGroup (Fin (r + 1)) (level n) (level n).point)) := by
      -- A3–A8, A10–A11, T1 subdivisions, T8–T9, B1–B4 and C2–C3: classify continuous cubes
      -- for the fixed cocycle spectrum, preserving zero and stabilization.
      sorry
    obtain ⟨e, he0, hzero, hstab, hvan⟩ := realization_data
    refine ⟨cocycleSpectrum, level_good, e, hzero, hstab,
      fun n p q => coordinates_add n (e (n + 1)) (hzero (n + 1)) p q, ?_⟩
    intro n r hr
    cases r with
    | zero => exact pi0_vanish n (Nat.pos_of_ne_zero (Ne.symm hr))
    | succ r => exact hvan n r hr
  obtain ⟨E, hgood, e, hzero, hstab, hadd, hvan⟩ := layer_data
  -- D1.2: iterated stabilization preserves the actual relation quotient.
  let raise {d : ℤ} (a : Prespectrum.Representative E d) :
      ℕ → Prespectrum.Representative E d := Nat.rec a (fun _ b => b.next)
  have raise_stage {d : ℤ} (a : Prespectrum.Representative E d) (k : ℕ) :
      (raise a k).stage = a.stage + k := by
    induction k with
    | zero => rfl
    | succ k ih => exact congrArg (· + 1) ih
  have raise_class {d : ℤ} (a : Prespectrum.Representative E d) (k : ℕ) :
      (Quot.mk _ (raise a k) : Prespectrum.StableHomotopy E d) = Quot.mk _ a := by
    induction k with
    | zero => rfl
    | succ k ih =>
      exact (Quot.sound (Prespectrum.StableRelation.stabilization (raise a k))).symm.trans ih
  -- C2 also supplies the stage-zero coordinate; this removes the S11 case split.
  let zeroLoop (a : Prespectrum.Representative E 0) :
      GenLoop (Fin a.stage) (E.level a.stage) (E.level a.stage).point := by
    have h : a.dimension = a.stage := by have := a.degree; omega
    exact h ▸ a.loop
  let coordinate (a : Prespectrum.Representative E 0) : ZMod 2 :=
    e a.stage ⟦zeroLoop a⟧
  -- D2.1: both kinds of generators preserve the coordinate.
  have coordinate_relation {a b : Prespectrum.Representative E 0}
      (h : Prespectrum.StableRelation E 0 a b) : coordinate a = coordinate b := by
    cases h with
    | homotopy p h =>
      obtain ⟨n, r, hr, q⟩ := a
      have hn : r = n := by omega
      subst r
      exact congrArg (e n) (Quotient.sound h)
    | stabilization =>
      obtain ⟨n, r, hr, q⟩ := a
      have hn : r = n := by omega
      subst r
      exact (hstab n q).symm
  let pi : Prespectrum.StableHomotopy E 0 → ZMod 2 :=
    Quot.lift coordinate (fun _ _ h => coordinate_relation h)
  have pi_loop (n : ℕ) (p : GenLoop (Fin n) (E.level n) (E.level n).point) :
      pi (Prespectrum.loopClass E 0 n n (by omega) p) = e n ⟦p⟧ := rfl
  have equal_at_stage (a b : Prespectrum.Representative E 0)
      (hs : a.stage = b.stage) (he : coordinate a = coordinate b) :
      (Quot.mk _ a : Prespectrum.StableHomotopy E 0) = Quot.mk _ b := by
    obtain ⟨n, r, hr, p⟩ := a
    obtain ⟨m, s, hs', q⟩ := b
    change n = m at hs
    subst m
    have hrn : r = n := by omega
    have hsn : s = n := by omega
    subst r
    subst s
    have hpq : GenLoop.Homotopic p q := Quotient.exact ((e n).injective he)
    exact Quot.sound (Prespectrum.StableRelation.homotopy ⟨n, n, hr, p⟩ q hpq)
  have pi_bijective : Function.Bijective pi := by
    constructor
    · -- D2.3: use n + m as a common stage instead of max(n,m).
      intro x y hxy
      induction x using Quot.inductionOn with | h a
      induction y using Quot.inductionOn with | h b
      let a' := raise a b.stage
      let b' := raise b a.stage
      have ha : (Quot.mk _ a' : Prespectrum.StableHomotopy E 0) = Quot.mk _ a :=
        raise_class a b.stage
      have hb : (Quot.mk _ b' : Prespectrum.StableHomotopy E 0) = Quot.mk _ b :=
        raise_class b a.stage
      have he : coordinate a' = coordinate b' :=
        (congrArg pi ha).trans (hxy.trans (congrArg pi hb).symm)
      exact ha.symm.trans ((equal_at_stage a' b'
        (by dsimp only [a', b']; rw [raise_stage, raise_stage, Nat.add_comm]) he).trans hb)
    · -- D2.2: C2 gives representatives already at stage zero.
      intro z
      obtain ⟨p, hp⟩ := (e 0).surjective z
      induction p using Quotient.inductionOn with | h p
      refine ⟨Prespectrum.loopClass E 0 0 0 (by omega) p, ?_⟩
      rw [pi_loop]
      exact hp
  -- D2.6: the degree equation is used over integers, including negative degrees.
  have vanishes (d : ℤ) (hd : d ≠ 0) : Subsingleton (Prespectrum.StableHomotopy E d) := by
    have same_stage (a b : Prespectrum.Representative E d) (hs : a.stage = b.stage) :
        (Quot.mk _ a : Prespectrum.StableHomotopy E d) = Quot.mk _ b := by
      obtain ⟨n, r, hr, p⟩ := a
      obtain ⟨m, s, hs', q⟩ := b
      change n = m at hs
      subst m
      have hrs : r = s := by omega
      subst s
      have hrn : r ≠ n := by intro h; subst r; omega
      have hpq : GenLoop.Homotopic p q := Quotient.exact
        ((hvan n r hrn).elim
          (⟦p⟧ : HomotopyGroup (Fin r) (E.level n) (E.level n).point) ⟦q⟧)
      exact Quot.sound (Prespectrum.StableRelation.homotopy ⟨n, r, hr, p⟩ q hpq)
    refine ⟨fun x y => ?_⟩
    induction x using Quot.inductionOn with | h a
    induction y using Quot.inductionOn with | h b
    have he := same_stage (raise a b.stage) (raise b a.stage)
      (by rw [raise_stage, raise_stage, Nat.add_comm])
    rw [raise_class, raise_class] at he
    exact he
  -- D2.4–D2.7: the displayed zero and transAt operation are unchanged.
  refine ⟨{
    spectrum := E
    good := hgood
    pi0 := Equiv.ofBijective pi pi_bijective
    pi0_zero := ?_
    pi0_add := ?_
    vanishes := vanishes }⟩
  · exact hzero 0
  · intro n p q
    exact hadd n p q

noncomputable def sourceHF2 : SourceHF2Model := Classical.choice sourceHF2Model_exists

noncomputable def sourceHF2Shift (d : ℤ) : SourceCategory.{0} :=
  sourceLocalization.obj
    (if 0 ≤ d then (Prespectrum.suspension^[d.toNat]) sourceHF2.spectrum
     else (Prespectrum.desuspension^[(-d).toNat]) sourceHF2.spectrum)

/-- Mod-2 cohomology equivalences in all integer degrees. Over the field F₂,
cohomology detects exactly HF₂-homology equivalences, without a boundedness
restriction. The target HF₂ here was fixed before choosing any implementation. -/
def HF2Equivalences : MorphismProperty SourceCategory.{0} :=
  fun X Y f => ∀ d : ℤ,
    Function.Bijective (fun a : Y ⟶ sourceHF2Shift d => f ≫ a)

namespace Prespectrum
/-- The actual right lifting/orthogonality property defining HF₂-local
objects in the ordinary stable category. This is not Moore-locality. -/
def IsHF2Local (X : Prespectrum.{0}) : Prop :=
  ∀ {A B : SourceCategory.{0}} (f : A ⟶ B), HF2Equivalences f →
    Function.Bijective (fun a : B ⟶ sourceLocalization.obj X => f ≫ a)
end Prespectrum

/-- The full subcategory of local objects, represented by point-set spectra. -/
structure CompletedSpectrum where
  spectrum : Prespectrum.{0}
  isLocal : spectrum.IsHF2Local

noncomputable instance : Category CompletedSpectrum where
  Hom X Y := sourceLocalization.obj X.spectrum ⟶ sourceLocalization.obj Y.spectrum
  id X := 𝟙 _
  comp f g := f ≫ g
  id_comp := by intros; apply Category.id_comp
  comp_id := by intros; apply Category.comp_id
  assoc := by intros; apply Category.assoc

/-- A functorial local replacement, including its reflection universal
property in the ordinary stable category. The unit is an actual point-set
map. This pins the completion and all induced maps up to unique isomorphism. -/
structure CompletionModel where
  replacement : Prespectrum.{0} ⥤ Prespectrum.{0}
  unit : 𝟭 _ ⟶ replacement
  isLocal : ∀ X, (replacement.obj X).IsHF2Local
  universal : ∀ (X : Prespectrum.{0}) (Y : CompletedSpectrum),
    Function.Bijective (fun f : sourceLocalization.obj (replacement.obj X) ⟶
        sourceLocalization.obj Y.spectrum => sourceLocalization.map (unit.app X) ≫ f)

/-- Construction of the reflection in the explicitly specified local objects.
No Adams differential, vanishing line, or stable stem is an input. -/
theorem completionModel_exists : Nonempty CompletionModel := by
  -- Markdown II, Lemma 1: every fixed detector is local.
  have detector_local (d : ℤ) :
      (if 0 ≤ d then (Prespectrum.suspension^[d.toNat]) sourceHF2.spectrum
        else (Prespectrum.desuspension^[(-d).toNat]) sourceHF2.spectrum).IsHF2Local := by
    intro A B f hf
    exact hf d
  -- Markdown II, Lemma 2: the detectors and all local objects detect the same maps.
  have detects_all_locals {A B : SourceCategory.{0}} (f : A ⟶ B) :
      HF2Equivalences f ↔ ∀ Y : CompletedSpectrum,
        Function.Bijective (fun a : B ⟶ sourceLocalization.obj Y.spectrum => f ≫ a) := by
    constructor
    · intro hf Y
      exact Y.isLocal f hf
    · intro hf d
      exact hf ⟨_, detector_local d⟩
  -- Markdown II, Lemma 3: this gives both directions of the unit criterion.
  have unit_criterion (R : Prespectrum.{0} ⥤ Prespectrum.{0}) (η : 𝟭 _ ⟶ R) :
      (∀ (X : Prespectrum.{0}) (Y : CompletedSpectrum),
        Function.Bijective (fun f : sourceLocalization.obj (R.obj X) ⟶
          sourceLocalization.obj Y.spectrum => sourceLocalization.map (η.app X) ≫ f)) ↔
      ∀ X, HF2Equivalences (sourceLocalization.map (η.app X)) := by
    constructor
    · intro h X
      exact (detects_all_locals _).2 (h X)
    · intro h X
      exact (detects_all_locals _).1 (h X)
  -- Markdown III, Lemma 9, and G-2--G-5: the remaining construction obligation.
  have local_replacement :
      ∃ (R : Prespectrum.{0} ⥤ Prespectrum.{0}) (η : 𝟭 _ ⟶ R),
        (∀ X, (R.obj X).IsHF2Local) ∧
        ∀ X, HF2Equivalences (sourceLocalization.map (η.app X)) := by
    classical
    -- Markdown III, Lemma 6: small colimits are formed levelwise as pointed quotients.
    let colimitRaw (J : Type) [Category.{0} J] (F : J ⥤ Prespectrum.{0}) (n : ℕ) :=
      Unit ⊕ (Σ j : J, (F.obj j).level n)
    let colimitRel (J : Type) [Category.{0} J] (F : J ⥤ Prespectrum.{0})
        (n : ℕ) (a b : colimitRaw J F n) : Prop :=
      (∃ j, a = Sum.inr ⟨j, ((F.obj j).level n).point⟩ ∧ b = Sum.inl ()) ∨
      (∃ (j k : J) (f : j ⟶ k) (x : (F.obj j).level n),
        a = Sum.inr ⟨j, x⟩ ∧ b = Sum.inr ⟨k, (F.map f).level n x⟩)
    let colimitLeg (J : Type) [Category.{0} J] (F : J ⥤ Prespectrum.{0})
        (c : CategoryTheory.Limits.Cocone F) (n : ℕ) : colimitRaw J F n → c.pt.level n :=
      Sum.elim (fun _ => (c.pt.level n).point) (fun z => (c.ι.app z.1).level n z.2)
    have prespectrum_colimit (J : Type) [Category.{0} J] (F : J ⥤ Prespectrum.{0}) :
        ∃ c : CategoryTheory.Limits.Cocone F,
          Nonempty (CategoryTheory.Limits.IsColimit c) ∧
          ∀ n, IsQuotientMap (colimitLeg J F c n) ∧
            ∀ a b, colimitLeg J F c n a = colimitLeg J F c n b ↔
              Relation.EqvGen (colimitRel J F n) a b := by
      let Raw := colimitRaw J F
      let Rel := colimitRel J F
      let level (n : ℕ) : BasedSpace.{0} :=
        ⟨TopCat.of (Quot (Rel n)), Quot.mk _ (Sum.inl ())⟩
      let inclusion (n : ℕ) (j : J) : C((F.obj j).level n, level n) :=
        ⟨fun x => Quot.mk _ (Sum.inr ⟨j, x⟩),
          continuous_quot_mk.comp (continuous_inr.comp continuous_sigmaMk)⟩
      have inclusion_point (n : ℕ) (j : J) :
          inclusion n j ((F.obj j).level n).point = (level n).point :=
        Quot.sound (Or.inl ⟨j, rfl, rfl⟩)
      have inclusion_map (n : ℕ) {j k : J} (f : j ⟶ k) (x : (F.obj j).level n) :
          inclusion n j x = inclusion n k ((F.map f).level n x) :=
        Quot.sound (Or.inr ⟨j, k, f, x, rfl, rfl⟩)
      let rawBond (n : ℕ) : C(Raw n, C(I, level (n + 1))) :=
        ⟨Sum.elim (fun _ => ContinuousMap.const I (level (n + 1)).point)
          (fun z => (((inclusion (n + 1) z.1).comp ((F.obj z.1).bond n)).curry) z.2),
          continuous_const.sumElim (continuous_sigma fun j =>
            (((inclusion (n + 1) j).comp ((F.obj j).bond n)).curry).continuous)⟩
      have rawBond_rel (n : ℕ) (a b : Raw n) (h : Rel n a b) :
          rawBond n a = rawBond n b := by
        apply ContinuousMap.ext
        intro t
        rcases h with ⟨j, rfl, rfl⟩ | ⟨j, k, f, x, rfl, rfl⟩
        · change inclusion (n + 1) j ((F.obj j).bond n (((F.obj j).level n).point, t)) = _
          rw [(F.obj j).bond_point, inclusion_point]
          rfl
        · change inclusion (n + 1) j ((F.obj j).bond n (x, t)) =
            inclusion (n + 1) k ((F.obj k).bond n ((F.map f).level n x, t))
          rw [inclusion_map (n + 1) f, (F.map f).bond]
      let bond (n : ℕ) : C(level n × I, level (n + 1)) :=
        (⟨Quot.lift (rawBond n) (rawBond_rel n),
          continuous_quot_lift (rawBond_rel n) (rawBond n).continuous⟩ :
          C(level n, C(I, level (n + 1)))).uncurry
      have bond_inclusion (n : ℕ) (j : J) (x : (F.obj j).level n) (t : I) :
          bond n (inclusion n j x, t) = inclusion (n + 1) j ((F.obj j).bond n (x, t)) := rfl
      let L : Prespectrum.{0} := {
        level := level
        bond := bond
        bond_point := fun _ _ => rfl
        bond_zero := by
          intro n x
          induction x using Quot.inductionOn with | h a
          cases a with
          | inl u => rfl
          | inr z =>
            rcases z with ⟨j, x⟩
            change inclusion (n + 1) j ((F.obj j).bond n (x, 0)) = _
            rw [(F.obj j).bond_zero, inclusion_point]
        bond_one := by
          intro n x
          induction x using Quot.inductionOn with | h a
          cases a with
          | inl u => rfl
          | inr z =>
            rcases z with ⟨j, x⟩
            change inclusion (n + 1) j ((F.obj j).bond n (x, 1)) = _
            rw [(F.obj j).bond_one, inclusion_point] }
      let leg (j : J) : F.obj j ⟶ L := {
        level := fun n => inclusion n j
        point := fun n => inclusion_point n j
        bond := fun n x t => (bond_inclusion n j x t).symm }
      let c : CategoryTheory.Limits.Cocone F := {
        pt := L
        ι := {
          app := leg
          naturality := by
            intro j k f
            apply Prespectrum.Hom.ext
            funext n
            apply ContinuousMap.ext
            intro x
            exact (inclusion_map n f x).symm } }
      let desc (s : CategoryTheory.Limits.Cocone F) : L ⟶ s.pt := by
        let rawMap (n : ℕ) : C(Raw n, s.pt.level n) :=
          ⟨Sum.elim (fun _ => (s.pt.level n).point)
            (fun z => (s.ι.app z.1).level n z.2),
            continuous_const.sumElim (continuous_sigma fun j => (s.ι.app j).level n |>.continuous)⟩
        have rawMap_rel (n : ℕ) (a b : Raw n) (h : Rel n a b) : rawMap n a = rawMap n b := by
          rcases h with ⟨j, rfl, rfl⟩ | ⟨j, k, f, x, rfl, rfl⟩
          · exact (s.ι.app j).point n
          · exact (congrArg (fun g : F.obj j ⟶ s.pt => g.level n x) (s.w f)).symm
        let maps (n : ℕ) : C(level n, s.pt.level n) :=
          ⟨Quot.lift (rawMap n) (rawMap_rel n),
            continuous_quot_lift (rawMap_rel n) (rawMap n).continuous⟩
        refine { level := maps, point := fun _ => rfl, bond := ?_ }
        intro n x t
        induction x using Quot.inductionOn with | h a
        cases a with
        | inl u => exact (s.pt.bond_point n t).symm
        | inr z =>
          rcases z with ⟨j, x⟩
          exact (s.ι.app j).bond n x t
      have hc : CategoryTheory.Limits.IsColimit c := {
        desc := desc
        fac := by
          intro s j
          apply Prespectrum.Hom.ext
          funext n
          apply ContinuousMap.ext
          intro x
          rfl
        uniq := by
          intro s m hm
          apply Prespectrum.Hom.ext
          funext n
          apply ContinuousMap.ext
          intro x
          induction x using Quot.inductionOn with | h a
          cases a with
          | inl u => exact m.point n
          | inr z =>
            rcases z with ⟨j, x⟩
            exact congrArg (fun g : F.obj j ⟶ s.pt => g.level n x) (hm j) }
      refine ⟨c, ⟨hc⟩, ?_⟩
      intro n
      have hleg : colimitLeg J F c n = Quot.mk (Rel n) := by
        funext a
        cases a with
        | inl u => cases u; rfl
        | inr z => rfl
      rw [hleg]
      exact ⟨isQuotientMap_quot_mk, fun _ _ => ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩⟩
    have prespectrum_colimits :
        CategoryTheory.Limits.HasColimitsOfSize.{0, 0} Prespectrum.{0} := by
      refine ⟨fun J _ => ⟨fun F => ?_⟩⟩
      obtain ⟨c, ⟨hc⟩, _⟩ := prespectrum_colimit J F
      exact CategoryTheory.Limits.HasColimit.mk ⟨c, hc⟩
    letI := prespectrum_colimits
    -- Markdown III, Lemma 7: closed embeddings survive the quotient pushout.
    have pushout_closed :
        ∀ {A B X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
          (i : A → B) (f : A → X), IsClosedEmbedding i → Continuous f →
          let r : (X ⊕ B) → (X ⊕ B) → Prop :=
            fun u v => ∃ a, u = Sum.inl (f a) ∧ v = Sum.inr (i a)
          IsClosedEmbedding (fun x : X => Quot.mk r (Sum.inl x)) := by
      intro A B X _ _ _ i f hi hf
      let r : (X ⊕ B) → (X ⊕ B) → Prop :=
        fun u v => ∃ a, u = Sum.inl (f a) ∧ v = Sum.inr (i a)
      let inc : X → Quot r := fun x => Quot.mk r (Sum.inl x)
      let test (D : Set X) : X ⊕ B → Prop :=
        Sum.elim (fun x => x ∈ D) (fun b => b ∈ i '' (f ⁻¹' D))
      have htest (D : Set X) : ∀ u v, r u v → test D u = test D v := by
        rintro u v ⟨a, rfl, rfl⟩
        apply propext
        change f a ∈ D ↔ ∃ a', f a' ∈ D ∧ i a' = i a
        constructor
        · intro ha
          exact ⟨a, ha, rfl⟩
        · rintro ⟨a', ha', he⟩
          obtain rfl := hi.injective he
          exact ha'
      let testQ (D : Set X) : Quot r → Prop := Quot.lift (test D) (htest D)
      have hinj : Function.Injective inc := by
        intro x y h
        have he := congrArg (testQ {x}) h
        change (x ∈ ({x} : Set X)) = (y ∈ ({x} : Set X)) at he
        have hy : y ∈ ({x} : Set X) := Eq.mp he (Set.mem_singleton x)
        exact (Set.mem_singleton_iff.mp hy).symm
      change IsClosedEmbedding inc
      refine IsClosedEmbedding.of_continuous_injective_isClosedMap
        (continuous_quot_mk.comp continuous_inl) hinj ?_
      intro D hD
      apply (isQuotientMap_quot_mk (r := r)).isClosed_preimage.mp
      apply isClosed_sum_iff.mpr
      constructor
      · change IsClosed (inc ⁻¹' (inc '' D))
        simpa only [Set.preimage_image_eq D hinj] using hD
      · have he : Sum.inr ⁻¹' ((Quot.mk r) ⁻¹' (inc '' D)) = i '' (f ⁻¹' D) := by
          ext b
          constructor
          · rintro ⟨x, hx, hxb⟩
            have hh := congrArg (testQ D) hxb
            change (x ∈ D) = (b ∈ i '' (f ⁻¹' D)) at hh
            exact Eq.mp hh hx
          · rintro ⟨a, ha, rfl⟩
            exact ⟨f a, ha, Quot.sound ⟨a, rfl, rfl⟩⟩
        rw [he]
        exact hi.isClosedMap _ (hD.preimage hf)
    -- The limit-stage part of Lemma 7 uses the final topology of the colimit.
    have chain_closed :
        ∀ {J : Type} [LinearOrder J]
          (X : J → Type) [∀ j, TopologicalSpace (X j)]
          (L : Type) [TopologicalSpace L]
          (t : ∀ i j, i ≤ j → C(X i, X j)) (ι : ∀ j, C(X j, L)),
          (∀ i j h, IsClosedEmbedding (t i j h)) →
          (∀ i j h x, ι j (t i j h x) = ι i x) →
          (∀ i, Function.Injective (ι i)) →
          (∀ D : Set L, IsClosed D ↔ ∀ j, IsClosed (ι j ⁻¹' D)) →
          ∀ i, IsClosedEmbedding (ι i) := by
      intro J _ X _ L _ t ι ht hι hinj hfinal i
      refine IsClosedEmbedding.of_continuous_injective_isClosedMap
        (ι i).continuous (hinj i) ?_
      intro D hD
      apply (hfinal _).2
      intro j
      rcases le_total i j with hij | hji
      · have he : ι j ⁻¹' (ι i '' D) = t i j hij '' D := by
          ext y
          constructor
          · rintro ⟨x, hx, hxy⟩
            exact ⟨x, hx, hinj j ((hι i j hij x).trans hxy)⟩
          · rintro ⟨x, hx, rfl⟩
            exact ⟨x, hx, (hι i j hij x).symm⟩
        rw [he]
        exact (ht i j hij).isClosedMap _ hD
      · have he : ι j ⁻¹' (ι i '' D) = t j i hji ⁻¹' D := by
          ext y
          constructor
          · rintro ⟨x, hx, hxy⟩
            have h : x = t j i hji y := hinj i (hxy.trans (hι j i hji y).symm)
            change t j i hji y ∈ D
            exact h ▸ hx
          · intro hy
            exact ⟨t j i hji y, hy, hι j i hji y⟩
        rw [he]
        exact hD.preimage (t j i hji).continuous
    -- Markdown III, Lemma 8: a map whose image is in an embedded stage factors continuously.
    have factor_through_embedding (A B X : Prespectrum.{0}) (i : B ⟶ X)
        (hi : ∀ n, IsEmbedding (i.level n)) (f : A ⟶ X)
        (hf : ∀ n a, f.level n a ∈ Set.range (i.level n)) :
        ∃ g : A ⟶ B, g ≫ i = f := by
      let g (n : ℕ) (a : A.level n) : B.level n := Classical.choose (hf n a)
      have hg (n : ℕ) (a : A.level n) : i.level n (g n a) = f.level n a :=
        Classical.choose_spec (hf n a)
      have hg_cont (n : ℕ) : Continuous (g n) := by
        apply (hi n).continuous_iff.2
        change Continuous (fun a => i.level n (g n a))
        simpa only [hg] using (f.level n).continuous
      let g' : A ⟶ B := {
        level := fun n => ⟨g n, hg_cont n⟩
        point := by
          intro n
          apply (hi n).injective
          change i.level n (g n (A.level n).point) = i.level n (B.level n).point
          rw [hg, f.point, i.point]
        bond := by
          intro n a t
          apply (hi (n + 1)).injective
          change i.level (n + 1) (g (n + 1) (A.bond n (a, t))) =
            i.level (n + 1) (B.bond n (g n a, t))
          rw [hg, f.bond, i.bond, hg] }
      refine ⟨g', ?_⟩
      apply Prespectrum.Hom.ext
      funext n
      apply ContinuousMap.ext
      exact hg n
    -- Markdown III, Lemma 8: regularity bounds the selected stages simultaneously.
    have regular_stage_bound (κ : Cardinal.{0}) (hκ : κ.IsRegular)
        (S : Type) (hS : Cardinal.mk S < κ) (s : S → κ.ord.ToType) :
        ∃ b : κ.ord.ToType, ∀ a : S, s a ≤ b := by
      let e : Set.Iio κ.ord ≃o κ.ord.ToType := Ordinal.ToType.mk
      let α : S → Ordinal.{0} := fun a => (e.symm (s a)).val
      have hα : ∀ a : S, α a < κ.ord := fun a => (e.symm (s a)).property
      have hγ : (⨆ a : S, α a) < κ.ord := by
        apply Ordinal.iSup_lt_of_lt_cof
        · rw [hκ.cof_ord]
          exact hS
        · exact hα
      let γ : Set.Iio κ.ord := ⟨⨆ a : S, α a, hγ⟩
      refine ⟨e γ, ?_⟩
      intro a
      have ha : e.symm (s a) ≤ γ := by
        change α a ≤ ⨆ a : S, α a
        exact Ordinal.le_iSup α a
      simpa using e.monotone ha
    -- The equality relation in a chain colimit is witnessed at a common later stage.
    have chain_colimit (J : Type) [LinearOrder J] [Nonempty J]
        (F : J ⥤ Prespectrum.{0})
        (hF : ∀ {i j : J} (f : i ⟶ j) n, IsClosedEmbedding ((F.map f).level n)) :
        ∃ c : CategoryTheory.Limits.Cocone F,
          Nonempty (CategoryTheory.Limits.IsColimit c) ∧
          (∀ j n, IsClosedEmbedding ((c.ι.app j).level n)) ∧
          ∀ n (x : c.pt.level n), ∃ (j : J) (y : (F.obj j).level n),
            (c.ι.app j).level n y = x := by
      obtain ⟨c, hc, hq⟩ := prespectrum_colimit J F
      let j₀ : J := Classical.choice inferInstance
      have hinj (j : J) (n : ℕ) : Function.Injective ((c.ι.app j).level n) := by
        let value (a : colimitRaw J F n) (k : J) : (F.obj k).level n :=
          match a with
          | Sum.inl _ => ((F.obj k).level n).point
          | Sum.inr ⟨i, x⟩ => if h : i ≤ k then (F.map (homOfLE h)).level n x
            else ((F.obj k).level n).point
        have hrel (a b : colimitRaw J F n) (h : Relation.EqvGen (colimitRel J F n) a b) :
            ∃ k, ∀ l, k ≤ l → value a l = value b l := by
          induction h with
          | rel a b h =>
            rcases h with ⟨i, rfl, rfl⟩ | ⟨i, k, f, x, rfl, rfl⟩
            · refine ⟨i, fun l hil => ?_⟩
              dsimp only [value]
              rw [dif_pos hil]
              exact (F.map (homOfLE hil)).point n
            · refine ⟨k, fun l hkl => ?_⟩
              have hil : i ≤ l := (leOfHom f).trans hkl
              dsimp only [value]
              rw [dif_pos hil, dif_pos hkl]
              have hmap : F.map (homOfLE hil) = F.map f ≫ F.map (homOfLE hkl) := by
                rw [← F.map_comp]
                rfl
              exact congrArg (fun g : F.obj i ⟶ F.obj l => g.level n x) hmap
          | refl a => exact ⟨j₀, fun _ _ => rfl⟩
          | symm a b h ih =>
            obtain ⟨k, hk⟩ := ih
            exact ⟨k, fun l hl => (hk l hl).symm⟩
          | trans a b d hab hbd ihab ihbd =>
            obtain ⟨k, hk⟩ := ihab
            obtain ⟨l, hl⟩ := ihbd
            exact ⟨max k l, fun m hm => (hk m ((le_max_left _ _).trans hm)).trans
              (hl m ((le_max_right _ _).trans hm))⟩
        intro x y hxy
        have he : Relation.EqvGen (colimitRel J F n) (Sum.inr ⟨j, x⟩) (Sum.inr ⟨j, y⟩) :=
          ((hq n).2 _ _).1 hxy
        obtain ⟨k, hk⟩ := hrel _ _ he
        have h := hk (max j k) (le_max_right _ _)
        dsimp only [value] at h
        simp only [dif_pos (le_max_left j k)] at h
        exact (hF (homOfLE (le_max_left j k)) n).injective h
      have hclosed (n : ℕ) (D : Set (c.pt.level n)) :
          IsClosed D ↔ ∀ j, IsClosed ((c.ι.app j).level n ⁻¹' D) := by
        rw [← (hq n).1.isClosed_preimage, isClosed_sum_iff]
        constructor
        · intro h j
          exact isClosed_sigma_iff.1 h.2 j
        · intro h
          constructor
          · exact isClosed_discrete _
          · exact isClosed_sigma_iff.2 h
      refine ⟨c, hc, ?_, ?_⟩
      · intro j n
        apply @chain_closed J inferInstance (fun j => (F.obj j).level n)
          (fun j => inferInstance) (c.pt.level n) inferInstance
          (fun i j h => (F.map (homOfLE h)).level n) (fun j => (c.ι.app j).level n)
        · intro i j h
          exact hF (homOfLE h) n
        · intro i j h x
          exact congrArg (fun g : F.obj i ⟶ c.pt => g.level n x) (c.w (homOfLE h))
        · intro i
          exact hinj i n
        · exact hclosed n
      · intro n x
        obtain ⟨a, ha⟩ := (hq n).1.surjective x
        cases a with
        | inl u =>
          refine ⟨j₀, ((F.obj j₀).level n).point, ?_⟩
          exact ((c.ι.app j₀).point n).trans ha
        | inr z => exact ⟨z.1, z.2, ha⟩
    -- Markdown III, Lemma 8, now applied to the actual chain colimit.
    have small_source (κ : Cardinal.{0}) (hκ : κ.IsRegular)
        (F : κ.ord.ToType ⥤ Prespectrum.{0})
        (hF : ∀ {i j : κ.ord.ToType} (f : i ⟶ j) n,
          IsClosedEmbedding ((F.map f).level n))
        (A : Prespectrum.{0}) (hA : Cardinal.mk (Σ n, A.level n) < κ) :
        ∃ c : CategoryTheory.Limits.Cocone F,
          Nonempty (CategoryTheory.Limits.IsColimit c) ∧
          ∀ f : A ⟶ c.pt, ∃ (j : κ.ord.ToType) (g : A ⟶ F.obj j), g ≫ c.ι.app j = f := by
      obtain ⟨j₀, _⟩ := regular_stage_bound κ hκ PEmpty (by simpa using hκ.pos) PEmpty.elim
      letI : Nonempty κ.ord.ToType := ⟨j₀⟩
      obtain ⟨c, hc, he, hs⟩ := chain_colimit κ.ord.ToType F hF
      refine ⟨c, hc, ?_⟩
      intro f
      let stage (a : Σ n, A.level n) : κ.ord.ToType :=
        Classical.choose (hs a.1 (f.level a.1 a.2))
      have hstage (n : ℕ) (a : A.level n) :
          ∃ y, (c.ι.app (stage ⟨n, a⟩)).level n y = f.level n a :=
        Classical.choose_spec (hs n (f.level n a))
      obtain ⟨j, hj⟩ := regular_stage_bound κ hκ (Σ n, A.level n) hA stage
      obtain ⟨g, hg⟩ := factor_through_embedding A (F.obj j) c.pt (c.ι.app j)
        (fun n => (he j n).isEmbedding) f (by
          intro n a
          obtain ⟨y, hy⟩ := hstage n a
          refine ⟨(F.map (homOfLE (hj ⟨n, a⟩))).level n y, ?_⟩
          exact (congrArg (fun g : F.obj (stage ⟨n, a⟩) ⟶ c.pt => g.level n y)
            (c.w (homOfLE (hj ⟨n, a⟩)))).trans hy)
      exact ⟨j, g, hg⟩
    -- The concrete quotient pushout is compatible with the chosen categorical pushout.
    let iso_level {X Y : Prespectrum.{0}} (e : X ≅ Y) (n : ℕ) :
        X.level n ≃ₜ Y.level n := {
        toEquiv := {
          toFun := e.hom.level n
          invFun := e.inv.level n
          left_inv := fun x => congrArg (fun f : X ⟶ X => f.level n x) e.hom_inv_id
          right_inv := fun y => congrArg (fun f : Y ⟶ Y => f.level n y) e.inv_hom_id }
        continuous_toFun := (e.hom.level n).continuous
        continuous_invFun := (e.inv.level n).continuous }
    have iso_level_closed {X Y : Prespectrum.{0}} (e : X ≅ Y) (n : ℕ) :
        IsClosedEmbedding (e.hom.level n) := (iso_level e n).isClosedEmbedding
    have any_colimit_quotient (J : Type) [Category.{0} J] (F : J ⥤ Prespectrum.{0})
        (c : CategoryTheory.Limits.Cocone F) (hc : CategoryTheory.Limits.IsColimit c) :
        ∀ n, IsQuotientMap (colimitLeg J F c n) ∧
          ∀ a b, colimitLeg J F c n a = colimitLeg J F c n b ↔
            Relation.EqvGen (colimitRel J F n) a b := by
      obtain ⟨c₀, ⟨hc₀⟩, h₀⟩ := prespectrum_colimit J F
      let e := hc₀.coconePointUniqueUpToIso hc
      intro n
      have he : colimitLeg J F c n = (iso_level e n) ∘ colimitLeg J F c₀ n := by
        funext a
        cases a with
        | inl u => exact (e.hom.point n).symm
        | inr z =>
          exact (congrArg (fun f : F.obj z.1 ⟶ c.pt => f.level n z.2)
            (hc₀.comp_coconePointUniqueUpToIso_hom hc z.1)).symm
      rw [he]
      refine ⟨(iso_level e n).isQuotientMap.comp (h₀ n).1, ?_⟩
      intro a b
      exact (iso_level e n).injective.eq_iff.trans ((h₀ n).2 a b)
    have prespectrum_pushout_closed (A B X : Prespectrum.{0}) (i : A ⟶ B) (f : A ⟶ X)
        (hi : ∀ n, IsClosedEmbedding (i.level n)) :
        ∀ n, IsClosedEmbedding ((CategoryTheory.Limits.pushout.inl f i).level n) := by
      let Rel (n : ℕ) (a b : X.level n ⊕ B.level n) : Prop :=
        ∃ x : A.level n, a = Sum.inl (f.level n x) ∧ b = Sum.inr (i.level n x)
      let level (n : ℕ) : BasedSpace.{0} :=
        ⟨TopCat.of (Quot (Rel n)), Quot.mk _ (Sum.inl (X.level n).point)⟩
      let ql (n : ℕ) : C(X.level n, level n) :=
        ⟨fun x => Quot.mk _ (Sum.inl x), continuous_quot_mk.comp continuous_inl⟩
      let qr (n : ℕ) : C(B.level n, level n) :=
        ⟨fun b => Quot.mk _ (Sum.inr b), continuous_quot_mk.comp continuous_inr⟩
      have qrel (n : ℕ) (x : A.level n) : ql n (f.level n x) = qr n (i.level n x) :=
        Quot.sound ⟨x, rfl, rfl⟩
      have qr_point (n : ℕ) : qr n (B.level n).point = (level n).point := by
        have h := qrel n (A.level n).point
        rw [f.point, i.point] at h
        exact h.symm
      let rawBond (n : ℕ) : C(X.level n ⊕ B.level n, C(I, level (n + 1))) :=
        ⟨Sum.elim (((ql (n + 1)).comp (X.bond n)).curry)
          (((qr (n + 1)).comp (B.bond n)).curry),
          (((ql (n + 1)).comp (X.bond n)).curry).continuous.sumElim
            (((qr (n + 1)).comp (B.bond n)).curry).continuous⟩
      have rawBond_rel (n : ℕ) (a b : X.level n ⊕ B.level n) (h : Rel n a b) :
          rawBond n a = rawBond n b := by
        rcases h with ⟨x, rfl, rfl⟩
        apply ContinuousMap.ext
        intro t
        change ql (n + 1) (X.bond n (f.level n x, t)) =
          qr (n + 1) (B.bond n (i.level n x, t))
        rw [← f.bond, ← i.bond, qrel]
      let bond (n : ℕ) : C(level n × I, level (n + 1)) :=
        (⟨Quot.lift (rawBond n) (rawBond_rel n),
          continuous_quot_lift (rawBond_rel n) (rawBond n).continuous⟩ :
          C(level n, C(I, level (n + 1)))).uncurry
      let L : Prespectrum.{0} := {
        level := level
        bond := bond
        bond_point := by
          intro n t
          change ql (n + 1) (X.bond n ((X.level n).point, t)) = _
          rw [X.bond_point]
          rfl
        bond_zero := by
          intro n x
          induction x using Quot.inductionOn with | h a
          cases a with
          | inl x =>
            change ql (n + 1) (X.bond n (x, 0)) = _
            rw [X.bond_zero]; rfl
          | inr b =>
            change qr (n + 1) (B.bond n (b, 0)) = _
            rw [B.bond_zero, qr_point]
        bond_one := by
          intro n x
          induction x using Quot.inductionOn with | h a
          cases a with
          | inl x =>
            change ql (n + 1) (X.bond n (x, 1)) = _
            rw [X.bond_one]; rfl
          | inr b =>
            change qr (n + 1) (B.bond n (b, 1)) = _
            rw [B.bond_one, qr_point] }
      let l : X ⟶ L := { level := ql, point := fun _ => rfl, bond := fun _ _ _ => rfl }
      let r : B ⟶ L := { level := qr, point := qr_point, bond := fun _ _ _ => rfl }
      have comm : f ≫ l = i ≫ r := by
        apply Prespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        exact qrel n
      let c := CategoryTheory.Limits.PushoutCocone.mk l r comm
      have hc : CategoryTheory.Limits.IsColimit c := by
        apply CategoryTheory.Limits.PushoutCocone.isColimitAux'
        intro s
        let raw (n : ℕ) : C(X.level n ⊕ B.level n, s.pt.level n) :=
          ⟨Sum.elim (s.inl.level n) (s.inr.level n),
            (s.inl.level n).continuous.sumElim (s.inr.level n).continuous⟩
        have raw_rel (n : ℕ) (a b : X.level n ⊕ B.level n) (h : Rel n a b) :
            raw n a = raw n b := by
          rcases h with ⟨x, rfl, rfl⟩
          exact congrArg (fun g : A ⟶ s.pt => g.level n x) s.condition
        let maps (n : ℕ) : C(level n, s.pt.level n) :=
          ⟨Quot.lift (raw n) (raw_rel n), continuous_quot_lift (raw_rel n) (raw n).continuous⟩
        let d : L ⟶ s.pt := {
          level := maps
          point := fun n => s.inl.point n
          bond := by
            intro n x t
            induction x using Quot.inductionOn with | h a
            cases a with
            | inl x => exact s.inl.bond n x t
            | inr b => exact s.inr.bond n b t }
        refine ⟨d, ?_, ?_, ?_⟩
        · apply Prespectrum.Hom.ext
          rfl
        · apply Prespectrum.Hom.ext
          rfl
        · intro m hl hr
          apply Prespectrum.Hom.ext
          funext n
          apply ContinuousMap.ext
          intro x
          induction x using Quot.inductionOn with | h a
          cases a with
          | inl x => exact congrArg (fun g : X ⟶ s.pt => g.level n x) hl
          | inr b => exact congrArg (fun g : B ⟶ s.pt => g.level n b) hr
      let e := hc.coconePointUniqueUpToIso
        (CategoryTheory.Limits.colimit.isColimit (CategoryTheory.Limits.span f i))
      have he : l ≫ e.hom = CategoryTheory.Limits.pushout.inl f i :=
        hc.comp_coconePointUniqueUpToIso_hom _ CategoryTheory.Limits.WalkingSpan.left
      intro n
      have hn : (CategoryTheory.Limits.pushout.inl f i).level n = (e.hom.level n).comp (l.level n) :=
        (congrArg (fun g : X ⟶ CategoryTheory.Limits.pushout f i => g.level n) he).symm
      rw [hn]
      exact (iso_level_closed e n).comp
        (pushout_closed (i.level n) (f.level n) (hi n) (f.level n).continuous)
    -- Markdown III, Lemma 7: the wedge of closed embeddings is a closed embedding.
    have coproduct_closed (S : Type) (A B : S → Prespectrum.{0}) (i : ∀ s, A s ⟶ B s)
        (hi : ∀ s n, IsClosedEmbedding ((i s).level n)) :
        ∀ n, IsClosedEmbedding ((CategoryTheory.Limits.Sigma.map i).level n) := by
      let FA := Discrete.functor A
      let FB := Discrete.functor B
      let cA := CategoryTheory.Limits.colimit.cocone FA
      let cB := CategoryTheory.Limits.colimit.cocone FB
      let f := CategoryTheory.Limits.Sigma.map i
      intro n
      change IsClosedEmbedding (f.level n)
      let qA := colimitLeg (Discrete S) FA cA n
      let qB := colimitLeg (Discrete S) FB cB n
      have hA := any_colimit_quotient (Discrete S) FA cA
        (CategoryTheory.Limits.colimit.isColimit FA) n
      have hB := any_colimit_quotient (Discrete S) FB cB
        (CategoryTheory.Limits.colimit.isColimit FB) n
      have qA_point (s : Discrete S) :
          qA (Sum.inr ⟨s, ((A s.as).level n).point⟩) = (cA.pt.level n).point :=
        (cA.ι.app s).point n
      have f_point : f.level n (cA.pt.level n).point = (cB.pt.level n).point := f.point n
      have f_ι (s : S) (a : (A s).level n) :
          f.level n (qA (Sum.inr ⟨Discrete.mk s, a⟩)) =
            qB (Sum.inr ⟨Discrete.mk s, (i s).level n a⟩) :=
        congrArg (fun g : A s ⟶ cB.pt => g.level n a)
          (CategoryTheory.Limits.Sigma.ι_map i s)
      let test (D : Set (cA.pt.level n)) : colimitRaw (Discrete S) FB n → Prop :=
        Sum.elim (fun _ => (cA.pt.level n).point ∈ D)
          (fun z => ∃ a : (A z.1.as).level n,
            qA (Sum.inr ⟨z.1, a⟩) ∈ D ∧ (i z.1.as).level n a = z.2)
      have test_rel (D : Set (cA.pt.level n)) (a b : colimitRaw (Discrete S) FB n)
          (h : colimitRel (Discrete S) FB n a b) : test D a = test D b := by
        rcases h with ⟨s, rfl, rfl⟩ | ⟨s, t, g, x, rfl, rfl⟩
        · apply propext
          constructor
          · rintro ⟨a, ha, he⟩
            have hp : a = ((A s.as).level n).point :=
              (hi s.as n).injective (he.trans ((i s.as).point n).symm)
            subst a
            change (cA.pt.level n).point ∈ D
            exact Eq.mp (congrArg (fun z : cA.pt.level n => z ∈ D) (qA_point s)) ha
          · intro h
            refine ⟨((A s.as).level n).point, ?_, (i s.as).point n⟩
            exact Eq.mpr (congrArg (fun z : cA.pt.level n => z ∈ D) (qA_point s)) h
        · have hst : s = t := Discrete.ext (Discrete.eq_of_hom g)
          subst t
          have hg : g = 𝟙 s := Subsingleton.elim _ _
          subst g
          have hx : (FB.map (𝟙 s)).level n x = x :=
            congrArg (fun g : FB.obj s ⟶ FB.obj s => g.level n x) (FB.map_id s)
          exact congrArg (fun y : (FB.obj s).level n => test D (Sum.inr ⟨s, y⟩)) hx.symm
      have test_eq (D : Set (cA.pt.level n)) {a b : colimitRaw (Discrete S) FB n}
          (h : qB a = qB b) : test D a = test D b := by
        have he := (hB.2 a b).1 h
        clear h
        induction he with
        | rel a b h => exact test_rel D a b h
        | refl a => rfl
        | symm a b h ih => exact ih.symm
        | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
      let testQ (D : Set (cA.pt.level n)) (x : cB.pt.level n) : Prop :=
        test D (Classical.choose (hB.1.surjective x))
      have testQ_q (D : Set (cA.pt.level n)) (a : colimitRaw (Discrete S) FB n) :
          testQ D (qB a) = test D a :=
        test_eq D (Classical.choose_spec (hB.1.surjective (qB a)))
      have testQ_f (D : Set (cA.pt.level n)) (x : cA.pt.level n) :
          testQ D (f.level n x) = (x ∈ D) := by
        obtain ⟨a, rfl⟩ := hA.1.surjective x
        cases a with
        | inl u =>
          change testQ D (f.level n (cA.pt.level n).point) = _
          rw [f_point]
          exact testQ_q D (Sum.inl ())
        | inr z =>
          rcases z with ⟨⟨s⟩, a⟩
          rw [f_ι, testQ_q]
          apply propext
          constructor
          · rintro ⟨a', ha', he⟩
            have haa : a' = a := (hi s n).injective he
            exact haa ▸ ha'
          · intro ha
            exact ⟨a, ha, rfl⟩
      have hinj : Function.Injective (f.level n) := by
        intro x y h
        have hh := congrArg (testQ {x}) h
        rw [testQ_f, testQ_f] at hh
        exact (Set.mem_singleton_iff.mp (Eq.mp hh (Set.mem_singleton x))).symm
      refine IsClosedEmbedding.of_continuous_injective_isClosedMap (f.level n).continuous hinj ?_
      intro D hD
      apply hB.1.isClosed_preimage.mp
      apply isClosed_sum_iff.2
      constructor
      · exact isClosed_discrete _
      · apply isClosed_sigma_iff.2
        intro s
        have he :
            Sigma.mk s ⁻¹' (Sum.inr ⁻¹' (qB ⁻¹' (f.level n '' D))) =
              (i s.as).level n '' ((cA.ι.app s).level n ⁻¹' D) := by
          ext b
          constructor
          · rintro ⟨x, hx, hxb⟩
            have hh := congrArg (testQ D) hxb
            rw [testQ_f, testQ_q] at hh
            exact Eq.mp hh hx
          · rintro ⟨a, ha, rfl⟩
            exact ⟨qA (Sum.inr ⟨s, a⟩), ha, f_ι s.as a⟩
        change IsClosed (Sigma.mk s ⁻¹' (Sum.inr ⁻¹' (qB ⁻¹' (f.level n '' D))))
        rw [he]
        exact (hi s.as n).isClosedMap _ (hD.preimage ((cA.ι.app s).level n).continuous)
    -- Markdown III, Lemma 9, (16): attach every labelled extension problem at once.
    let cell_step (S : Type) (A B : S → Prespectrum.{0}) (j : ∀ s, A s ⟶ B s) :
        MorphismProperty Prespectrum.{0} := fun X Y u =>
      ∃ (K : Type) (p : K → S) (a : ∀ k, A (p k) ⟶ X)
        (b : CategoryTheory.Limits.sigmaObj (fun k => B (p k)) ⟶ Y),
        ∃ h : CategoryTheory.Limits.Sigma.desc a ≫ u =
          CategoryTheory.Limits.Sigma.map (fun k => j (p k)) ≫ b,
          Nonempty (CategoryTheory.Limits.IsColimit
            (CategoryTheory.Limits.PushoutCocone.mk u b h))
    have attach_step (S : Type) (A B : S → Prespectrum.{0}) (j : ∀ s, A s ⟶ B s)
        (hj : ∀ s n, IsClosedEmbedding ((j s).level n)) :
        ∃ T : Prespectrum.{0} ⥤ Prespectrum.{0}, ∃ η : 𝟭 _ ⟶ T,
          (∀ X n, IsClosedEmbedding ((η.app X).level n)) ∧
          (∀ (X : Prespectrum.{0}) (s : S) (a : A s ⟶ X),
            ∃ b : B s ⟶ T.obj X, j s ≫ b = a ≫ η.app X) ∧
          ∀ X, cell_step S A B j (η.app X) := by
      let Idx (X : Prespectrum.{0}) := Σ s : S, A s ⟶ X
      let src (X : Prespectrum.{0}) (i : Idx X) := A i.1
      let tgt (X : Prespectrum.{0}) (i : Idx X) := B i.1
      let top (X : Prespectrum.{0}) : CategoryTheory.Limits.sigmaObj (src X) ⟶ X :=
        CategoryTheory.Limits.Sigma.desc (fun i => i.2)
      let side (X : Prespectrum.{0}) :
          CategoryTheory.Limits.sigmaObj (src X) ⟶ CategoryTheory.Limits.sigmaObj (tgt X) :=
        CategoryTheory.Limits.Sigma.desc (fun i => j i.1 ≫ CategoryTheory.Limits.Sigma.ι (tgt X) i)
      let N (X : Prespectrum.{0}) := CategoryTheory.Limits.pushout (top X) (side X)
      let u (X : Prespectrum.{0}) : X ⟶ N X := CategoryTheory.Limits.pushout.inl _ _
      let v (X : Prespectrum.{0}) : CategoryTheory.Limits.sigmaObj (tgt X) ⟶ N X :=
        CategoryTheory.Limits.pushout.inr _ _
      let cell (X : Prespectrum.{0}) (i : Idx X) : B i.1 ⟶ N X :=
        CategoryTheory.Limits.Sigma.ι (tgt X) i ≫ v X
      have top_ι (X : Prespectrum.{0}) (i : Idx X) :
          CategoryTheory.Limits.Sigma.ι (src X) i ≫ top X = i.2 :=
        CategoryTheory.Limits.Sigma.ι_desc _ _
      have side_ι (X : Prespectrum.{0}) (i : Idx X) :
          CategoryTheory.Limits.Sigma.ι (src X) i ≫ side X =
            j i.1 ≫ CategoryTheory.Limits.Sigma.ι (tgt X) i :=
        CategoryTheory.Limits.Sigma.ι_desc _ _
      have square (X : Prespectrum.{0}) : top X ≫ u X = side X ≫ v X :=
        CategoryTheory.Limits.pushout.condition
      have cell_rel (X : Prespectrum.{0}) (i : Idx X) :
          j i.1 ≫ cell X i = i.2 ≫ u X := by
        calc
          j i.1 ≫ cell X i =
              (CategoryTheory.Limits.Sigma.ι (src X) i ≫ side X) ≫ v X := by
            rw [side_ι]
            exact (Category.assoc _ _ _).symm
          _ = CategoryTheory.Limits.Sigma.ι (src X) i ≫ (side X ≫ v X) := Category.assoc _ _ _
          _ = CategoryTheory.Limits.Sigma.ι (src X) i ≫ (top X ≫ u X) := by rw [← square]
          _ = (CategoryTheory.Limits.Sigma.ι (src X) i ≫ top X) ≫ u X :=
            (Category.assoc _ _ _).symm
          _ = i.2 ≫ u X := by rw [top_ι]
      let newCells {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
          CategoryTheory.Limits.sigmaObj (tgt X) ⟶ N Y :=
        CategoryTheory.Limits.Sigma.desc (fun i => cell Y ⟨i.1, i.2 ≫ f⟩)
      have newCells_ι {X Y : Prespectrum.{0}} (f : X ⟶ Y) (i : Idx X) :
          CategoryTheory.Limits.Sigma.ι (tgt X) i ≫ newCells f = cell Y ⟨i.1, i.2 ≫ f⟩ :=
        CategoryTheory.Limits.Sigma.ι_desc _ _
      have map_square {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
          top X ≫ (f ≫ u Y) = side X ≫ newCells f := by
        apply CategoryTheory.Limits.Sigma.hom_ext _ _
        intro i
        calc
          CategoryTheory.Limits.Sigma.ι (src X) i ≫ (top X ≫ (f ≫ u Y)) =
              (i.2 ≫ f) ≫ u Y := by
            rw [← Category.assoc, top_ι, ← Category.assoc]
          _ = j i.1 ≫ cell Y ⟨i.1, i.2 ≫ f⟩ := (cell_rel Y ⟨i.1, i.2 ≫ f⟩).symm
          _ = CategoryTheory.Limits.Sigma.ι (src X) i ≫ (side X ≫ newCells f) := by
            conv_rhs => rw [← Category.assoc, side_ι, Category.assoc, newCells_ι]
      let m {X Y : Prespectrum.{0}} (f : X ⟶ Y) : N X ⟶ N Y :=
        CategoryTheory.Limits.pushout.desc (f ≫ u Y) (newCells f) (map_square f)
      have m_u {X Y : Prespectrum.{0}} (f : X ⟶ Y) : u X ≫ m f = f ≫ u Y :=
        CategoryTheory.Limits.pushout.inl_desc _ _ _
      have m_v {X Y : Prespectrum.{0}} (f : X ⟶ Y) : v X ≫ m f = newCells f :=
        CategoryTheory.Limits.pushout.inr_desc _ _ _
      have m_cell {X Y : Prespectrum.{0}} (f : X ⟶ Y) (i : Idx X) :
          cell X i ≫ m f = cell Y ⟨i.1, i.2 ≫ f⟩ := by
        change (CategoryTheory.Limits.Sigma.ι (tgt X) i ≫ v X) ≫ m f = _
        rw [Category.assoc, m_v, newCells_ι]
      have N_ext {X W : Prespectrum.{0}} (f g : N X ⟶ W)
          (hu : u X ≫ f = u X ≫ g)
          (hc : ∀ i : Idx X, cell X i ≫ f = cell X i ≫ g) : f = g := by
        apply CategoryTheory.Limits.pushout.hom_ext hu
        apply CategoryTheory.Limits.Sigma.hom_ext _ _
        intro i
        simpa only [cell, Category.assoc] using hc i
      let T : Prespectrum.{0} ⥤ Prespectrum.{0} := {
        obj := N
        map := m
        map_id := by
          intro X
          apply N_ext
          · rw [m_u, Category.id_comp, Category.comp_id]
          · rintro ⟨s, a⟩
            rw [m_cell, Category.comp_id]
            simp only [Category.comp_id]
        map_comp := by
          intro X Y Z f g
          apply N_ext
          · calc
              u X ≫ m (f ≫ g) = (f ≫ g) ≫ u Z := m_u _
              _ = f ≫ (g ≫ u Z) := Category.assoc _ _ _
              _ = f ≫ (u Y ≫ m g) := by rw [m_u]
              _ = (f ≫ u Y) ≫ m g := (Category.assoc _ _ _).symm
              _ = (u X ≫ m f) ≫ m g := by rw [m_u]
              _ = u X ≫ (m f ≫ m g) := Category.assoc _ _ _
          · rintro ⟨s, a⟩
            calc
              cell X ⟨s, a⟩ ≫ m (f ≫ g) = cell Z ⟨s, a ≫ (f ≫ g)⟩ := m_cell _ _
              _ = cell Z ⟨s, (a ≫ f) ≫ g⟩ := by rw [Category.assoc]
              _ = cell Y ⟨s, a ≫ f⟩ ≫ m g := (m_cell g ⟨s, a ≫ f⟩).symm
              _ = (cell X ⟨s, a⟩ ≫ m f) ≫ m g :=
                congrArg (fun k : B s ⟶ N Y => k ≫ m g) (m_cell f ⟨s, a⟩).symm
              _ = cell X ⟨s, a⟩ ≫ (m f ≫ m g) := Category.assoc _ _ _ }
      let η : 𝟭 _ ⟶ T := { app := u, naturality := fun X Y f => (m_u f).symm }
      refine ⟨T, η, ?_, ?_, ?_⟩
      · intro X n
        have hs : side X = CategoryTheory.Limits.Sigma.map (fun i : Idx X => j i.1) := by
          apply CategoryTheory.Limits.Sigma.hom_ext _ _
          intro i
          rw [side_ι, CategoryTheory.Limits.Sigma.ι_map]
        exact prespectrum_pushout_closed _ _ _ (side X) (top X) (by
          rw [hs]
          exact coproduct_closed (Idx X) (src X) (tgt X) (fun i => j i.1)
            (fun i n => hj i.1 n)) n
      · intro X s a
        exact ⟨cell X ⟨s, a⟩, cell_rel X ⟨s, a⟩⟩
      · intro X
        have hs : side X = CategoryTheory.Limits.Sigma.map (fun i : Idx X => j i.1) := by
          apply CategoryTheory.Limits.Sigma.hom_ext _ _
          intro i
          rw [side_ι, CategoryTheory.Limits.Sigma.ι_map]
        have h : top X ≫ u X =
            CategoryTheory.Limits.Sigma.map (fun i : Idx X => j i.1) ≫ v X := by
          rw [← hs]
          exact square X
        refine ⟨Idx X, (fun i => i.1), (fun i => i.2), v X, h, ?_⟩
        change Nonempty (CategoryTheory.Limits.IsColimit
          (CategoryTheory.Limits.PushoutCocone.mk (u X) (v X) h))
        revert h
        rw [← hs]
        intro h
        exact ⟨CategoryTheory.Limits.pushoutIsPushout (top X) (side X)⟩
    -- Pointwise colimits keep every stage of the transfinite construction strictly functorial.
    have functor_colimit (J : Type) [Category.{0} J]
        (D : J ⥤ (Prespectrum.{0} ⥤ Prespectrum.{0})) :
        ∃ c : CategoryTheory.Limits.Cocone D,
          Nonempty (CategoryTheory.Limits.IsColimit c) ∧
          ∀ X : Prespectrum.{0}, Nonempty (CategoryTheory.Limits.IsColimit
            (((evaluation Prespectrum.{0} Prespectrum.{0}).obj X).mapCocone c)) := by
      let L : Prespectrum.{0} ⥤ Prespectrum.{0} := D.flip ⋙ CategoryTheory.Limits.colim
      let c : CategoryTheory.Limits.Cocone D := {
        pt := L
        ι := {
          app := fun j => {
            app := fun X => CategoryTheory.Limits.colimit.ι (D.flip.obj X) j
            naturality := by
              intro X Y f
              exact (CategoryTheory.Limits.ι_colimMap (D.flip.map f) j).symm }
          naturality := by
            intro j k g
            apply NatTrans.ext
            funext X
            change (D.flip.obj X).map g ≫ CategoryTheory.Limits.colimit.ι (D.flip.obj X) k =
              CategoryTheory.Limits.colimit.ι (D.flip.obj X) j ≫ 𝟙 _
            rw [Category.comp_id]
            exact CategoryTheory.Limits.colimit.w (D.flip.obj X) g } }
      have hX (X : Prespectrum.{0}) : CategoryTheory.Limits.IsColimit
          (((evaluation Prespectrum.{0} Prespectrum.{0}).obj X).mapCocone c) := by
        exact CategoryTheory.Limits.colimit.isColimit (D.flip.obj X)
      have hc : CategoryTheory.Limits.IsColimit c := {
        desc := fun s => by
          let d (X : Prespectrum.{0}) : c.pt.obj X ⟶ s.pt.obj X :=
            (hX X).desc (((evaluation Prespectrum.{0} Prespectrum.{0}).obj X).mapCocone s)
          have hd (X : Prespectrum.{0}) (j : J) :
              (c.ι.app j).app X ≫ d X = (s.ι.app j).app X := (hX X).fac _ j
          refine { app := d, naturality := ?_ }
          intro X Y f
          apply (hX X).hom_ext
          intro j
          change (c.ι.app j).app X ≫ (c.pt.map f ≫ d Y) =
            (c.ι.app j).app X ≫ (d X ≫ s.pt.map f)
          exact (Category.assoc _ _ _).symm.trans
            ((congrArg (fun k : (D.obj j).obj X ⟶ c.pt.obj Y => k ≫ d Y)
              ((c.ι.app j).naturality f).symm).trans
              ((Category.assoc _ _ _).trans
                ((congrArg (fun k : (D.obj j).obj Y ⟶ s.pt.obj Y => (D.obj j).map f ≫ k)
                  (hd Y j)).trans
                  (((s.ι.app j).naturality f).trans
                    ((congrArg (fun k : (D.obj j).obj X ⟶ s.pt.obj X => k ≫ s.pt.map f)
                      (hd X j).symm).trans (Category.assoc _ _ _))))))
        fac := by
          intro s j
          apply NatTrans.ext
          funext X
          exact (hX X).fac _ j
        uniq := by
          intro s m hm
          apply NatTrans.ext
          funext X
          apply (hX X).hom_ext
          intro j
          exact (NatTrans.congr_app (hm j) X).trans
            ((hX X).fac (((evaluation Prespectrum.{0} Prespectrum.{0}).obj X).mapCocone s) j).symm }
      exact ⟨c, ⟨hc⟩, fun X => ⟨hX X⟩⟩
    have functor_colimits : CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
        (Prespectrum.{0} ⥤ Prespectrum.{0}) := by
      refine ⟨fun J _ => ⟨fun D => ?_⟩⟩
      obtain ⟨c, ⟨hc⟩, _⟩ := functor_colimit J D
      exact CategoryTheory.Limits.HasColimit.mk ⟨c, hc⟩
    -- Transport smallness to any chosen colimit, so all source maps use the same final object.
    have small_source_at (κ : Cardinal.{0}) (hκ : κ.IsRegular)
        (F : κ.ord.ToType ⥤ Prespectrum.{0})
        (hF : ∀ {i j : κ.ord.ToType} (f : i ⟶ j) n,
          IsClosedEmbedding ((F.map f).level n))
        (A : Prespectrum.{0}) (hA : Cardinal.mk (Σ n, A.level n) < κ)
        (c : CategoryTheory.Limits.Cocone F) (hc : CategoryTheory.Limits.IsColimit c)
        (f : A ⟶ c.pt) :
        ∃ (j : κ.ord.ToType) (g : A ⟶ F.obj j), g ≫ c.ι.app j = f := by
      obtain ⟨c₀, ⟨hc₀⟩, hs⟩ := small_source κ hκ F hF A hA
      let e := hc.coconePointUniqueUpToIso hc₀
      obtain ⟨j, g, hg⟩ := hs (f ≫ e.hom)
      refine ⟨j, g, ?_⟩
      calc
        g ≫ c.ι.app j = g ≫ (c₀.ι.app j ≫ e.inv) :=
          congrArg (fun k => g ≫ k) (hc.comp_coconePointUniqueUpToIso_inv hc₀ j).symm
        _ = (g ≫ c₀.ι.app j) ≫ e.inv := (Category.assoc _ _ _).symm
        _ = (f ≫ e.hom) ≫ e.inv := congrArg (fun k => k ≫ e.inv) hg
        _ = f := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    -- Extend an initial-segment diagram by its specified cocone.
    -- This is the local form of the construction in Mathlib's Iteration/FunctorOfCocone.
    have extend_cocone (J : Type) [LinearOrder J] (j : J)
        (F : Set.Iio j ⥤ (Prespectrum.{0} ⥤ Prespectrum.{0}))
        (c : CategoryTheory.Limits.Cocone F) :
        ∃ G : Set.Iic j ⥤ (Prespectrum.{0} ⥤ Prespectrum.{0}),
          (∀ (i : J) (hi : i < j), G.obj ⟨i, hi.le⟩ = F.obj ⟨i, hi⟩) ∧
          G.obj ⟨j, le_rfl⟩ = c.pt ∧
          (∀ (a b : J) (hab : a ≤ b) (hb : b < j),
            Arrow.mk (G.map (homOfLE hab : ⟨a, hab.trans hb.le⟩ ⟶ ⟨b, hb.le⟩)) =
              Arrow.mk (F.map (homOfLE hab : ⟨a, lt_of_le_of_lt hab hb⟩ ⟶ ⟨b, hb⟩))) ∧
          ∀ (i : J) (hi : i < j),
            Arrow.mk (G.map (homOfLE hi.le : ⟨i, hi.le⟩ ⟶ ⟨j, le_rfl⟩)) =
              Arrow.mk (c.ι.app ⟨i, hi⟩) := by
      let obj (i : J) := if hi : i < j then F.obj ⟨i, hi⟩ else c.pt
      let objIso (i : J) (hi : i < j) : obj i ≅ F.obj ⟨i, hi⟩ := eqToIso (dif_pos hi)
      let objIsoPt : obj j ≅ c.pt := eqToIso (dif_neg (lt_irrefl _))
      let map (a b : J) (hab : a ≤ b) (hb : b ≤ j) : obj a ⟶ obj b :=
        if h₂ : b < j then
          (objIso a (lt_of_le_of_lt hab h₂)).hom ≫ F.map (homOfLE hab) ≫ (objIso b h₂).inv
        else
          have hb' : b = j := le_antisymm hb (le_of_not_gt h₂)
          if h₁ : a < j then
            (objIso a h₁).hom ≫ c.ι.app ⟨a, h₁⟩ ≫ objIsoPt.inv ≫ eqToHom (by subst b; rfl)
          else
            have ha' : a = j := le_antisymm (hab.trans hb) (le_of_not_gt h₁)
            eqToHom (by subst a b; rfl)
      have map_id (i : J) (hi : i ≤ j) : map i i le_rfl hi = 𝟙 _ := by
        dsimp [map]
        grind
      have map_comp (a b d : J) (hab : a ≤ b) (hbd : b ≤ d) (hd : d ≤ j) :
          map a d (hab.trans hbd) hd = map a b hab (hbd.trans hd) ≫ map b d hbd hd := by
        obtain hab | rfl := hab.lt_or_eq
        · obtain hbd | rfl := hbd.lt_or_eq
          · dsimp only [map]
            obtain hd | rfl := hd.lt_or_eq
            · rw [dif_pos hd, dif_pos (hbd.trans hd), dif_pos hd, Category.assoc,
                Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, homOfLE_comp]
            · rw [dif_neg (lt_irrefl _), dif_pos (hab.trans hbd), dif_pos hbd,
                dif_neg (lt_irrefl _), dif_pos hbd, eqToHom_refl, Category.comp_id,
                Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
              have hw := c.w (homOfLE hab.le :
                ⟨a, hab.trans hbd⟩ ⟶ ⟨b, hbd⟩)
              set_option backward.isDefEq.respectTransparency false in
                simpa only [Category.assoc, Category.comp_id] using
                  congrArg (fun k : F.obj ⟨a, hab.trans hbd⟩ ⟶ c.pt =>
                    (objIso a (hab.trans hbd)).hom ≫ k ≫ objIsoPt.inv) hw.symm
          · rw [map_id b hd, Category.comp_id]
        · rw [map_id a (hbd.trans hd), Category.id_comp]
      let G : Set.Iic j ⥤ (Prespectrum.{0} ⥤ Prespectrum.{0}) := {
        obj := fun i => obj i.1
        map := fun {a b} f => map a.1 b.1 (leOfHom f) b.2
        map_id := fun i => map_id i.1 i.2
        map_comp := fun {a b d} f g => map_comp a.1 b.1 d.1 (leOfHom f) (leOfHom g) d.2 }
      refine ⟨G, fun i hi => dif_pos hi, dif_neg (lt_irrefl _), ?_, ?_⟩
      · intro a b hab hb
        apply Arrow.ext (dif_pos (lt_of_le_of_lt hab hb)) (dif_pos hb)
        change map a b hab hb.le = _
        dsimp only [map]
        rw [dif_pos hb]
        rfl
      · intro i hi
        apply Arrow.ext (dif_pos hi) (dif_neg (lt_irrefl _))
        change map i j hi.le le_rfl = _
        dsimp only [map]
        rw [dif_neg (lt_irrefl _), dif_pos hi, eqToHom_refl, Category.comp_id]
        rfl
    let below (J : Type) [LinearOrder J] (j : J) : Set.Iio j ⥤ J := {
      obj := Subtype.val
      map := fun f => homOfLE (leOfHom f) }
    have transfinite_iteration (J : Type) [LinearOrder J] [SuccOrder J]
        [OrderBot J] [WellFoundedLT J] (T : Prespectrum.{0} ⥤ Prespectrum.{0})
        (η : 𝟭 Prespectrum.{0} ⟶ T) :
        ∃ D : J ⥤ (Prespectrum.{0} ⥤ Prespectrum.{0}),
          D.obj ⊥ = 𝟭 Prespectrum.{0} ∧
          (∀ (i : J) (hi : ¬ IsMax i),
            Arrow.mk (D.map (homOfLE (Order.le_succ i))) =
              Arrow.mk (Functor.whiskerLeft (D.obj i) η)) ∧
          ∀ (j : J) (hj : Order.IsSuccLimit j),
            ∃ c : CategoryTheory.Limits.Cocone (below J j ⋙ D),
              Nonempty (CategoryTheory.Limits.IsColimit c) ∧
              (∀ X : Prespectrum.{0}, Nonempty (CategoryTheory.Limits.IsColimit
                (((evaluation Prespectrum.{0} Prespectrum.{0}).obj X).mapCocone c))) ∧
              ∀ (i : J) (hi : i < j), Arrow.mk (c.ι.app ⟨i, hi⟩) =
                Arrow.mk (D.map (homOfLE hi.le)) := by
      let E := Prespectrum.{0} ⥤ Prespectrum.{0}
      let next (G : E) : E := G ⋙ T
      let step (G : E) : G ⟶ next G := Functor.whiskerLeft G η
      let limC (i : J) (F : Set.Iio i ⥤ E) : CategoryTheory.Limits.Cocone F :=
        (functor_colimit (Set.Iio i) F).choose
      have limC_isColimit (i : J) (F : Set.Iio i ⥤ E) :
          Nonempty (CategoryTheory.Limits.IsColimit (limC i F)) :=
        (functor_colimit (Set.Iio i) F).choose_spec.1
      have limC_eval (i : J) (F : Set.Iio i ⥤ E) (X : Prespectrum.{0}) :
          Nonempty (CategoryTheory.Limits.IsColimit
            (((evaluation Prespectrum.{0} Prespectrum.{0}).obj X).mapCocone (limC i F))) :=
        (functor_colimit (Set.Iio i) F).choose_spec.2 X
      let rLT {i j : J} (h : i ≤ j) (F : Set.Iic j ⥤ E) : Set.Iio i ⥤ E := {
        obj := fun k => F.obj ⟨k.1, k.2.le.trans h⟩
        map := fun f => F.map (homOfLE (leOfHom f))
        map_id := fun k => by simpa using F.map_id ⟨k.1, k.2.le.trans h⟩
        map_comp := by
          intro a b d f g
          simpa using F.map_comp
            (homOfLE (leOfHom f)) (homOfLE (leOfHom g)) }
      let rLE {i j : J} (h : i ≤ j) (F : Set.Iic j ⥤ E) : Set.Iic i ⥤ E := {
        obj := fun k => F.obj ⟨k.1, k.2.trans h⟩
        map := fun f => F.map (homOfLE (leOfHom f))
        map_id := fun k => by simpa using F.map_id ⟨k.1, k.2.trans h⟩
        map_comp := by
          intro a b d f g
          simpa using F.map_comp
            (homOfLE (leOfHom f)) (homOfLE (leOfHom g)) }
      let aMap {j : J} (F : Set.Iic j ⥤ E) (a b : J) (hab : a ≤ b) (hb : b ≤ j) : Arrow E :=
        Arrow.mk (F.map (homOfLE hab : ⟨a, hab.trans hb⟩ ⟶ ⟨b, hb⟩))
      let Good (j : J) (F : Set.Iic j ⥤ E) : Prop :=
        F.obj ⟨⊥, bot_le⟩ = 𝟭 Prespectrum.{0} ∧
        (∀ (i : J) (hi : i < j),
          aMap F i (Order.succ i) (Order.le_succ i) (Order.succ_le_of_lt hi) =
            Arrow.mk (step (F.obj ⟨i, hi.le⟩))) ∧
        ∀ (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) (k : J) (hk : k < i),
          aMap F k i hk.le hij = Arrow.mk ((limC i (rLT hij F)).ι.app ⟨k, hk⟩)
      let Prefix (j : J) := { F : Set.Iic j ⥤ E // Good j F }
      let trunc {i j : J} (p : Prefix j) (h : i ≤ j) : Prefix i :=
        ⟨rLE h p.1, p.2.1,
          (fun k hk => p.2.2.1 k (lt_of_lt_of_le hk h)),
          fun k hk hki a ha => by
            simpa only [rLT, rLE] using p.2.2.2 k hk (hki.trans h) a ha⟩
      have obj_succ {j : J} (p : Prefix j) (i : J) (hi : i < j) :
          p.1.obj ⟨Order.succ i, Order.succ_le_of_lt hi⟩ = next (p.1.obj ⟨i, hi.le⟩) :=
        congrArg Comma.right (p.2.2.1 i hi)
      have obj_limit {j : J} (p : Prefix j) (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
          p.1.obj ⟨i, hij⟩ = (limC i (rLT hij p.1)).pt :=
        congrArg Comma.right (p.2.2.2 i hi hij ⊥ hi.bot_lt)
      have mapEq_refl {j : J} (F G : Set.Iic j ⥤ E) (k : J) (hk : k ≤ j)
          (h : F.obj ⟨k, hk⟩ = G.obj ⟨k, hk⟩) :
          aMap F k k le_rfl hk = aMap G k k le_rfl hk := by
        change Arrow.mk (F.map (𝟙 ⟨k, hk⟩)) = Arrow.mk (G.map (𝟙 ⟨k, hk⟩))
        rw [F.map_id, G.map_id, h]
      have mapEq_trans {j : J} (F G : Set.Iic j ⥤ E) {a b d : J}
          (hab : a ≤ b) (hbd : b ≤ d) {hd : d ≤ j}
          (h₁ : aMap F a b hab (hbd.trans hd) = aMap G a b hab (hbd.trans hd))
          (h₂ : aMap F b d hbd hd = aMap G b d hbd hd) :
          aMap F a d (hab.trans hbd) hd = aMap G a d (hab.trans hbd) hd := by
        obtain ⟨ha, hb, hw₁⟩ := (Arrow.mk_eq_mk_iff _ _).1 h₁
        obtain ⟨hb', hd', hw₂⟩ := (Arrow.mk_eq_mk_iff _ _).1 h₂
        apply Arrow.ext ha hd'
        change F.map (homOfLE (hab.trans hbd) : ⟨a, _⟩ ⟶ ⟨d, _⟩) =
          eqToHom ha ≫ G.map (homOfLE (hab.trans hbd)) ≫ eqToHom hd'.symm
        rw [← homOfLE_comp (y := ⟨b, hbd.trans hd⟩) hab hbd]
        simp only [Functor.map_comp, hw₁, hw₂, Category.assoc, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp]
      have prefix_eq : ∀ (j : J) (p q : Prefix j), p.1 = q.1 := by
        intro j
        induction j using SuccOrder.limitRecOn with
        | isMin j hj =>
          obtain rfl := hj.eq_bot
          intro p q
          apply Arrow.functor_ext
          rintro ⟨a, ha⟩ ⟨b, hb⟩ f
          obtain rfl : b = ⊥ := le_antisymm hb bot_le
          obtain rfl : a = ⊥ := le_antisymm ha bot_le
          exact mapEq_refl p.1 q.1 ⊥ le_rfl (p.2.1.trans q.2.1.symm)
        | succ j hj ih =>
          intro p q
          have he := ih (trunc p (Order.le_succ j)) (trunc q (Order.le_succ j))
          have he_obj := Functor.congr_obj he ⟨j, le_rfl⟩
          change p.1.obj ⟨j, Order.le_succ j⟩ = q.1.obj ⟨j, Order.le_succ j⟩ at he_obj
          have hbelow (a b : J) (hab : a ≤ b) (hb : b ≤ j) :
              aMap p.1 a b hab (hb.trans (Order.le_succ j)) =
                aMap q.1 a b hab (hb.trans (Order.le_succ j)) := by
            change aMap (trunc p (Order.le_succ j)).1 a b hab hb =
              aMap (trunc q (Order.le_succ j)).1 a b hab hb
            rw [he]
          have hlast : aMap p.1 j (Order.succ j) (Order.le_succ j) le_rfl =
              aMap q.1 j (Order.succ j) (Order.le_succ j) le_rfl := by
            rw [p.2.2.1 j (Order.lt_succ_of_not_isMax hj),
              q.2.2.1 j (Order.lt_succ_of_not_isMax hj), he_obj]
          apply Arrow.functor_ext
          rintro ⟨a, ha⟩ ⟨b, hb⟩ f
          change aMap p.1 a b (leOfHom f) hb = aMap q.1 a b (leOfHom f) hb
          obtain hb' | rfl := hb.lt_or_eq
          · exact hbelow a b (leOfHom f) ((Order.lt_succ_iff_of_not_isMax hj).1 hb')
          · by_cases ha' : a ≤ j
            · exact mapEq_trans p.1 q.1 ha' (Order.le_succ j)
                (hbelow a j ha' le_rfl) hlast
            · have ha'' : a = Order.succ j := le_antisymm ha
                ((Order.succ_le_iff_of_not_isMax hj).2 (lt_of_not_ge ha'))
              subst a
              exact mapEq_refl p.1 q.1 (Order.succ j) le_rfl
                (congrArg Comma.right hlast)
        | isSuccLimit j hj ih =>
          intro p q
          have hbelow (a b : J) (hab : a ≤ b) (hb : b < j) :
              aMap p.1 a b hab hb.le = aMap q.1 a b hab hb.le := by
            have he := ih b hb (trunc p hb.le) (trunc q hb.le)
            change aMap (trunc p hb.le).1 a b hab le_rfl =
              aMap (trunc q hb.le).1 a b hab le_rfl
            rw [he]
          have he : rLT (le_refl j) p.1 = rLT (le_refl j) q.1 := by
            apply Arrow.functor_ext
            rintro ⟨a, ha⟩ ⟨b, hb⟩ f
            exact hbelow a b (leOfHom f) hb
          apply Arrow.functor_ext
          rintro ⟨a, ha⟩ ⟨b, hb⟩ f
          change aMap p.1 a b (leOfHom f) hb = aMap q.1 a b (leOfHom f) hb
          obtain hb' | hb' := hb.lt_or_eq
          · exact hbelow a b (leOfHom f) hb'
          · subst b
            obtain ha' | ha' := ha.lt_or_eq
            · rw [p.2.2.2 j hj le_rfl a ha', q.2.2.2 j hj le_rfl a ha', he]
            · subst a
              apply mapEq_refl p.1 q.1 j le_rfl
              rw [obj_limit p j hj le_rfl, obj_limit q j hj le_rfl, he]
      have prefix_unique (j : J) : Subsingleton (Prefix j) :=
        ⟨fun p q => Subtype.ext (prefix_eq j p q)⟩
      have overlap_obj {i j : J} (p : Prefix i) (q : Prefix j)
          (k : J) (hk : k ≤ i) (hk' : k ≤ j) :
          p.1.obj ⟨k, hk⟩ = q.1.obj ⟨k, hk'⟩ :=
        Functor.congr_obj (prefix_eq k (trunc p hk) (trunc q hk')) ⟨k, le_rfl⟩
      have overlap_arrow {i j : J} (p : Prefix i) (q : Prefix j)
          (a b : J) (hab : a ≤ b) (hb : b ≤ i) (hb' : b ≤ j) :
          aMap p.1 a b hab hb = aMap q.1 a b hab hb' :=
        congrArg (fun F => aMap F a b hab le_rfl)
          (prefix_eq b (trunc p hb) (trunc q hb'))
      have overlap_map {i j : J} (p : Prefix i) (q : Prefix j)
          (a b : J) (hab : a ≤ b) (hb : b ≤ i) (hb' : b ≤ j) :
          p.1.map (homOfLE hab : ⟨a, hab.trans hb⟩ ⟶ ⟨b, hb⟩) =
            eqToHom (overlap_obj p q a (hab.trans hb) (hab.trans hb')) ≫
              q.1.map (homOfLE hab) ≫ eqToHom (overlap_obj p q b hb hb').symm := by
        have h := (Arrow.mk_eq_mk_iff _ _).1 (overlap_arrow p q a b hab hb hb')
        tauto
      let mapObj {i j : J} (p : Prefix i) (q : Prefix j)
          (a b : J) (hab : a ≤ b) (ha : a ≤ i) (hb : b ≤ j) (hij : i ≤ j) :
          p.1.obj ⟨a, ha⟩ ⟶ q.1.obj ⟨b, hb⟩ :=
        eqToHom (overlap_obj p q a ha (ha.trans hij)) ≫ q.1.map (homOfLE hab)
      have mapObj_arrow {i j : J} (p : Prefix i) (q : Prefix j)
          (a b : J) (hab : a ≤ b) (ha : a ≤ i) (hb : b ≤ j) (hij : i ≤ j) :
          Arrow.mk (mapObj p q a b hab ha hb hij) = aMap q.1 a b hab hb := by
        simp [mapObj, aMap]
      have mapObj_refl {j : J} (p : Prefix j) (a b : J) (hab : a ≤ b) (hb : b ≤ j) :
          mapObj p p a b hab (hab.trans hb) hb le_rfl = p.1.map (homOfLE hab) := by
        simp [mapObj]
      have mapObj_trans {i j k : J} (p : Prefix i) (q : Prefix j) (r : Prefix k)
          (a b d : J) (hab : a ≤ b) (hbd : b ≤ d)
          (ha : a ≤ i) (hb : b ≤ j) (hd : d ≤ k) (hij : i ≤ j) (hjk : j ≤ k) :
          mapObj p q a b hab ha hb hij ≫ mapObj q r b d hbd hb hd hjk =
            mapObj p r a d (hab.trans hbd) ha hd (hij.trans hjk) := by
        simp [mapObj, overlap_map q r a b hab hb (hb.trans hjk), ← Functor.map_comp]
      have prefix_bot : Nonempty (Prefix ⊥) := by
        refine ⟨⟨(Functor.const (Set.Iic (⊥ : J))).obj (𝟭 Prespectrum.{0}), rfl, ?_, ?_⟩⟩
        · intro i hi
          exact False.elim ((not_lt_of_ge bot_le) hi)
        · intro i hi hij
          exact False.elim ((not_lt_of_ge hij) hi.bot_lt)
      have prefix_succ (j : J) (hj : ¬ IsMax j) (p : Prefix j) :
          Nonempty (Prefix (Order.succ j)) := by
        let F : Set.Iio (Order.succ j) ⥤ E := {
          obj := fun i => p.1.obj ⟨i.1, (Order.lt_succ_iff_of_not_isMax hj).1 i.2⟩
          map := fun f => p.1.map (homOfLE (leOfHom f))
          map_id := by
            intro i
            simpa using p.1.map_id ⟨i.1, (Order.lt_succ_iff_of_not_isMax hj).1 i.2⟩
          map_comp := by
            intro a b d f g
            simpa using p.1.map_comp (homOfLE (leOfHom f)) (homOfLE (leOfHom g)) }
        let c : CategoryTheory.Limits.Cocone F := {
          pt := next (p.1.obj ⟨j, le_rfl⟩)
          ι := {
            app := fun i => p.1.map (homOfLE ((Order.lt_succ_iff_of_not_isMax hj).1 i.2)) ≫
              step (p.1.obj ⟨j, le_rfl⟩)
            naturality := by
              intro a b f
              change p.1.map (homOfLE (leOfHom f)) ≫
                (p.1.map (homOfLE _) ≫ step _) = (p.1.map (homOfLE _) ≫ step _) ≫ 𝟙 _
              rw [Category.comp_id, ← Category.assoc, ← Functor.map_comp, homOfLE_comp] } }
        obtain ⟨G, hobj, htop, harr, hleg⟩ := extend_cocone J (Order.succ j) F c
        have hgobj (i : J) (hi : i ≤ j) :
            G.obj ⟨i, hi.trans (Order.le_succ j)⟩ = p.1.obj ⟨i, hi⟩ :=
          hobj i ((Order.lt_succ_iff_of_not_isMax hj).2 hi)
        have hgarr (a b : J) (hab : a ≤ b) (hb : b ≤ j) :
            aMap G a b hab (hb.trans (Order.le_succ j)) = aMap p.1 a b hab hb :=
          harr a b hab ((Order.lt_succ_iff_of_not_isMax hj).2 hb)
        refine ⟨⟨G, (hgobj ⊥ bot_le).trans p.2.1, ?_, ?_⟩⟩
        · intro i hi
          have hi' := (Order.lt_succ_iff_of_not_isMax hj).1 hi
          obtain hi' | hi' := hi'.lt_or_eq
          · rw [hgarr i (Order.succ i) (Order.le_succ i) (Order.succ_le_of_lt hi'),
              p.2.2.1 i hi', hgobj i hi'.le]
          · subst i
            change aMap G j (Order.succ j) (Order.le_succ j) le_rfl = _
            apply (hleg j (Order.lt_succ_of_not_isMax hj)).trans
            change Arrow.mk (p.1.map (𝟙 ⟨j, le_rfl⟩) ≫ step _) = _
            rw [p.1.map_id, Category.id_comp, hgobj j le_rfl]
        · intro i hi hij k hk
          have hij' := (Order.IsSuccLimit.le_succ_iff hi).1 hij
          have he : rLT hij G = rLT hij' p.1 := by
            apply Arrow.functor_ext
            rintro ⟨a, ha⟩ ⟨b, hb⟩ f
            exact hgarr a b (leOfHom f) (hb.le.trans hij')
          rw [hgarr k i hk.le hij', p.2.2.2 i hi hij' k hk, he]
      have prefix_limit (j : J) (hj : Order.IsSuccLimit j)
          (p : ∀ (i : J), i < j → Prefix i) : Nonempty (Prefix j) := by
        let F : Set.Iio j ⥤ E := {
          obj := fun i => (p i.1 i.2).1.obj ⟨i.1, le_rfl⟩
          map := fun {a b} f => mapObj (p a.1 a.2) (p b.1 b.2)
            a.1 b.1 (leOfHom f) le_rfl le_rfl (leOfHom f)
          map_id := by
            intro i
            rw [mapObj_refl]
            exact (p i.1 i.2).1.map_id _
          map_comp := by
            intro a b d f g
            exact (mapObj_trans (p a.1 a.2) (p b.1 b.2) (p d.1 d.2)
              a.1 b.1 d.1 (leOfHom f) (leOfHom g) le_rfl le_rfl le_rfl
              (leOfHom f) (leOfHom g)).symm }
        obtain ⟨G, hobj, htop, harr, hleg⟩ := extend_cocone J j F (limC j F)
        have hgobj (i : J) (hi : i < j) {k : J} (q : Prefix k) (hik : i ≤ k) :
            G.obj ⟨i, hi.le⟩ = q.1.obj ⟨i, hik⟩ :=
          (hobj i hi).trans (overlap_obj (p i hi) q i le_rfl hik)
        have hgarr (a b : J) (hab : a ≤ b) (hb : b < j) :
            aMap G a b hab hb.le = aMap (p b hb).1 a b hab le_rfl :=
          (harr a b hab hb).trans
            (mapObj_arrow (p a (lt_of_le_of_lt hab hb)) (p b hb)
              a b hab le_rfl le_rfl hab)
        refine ⟨⟨G, (hobj ⊥ hj.bot_lt).trans (p ⊥ hj.bot_lt).2.1, ?_, ?_⟩⟩
        · intro i hi
          have hs := (Order.IsSuccLimit.succ_lt_iff hj).2 hi
          have his := Order.lt_succ_of_not_isMax (not_isMax_of_lt hi)
          rw [hgarr i (Order.succ i) (Order.le_succ i) hs,
            (p (Order.succ i) hs).2.2.1 i his,
            hgobj i hi (p (Order.succ i) hs) (Order.le_succ i)]
        · intro i hi hij k hk
          obtain hij' | hij' := hij.lt_or_eq
          · have he : rLT hij G = rLT (le_refl i) (p i hij').1 := by
              apply Arrow.functor_ext
              rintro ⟨a, ha⟩ ⟨b, hb⟩ f
              exact (hgarr a b (leOfHom f) (hb.trans hij')).trans
                (overlap_arrow (p b (hb.trans hij')) (p i hij')
                  a b (leOfHom f) le_rfl hb.le)
            rw [hgarr k i hk.le hij', (p i hij').2.2.2 i hi le_rfl k hk, he]
          · subst i
            have he : rLT (le_refl j) G = F := by
              apply Arrow.functor_ext
              rintro ⟨a, ha⟩ ⟨b, hb⟩ f
              exact harr a b (leOfHom f) hb
            apply (hleg k hk).trans
            rw [he]
      have prefix_exists (j : J) : Nonempty (Prefix j) := by
        induction j using SuccOrder.limitRecOn with
        | isMin j hj => obtain rfl := hj.eq_bot; exact prefix_bot
        | succ j hj ih => exact prefix_succ j hj ih.some
        | isSuccLimit j hj ih => exact prefix_limit j hj (fun i hi => (ih i hi).some)
      let p (j : J) : Prefix j := (prefix_exists j).some
      let D : J ⥤ E := {
        obj := fun j => (p j).1.obj ⟨j, le_rfl⟩
        map := fun {i j} f => mapObj (p i) (p j) i j (leOfHom f) le_rfl le_rfl (leOfHom f)
        map_id := by
          intro i
          rw [mapObj_refl]
          exact (p i).1.map_id _
        map_comp := by
          intro a b d f g
          exact (mapObj_trans (p a) (p b) (p d) a b d
            (leOfHom f) (leOfHom g) le_rfl le_rfl le_rfl (leOfHom f) (leOfHom g)).symm }
      have hDarr (a b : J) (hab : a ≤ b) :
          Arrow.mk (D.map (homOfLE hab)) = aMap (p b).1 a b hab le_rfl :=
        mapObj_arrow (p a) (p b) a b hab le_rfl le_rfl hab
      refine ⟨D, (p ⊥).2.1, ?_, ?_⟩
      · intro i hi
        rw [hDarr i (Order.succ i) (Order.le_succ i),
          (p (Order.succ i)).2.2.1 i (Order.lt_succ_of_not_isMax hi)]
        change Arrow.mk (step ((p (Order.succ i)).1.obj ⟨i, Order.le_succ i⟩)) =
          Arrow.mk (step ((p i).1.obj ⟨i, le_rfl⟩))
        rw [overlap_obj (p (Order.succ i)) (p i) i (Order.le_succ i) le_rfl]
      · intro j hj
        have he : below J j ⋙ D = rLT (le_refl j) (p j).1 := by
          apply Arrow.functor_ext
          rintro ⟨a, ha⟩ ⟨b, hb⟩ f
          exact (hDarr a b (leOfHom f)).trans
            (overlap_arrow (p b) (p j) a b (leOfHom f) le_rfl hb.le)
        refine ⟨limC j (below J j ⋙ D), limC_isColimit _ _, limC_eval _ _, ?_⟩
        intro i hi
        rw [he, hDarr i j hi.le, (p j).2.2.2 j hj le_rfl i hi]
    have chain_colimit_at (J : Type) [LinearOrder J] [Nonempty J]
        (F : J ⥤ Prespectrum.{0})
        (hF : ∀ {i j : J} (f : i ⟶ j) n, IsClosedEmbedding ((F.map f).level n))
        (c : CategoryTheory.Limits.Cocone F) (hc : CategoryTheory.Limits.IsColimit c) :
        ∀ j n, IsClosedEmbedding ((c.ι.app j).level n) := by
      obtain ⟨c₀, ⟨hc₀⟩, hclosed, _⟩ := chain_colimit J F hF
      let e := hc₀.coconePointUniqueUpToIso hc
      intro j n
      have he := hc₀.comp_coconePointUniqueUpToIso_hom hc j
      have h := (iso_level_closed e n).comp (hclosed j n)
      change IsClosedEmbedding (((c₀.ι.app j) ≫ e.hom).level n) at h
      exact (congrArg (fun f : F.obj j ⟶ c.pt => IsClosedEmbedding (f.level n)) he).mp h
    have iteration_closed (J : Type) [LinearOrder J] [SuccOrder J]
        [OrderBot J] [WellFoundedLT J] (T : Prespectrum.{0} ⥤ Prespectrum.{0})
        (η : 𝟭 Prespectrum.{0} ⟶ T)
        (hη : ∀ X n, IsClosedEmbedding ((η.app X).level n))
        (D : J ⥤ (Prespectrum.{0} ⥤ Prespectrum.{0}))
        (hsucc : ∀ (i : J) (hi : ¬ IsMax i),
          Arrow.mk (D.map (homOfLE (Order.le_succ i))) =
            Arrow.mk (Functor.whiskerLeft (D.obj i) η))
        (hlimit : ∀ (j : J) (hj : Order.IsSuccLimit j),
          ∃ c : CategoryTheory.Limits.Cocone (below J j ⋙ D),
            Nonempty (CategoryTheory.Limits.IsColimit c) ∧
            (∀ X : Prespectrum.{0}, Nonempty (CategoryTheory.Limits.IsColimit
              (((evaluation Prespectrum.{0} Prespectrum.{0}).obj X).mapCocone c))) ∧
            ∀ (i : J) (hi : i < j), Arrow.mk (c.ι.app ⟨i, hi⟩) =
              Arrow.mk (D.map (homOfLE hi.le))) :
        ∀ {i j : J} (f : i ⟶ j) (X : Prespectrum.{0}) n,
          IsClosedEmbedding (((D.map f).app X).level n) := by
      have harrow {A B C E : Prespectrum.{0} ⥤ Prespectrum.{0}}
          {f : A ⟶ B} {g : C ⟶ E} (h : Arrow.mk f = Arrow.mk g)
          (X : Prespectrum.{0}) (n : ℕ) :
          IsClosedEmbedding ((f.app X).level n) ↔ IsClosedEmbedding ((g.app X).level n) := by
        exact Iff.of_eq (congrArg
          (fun a : Arrow (Prespectrum.{0} ⥤ Prespectrum.{0}) =>
            IsClosedEmbedding ((a.hom.app X).level n)) h)
      have h (j : J) : ∀ (i : J) (hij : i ≤ j) (X : Prespectrum.{0}) n,
          IsClosedEmbedding (((D.map (homOfLE hij)).app X).level n) := by
        induction j using SuccOrder.limitRecOn with
        | isMin j hj =>
          obtain rfl := hj.eq_bot
          intro i hi X n
          obtain rfl : i = ⊥ := le_antisymm hi bot_le
          change IsClosedEmbedding (((D.map (𝟙 (⊥ : J))).app X).level n)
          rw [D.map_id]
          exact IsClosedEmbedding.id
        | succ j hj ih =>
          intro i hi X n
          obtain hi' | hi' := hi.lt_or_eq
          · have hij := (Order.lt_succ_iff_of_not_isMax hj).1 hi'
            have hlast := (harrow (hsucc j hj) X n).2 (hη ((D.obj j).obj X) n)
            have hc := hlast.comp (ih i hij X n)
            change IsClosedEmbedding
              ((((D.map (homOfLE hij)) ≫ D.map (homOfLE (Order.le_succ j))).app X).level n) at hc
            rwa [← D.map_comp, homOfLE_comp] at hc
          · subst i
            change IsClosedEmbedding (((D.map (𝟙 (Order.succ j))).app X).level n)
            rw [D.map_id]
            exact IsClosedEmbedding.id
        | isSuccLimit j hj ih =>
          intro i hi X n
          obtain hi' | hi' := hi.lt_or_eq
          · obtain ⟨c, _, hc, hleg⟩ := hlimit j hj
            letI : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
            let ev := (evaluation Prespectrum.{0} Prespectrum.{0}).obj X
            have hf : ∀ {a b : Set.Iio j} (f : a ⟶ b) m,
                IsClosedEmbedding (((below J j ⋙ D) ⋙ ev).map f |>.level m) := by
              intro a b f m
              exact ih b.1 b.2 a.1 (leOfHom f) X m
            have hc' := chain_colimit_at (Set.Iio j) ((below J j ⋙ D) ⋙ ev)
              hf (ev.mapCocone c) (hc X).some ⟨i, hi'⟩ n
            exact (harrow (hleg i hi') X n).1 hc'
          · subst i
            change IsClosedEmbedding (((D.map (𝟙 j)).app X).level n)
            rw [D.map_id]
            exact IsClosedEmbedding.id
      intro i j f X n
      exact h j i (leOfHom f) X n
    have regular_bound (S : Type) (A : S → Prespectrum.{0}) :
        ∃ κ : Cardinal.{0}, κ.IsRegular ∧ ∀ s, Cardinal.mk (Σ n, (A s).level n) < κ := by
      let μ : Cardinal.{0} := max Cardinal.aleph0 (Cardinal.mk (Σ s, Σ n, (A s).level n))
      refine ⟨Order.succ μ, Cardinal.isRegular_succ (le_max_left _ _), ?_⟩
      intro s
      have hs : Cardinal.mk (Σ n, (A s).level n) ≤ Cardinal.mk (Σ s, Σ n, (A s).level n) :=
        Cardinal.mk_le_of_injective
          (f := fun x : Σ n, (A s).level n => (⟨s, x⟩ : Σ t, Σ n, (A t).level n))
          (by intro x y h; exact @sigma_mk_injective S (fun t => Σ n, (A t).level n) s x y h)
      exact (hs.trans (le_max_right _ _)).trans_lt (Order.lt_succ μ)
    have small_object_at (S : Type) (A B : S → Prespectrum.{0}) (j : ∀ s, A s ⟶ B s)
        (hj : ∀ s n, IsClosedEmbedding ((j s).level n))
        (κ : Cardinal.{0}) (hκ : κ.IsRegular)
        [OrderBot κ.ord.ToType] [NoMaxOrder κ.ord.ToType]
        (hA : ∀ s, Cardinal.mk (Σ n, (A s).level n) < κ) :
        ∃ (D : κ.ord.ToType ⥤ (Prespectrum.{0} ⥤ Prespectrum.{0}))
          (h₀ : D.obj ⊥ = 𝟭 Prespectrum.{0}) (c : CategoryTheory.Limits.Cocone D),
          Nonempty (CategoryTheory.Limits.IsColimit c) ∧
          (∀ X : Prespectrum.{0}, Nonempty (CategoryTheory.Limits.IsColimit
            (((evaluation Prespectrum.{0} Prespectrum.{0}).obj X).mapCocone c))) ∧
          (∀ X n, IsClosedEmbedding ((((eqToHom h₀.symm ≫ c.ι.app ⊥).app X)).level n)) ∧
          (∀ (X : Prespectrum.{0}) (s : S) (a : A s ⟶ c.pt.obj X),
            ∃ b : B s ⟶ c.pt.obj X, j s ≫ b = a) ∧
          (∀ (i : κ.ord.ToType) (X : Prespectrum.{0}),
            cell_step S A B j ((D.map (homOfLE (Order.le_succ i))).app X)) ∧
          (∀ {i k : κ.ord.ToType} (f : i ⟶ k) (X : Prespectrum.{0}) n,
            IsClosedEmbedding (((D.map f).app X).level n)) ∧
          ∀ (k : κ.ord.ToType) (hk : Order.IsSuccLimit k),
            ∃ cₖ : CategoryTheory.Limits.Cocone (below κ.ord.ToType k ⋙ D),
              Nonempty (CategoryTheory.Limits.IsColimit cₖ) ∧
              (∀ X : Prespectrum.{0}, Nonempty (CategoryTheory.Limits.IsColimit
                (((evaluation Prespectrum.{0} Prespectrum.{0}).obj X).mapCocone cₖ))) ∧
              ∀ (i : κ.ord.ToType) (hi : i < k), Arrow.mk (cₖ.ι.app ⟨i, hi⟩) =
                Arrow.mk (D.map (homOfLE hi.le)) := by
      obtain ⟨T, η, hclosed, hfill, hcell⟩ := attach_step S A B j hj
      obtain ⟨D, h₀, hsucc, hlimit⟩ := transfinite_iteration κ.ord.ToType T η
      obtain ⟨c, hc, hcX⟩ := functor_colimit κ.ord.ToType D
      have hD {i k : κ.ord.ToType} (f : i ⟶ k) (X : Prespectrum.{0}) (n : ℕ) :
          IsClosedEmbedding (((D.map f).app X).level n) :=
        iteration_closed κ.ord.ToType T η hclosed D hsucc hlimit f X n
      refine ⟨D, h₀, c, hc, hcX, ?_, ?_, ?_, hD, hlimit⟩
      · intro X n
        let ev := (evaluation Prespectrum.{0} Prespectrum.{0}).obj X
        have hleg := chain_colimit_at κ.ord.ToType (D ⋙ ev)
          (fun {i k} f m => hD f X m) (ev.mapCocone c) (hcX X).some ⊥ n
        let e : X ≅ (D.obj ⊥).obj X := ev.mapIso (eqToIso h₀.symm)
        exact hleg.comp (iso_level_closed e n)
      · intro X s a
        let ev := (evaluation Prespectrum.{0} Prespectrum.{0}).obj X
        obtain ⟨i, g, hg⟩ := small_source_at κ hκ (D ⋙ ev)
          (fun {i k} f n => hD f X n) (A s) (hA s) (ev.mapCocone c) (hcX X).some a
        have hExt : ∀ a' : A s ⟶ (D.obj i).obj X,
            ∃ b : B s ⟶ (D.obj (Order.succ i)).obj X,
              j s ≫ b = a' ≫ (D.map (homOfLE (Order.le_succ i))).app X := by
          have he := congrArg
            (fun ar : Arrow (Prespectrum.{0} ⥤ Prespectrum.{0}) =>
              ∀ a' : A s ⟶ ar.left.obj X, ∃ b : B s ⟶ ar.right.obj X,
                j s ≫ b = a' ≫ ar.hom.app X) (hsucc i (by simp))
          exact he.mpr (hfill ((D.obj i).obj X) s)
        obtain ⟨b, hb⟩ := hExt g
        have hw : (D.map (homOfLE (Order.le_succ i))).app X ≫
            (c.ι.app (Order.succ i)).app X = (c.ι.app i).app X := by
          exact NatTrans.congr_app (c.w (homOfLE (Order.le_succ i))) X
        refine ⟨b ≫ (c.ι.app (Order.succ i)).app X, ?_⟩
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun f : A s ⟶ (D.obj (Order.succ i)).obj X =>
            f ≫ (c.ι.app (Order.succ i)).app X) hb).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun f : (D.obj i).obj X ⟶ c.pt.obj X => g ≫ f) hw).trans hg)))
      · intro i X
        have he := congrArg
          (fun ar : Arrow (Prespectrum.{0} ⥤ Prespectrum.{0}) => cell_step S A B j (ar.hom.app X))
          (hsucc i (by simp))
        exact he.mpr (hcell ((D.obj i).obj X))
    have small_object (S : Type) (A B : S → Prespectrum.{0}) (j : ∀ s, A s ⟶ B s)
        (hj : ∀ s n, IsClosedEmbedding ((j s).level n)) :
        ∃ R : Prespectrum.{0} ⥤ Prespectrum.{0}, ∃ η : 𝟭 _ ⟶ R,
          (∀ X n, IsClosedEmbedding ((η.app X).level n)) ∧
          ∀ (X : Prespectrum.{0}) (s : S) (a : A s ⟶ R.obj X),
            ∃ b : B s ⟶ R.obj X, j s ≫ b = a := by
      obtain ⟨κ, hκ, hA⟩ := regular_bound S A
      letI : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType hκ.ne_zero
      letI : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
      letI : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder hκ.aleph0_le
      obtain ⟨D, h₀, c, _, _, hclosed, hfill, _⟩ := small_object_at S A B j hj κ hκ hA
      exact ⟨c.pt, eqToHom h₀.symm ≫ c.ι.app ⊥, hclosed, hfill⟩
    -- Markdown IV, Ω-1: the ordinary parameter tensor, including an empty parameter space.
    let tensorRaw (A : BasedSpace.{0}) (K : TopCat.{0}) := Unit ⊕ (A × K)
    let tensorCollapsed (A : BasedSpace.{0}) (K : TopCat.{0}) : tensorRaw A K → Prop :=
      Sum.elim (fun _ => True) (fun p => p.1 = A.point)
    let tensorRel (A : BasedSpace.{0}) (K : TopCat.{0}) (a b : tensorRaw A K) : Prop :=
      tensorCollapsed A K a ∧ tensorCollapsed A K b
    let tensorSpace (A : BasedSpace.{0}) (K : TopCat.{0}) : BasedSpace.{0} :=
      ⟨TopCat.of (Quot (tensorRel A K)), Quot.mk _ (Sum.inl ())⟩
    let tensorPoint (A : BasedSpace.{0}) (K : TopCat.{0}) (a : A) (k : K) : tensorSpace A K :=
      Quot.mk _ (Sum.inr (a, k))
    have tensorPoint_point (A : BasedSpace.{0}) (K : TopCat.{0}) (k : K) :
        tensorPoint A K A.point k = (tensorSpace A K).point :=
      Quot.sound ⟨rfl, trivial⟩
    have tensorPoint_continuous (A : BasedSpace.{0}) (K : TopCat.{0}) :
        Continuous (fun p : A × K => tensorPoint A K p.1 p.2) :=
      continuous_quot_mk.comp continuous_inr
    let tensorBond (X : Prespectrum.{0}) (K : TopCat.{0}) (n : ℕ) :
        C(tensorSpace (X.level n) K × I, tensorSpace (X.level (n + 1)) K) := by
      let raw : C(X.level n × K, C(I, tensorSpace (X.level (n + 1)) K)) :=
        (⟨fun p : (X.level n × K) × I =>
            tensorPoint (X.level (n + 1)) K (X.bond n (p.1.1, p.2)) p.1.2,
          (tensorPoint_continuous _ _).comp
            (((X.bond n).continuous.comp (continuous_fst.fst.prodMk continuous_snd)).prodMk
              continuous_fst.snd)⟩ :
          C((X.level n × K) × I, tensorSpace (X.level (n + 1)) K)).curry
      let raw' : C(tensorRaw (X.level n) K, C(I, tensorSpace (X.level (n + 1)) K)) :=
        ⟨Sum.elim (fun _ => ContinuousMap.const I (tensorSpace (X.level (n + 1)) K).point) raw,
          continuous_const.sumElim raw.continuous⟩
      have hcollapsed (a : tensorRaw (X.level n) K) (ha : tensorCollapsed (X.level n) K a) :
          raw' a = ContinuousMap.const I (tensorSpace (X.level (n + 1)) K).point := by
        cases a with
        | inl u => rfl
        | inr p =>
          apply ContinuousMap.ext
          intro t
          change tensorPoint (X.level (n + 1)) K (X.bond n (p.1, t)) p.2 = _
          change p.1 = (X.level n).point at ha
          rw [ha, X.bond_point, tensorPoint_point]
          rfl
      have hrel (a b : tensorRaw (X.level n) K) (h : tensorRel (X.level n) K a b) :
          raw' a = raw' b := (hcollapsed a h.1).trans (hcollapsed b h.2).symm
      exact (⟨Quot.lift raw' hrel, continuous_quot_lift hrel raw'.continuous⟩ :
        C(tensorSpace (X.level n) K, C(I, tensorSpace (X.level (n + 1)) K))).uncurry
    have tensorBond_point (X : Prespectrum.{0}) (K : TopCat.{0}) (n : ℕ) (t : I) :
        tensorBond X K n ((tensorSpace (X.level n) K).point, t) =
          (tensorSpace (X.level (n + 1)) K).point := rfl
    have tensorBond_tensorPoint (X : Prespectrum.{0}) (K : TopCat.{0}) (n : ℕ)
        (x : X.level n) (k : K) (t : I) :
        tensorBond X K n (tensorPoint (X.level n) K x k, t) =
          tensorPoint (X.level (n + 1)) K (X.bond n (x, t)) k := rfl
    have tensorBond_endpoint (X : Prespectrum.{0}) (K : TopCat.{0}) (n : ℕ)
        (t : I) (ht : t = 0 ∨ t = 1) (x : tensorSpace (X.level n) K) :
        tensorBond X K n (x, t) = (tensorSpace (X.level (n + 1)) K).point := by
      induction x using Quot.inductionOn with | h a
      cases a with
      | inl u => cases u; rfl
      | inr p =>
        change tensorBond X K n (tensorPoint (X.level n) K p.1 p.2, t) = _
        rw [tensorBond_tensorPoint]
        rcases ht with rfl | rfl
        · rw [X.bond_zero, tensorPoint_point]
        · rw [X.bond_one, tensorPoint_point]
    let tensor (X : Prespectrum.{0}) (K : TopCat.{0}) : Prespectrum.{0} := {
      level := fun n => tensorSpace (X.level n) K
      bond := tensorBond X K
      bond_point := tensorBond_point X K
      bond_zero := fun n x => tensorBond_endpoint X K n 0 (Or.inl rfl) x
      bond_one := fun n x => tensorBond_endpoint X K n 1 (Or.inr rfl) x }
    let tensorSpaceMap {A B : BasedSpace.{0}} {K L : TopCat.{0}}
        (f : A ⟶ B) (g : C(K, L)) : tensorSpace A K ⟶ tensorSpace B L := by
      let raw : C(tensorRaw A K, tensorSpace B L) :=
        ⟨Sum.elim (fun _ => (tensorSpace B L).point)
          (fun p => tensorPoint B L (f.map p.1) (g p.2)),
          continuous_const.sumElim ((tensorPoint_continuous B L).comp
            ((f.map.continuous.comp continuous_fst).prodMk (g.continuous.comp continuous_snd)))⟩
      have hcollapsed (a : tensorRaw A K) (ha : tensorCollapsed A K a) :
          raw a = (tensorSpace B L).point := by
        cases a with
        | inl u => rfl
        | inr p =>
          change tensorPoint B L (f.map p.1) (g p.2) = _
          change p.1 = A.point at ha
          rw [ha, f.point, tensorPoint_point]
      have hrel (a b : tensorRaw A K) (h : tensorRel A K a b) : raw a = raw b :=
        (hcollapsed a h.1).trans (hcollapsed b h.2).symm
      exact ⟨⟨Quot.lift raw hrel, continuous_quot_lift hrel raw.continuous⟩, rfl⟩
    have tensorSpaceMap_tensorPoint {A B : BasedSpace.{0}} {K L : TopCat.{0}}
        (f : A ⟶ B) (g : C(K, L)) (a : A) (k : K) :
        (tensorSpaceMap f g).map (tensorPoint A K a k) =
          tensorPoint B L (f.map a) (g k) := rfl
    let tensorMap {X Y : Prespectrum.{0}} {K L : TopCat.{0}}
        (f : X ⟶ Y) (g : C(K, L)) : tensor X K ⟶ tensor Y L := {
      level := fun n => (tensorSpaceMap (⟨f.level n, f.point n⟩ : X.level n ⟶ Y.level n) g).map
      point := fun _ => rfl
      bond := by
        intro n x t
        induction x using Quot.inductionOn with | h a
        cases a with
        | inl u => cases u; rfl
        | inr p =>
          change tensorPoint (Y.level (n + 1)) L ((f.level (n + 1)) (X.bond n (p.1, t))) (g p.2) =
            tensorPoint (Y.level (n + 1)) L (Y.bond n (f.level n p.1, t)) (g p.2)
          rw [f.bond] }
    have tensorMap_tensorPoint {X Y : Prespectrum.{0}} {K L : TopCat.{0}}
        (f : X ⟶ Y) (g : C(K, L)) (n : ℕ) (x : X.level n) (k : K) :
        (tensorMap f g).level n (tensorPoint (X.level n) K x k) =
          tensorPoint (Y.level n) L (f.level n x) (g k) := rfl
    have tensor_hom_ext {X Y : Prespectrum.{0}} {K : TopCat.{0}}
        (f g : tensor X K ⟶ Y)
        (h : ∀ n (x : X.level n) (k : K),
          f.level n (tensorPoint (X.level n) K x k) = g.level n (tensorPoint (X.level n) K x k)) :
        f = g := by
      apply Prespectrum.Hom.ext
      funext n
      apply ContinuousMap.ext
      intro z
      induction z using Quot.inductionOn with | h a
      cases a with
      | inl u => cases u; exact (f.point n).trans (g.point n).symm
      | inr p => exact h n p.1 p.2
    have tensorMap_id (X : Prespectrum.{0}) (K : TopCat.{0}) :
        tensorMap (𝟙 X) (ContinuousMap.id K) = 𝟙 (tensor X K) := by
      apply tensor_hom_ext
      intro n x k
      rfl
    have tensorMap_comp {X Y Z : Prespectrum.{0}} {K L M : TopCat.{0}}
        (f : X ⟶ Y) (f' : Y ⟶ Z) (g : C(K, L)) (g' : C(L, M)) :
        tensorMap (f ≫ f') (g'.comp g) = tensorMap f g ≫ tensorMap f' g' := by
      apply tensor_hom_ext
      intro n x k
      rfl
    let tensorFunctor (K : TopCat.{0}) : Prespectrum.{0} ⥤ Prespectrum.{0} := {
      obj := fun X => tensor X K
      map := fun f => tensorMap f (ContinuousMap.id K)
      map_id := fun X => tensorMap_id X K
      map_comp := fun f g => tensorMap_comp f g (ContinuousMap.id K) (ContinuousMap.id K) }
    let tensorParameter {K L : TopCat.{0}} (g : C(K, L)) : tensorFunctor K ⟶ tensorFunctor L := {
      app := fun X => tensorMap (𝟙 X) g
      naturality := by
        intro X Y f
        apply tensor_hom_ext
        intro n x k
        rfl }
    let tensorInclusion (K : TopCat.{0}) (k : K) : 𝟭 Prespectrum.{0} ⟶ tensorFunctor K := {
      app := fun X => {
        level := fun n => ⟨fun x => tensorPoint (X.level n) K x k,
          (tensorPoint_continuous _ _).comp (continuous_id.prodMk continuous_const)⟩
        point := fun n => tensorPoint_point _ _ k
        bond := fun _ _ _ => rfl }
      naturality := by
        intro X Y f
        apply Prespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        rfl }
    let tensorSpaceDesc (A : BasedSpace.{0}) (K : TopCat.{0}) (B : BasedSpace.{0})
        (f : C(A × K, B)) (hf : ∀ k, f (A.point, k) = B.point) : tensorSpace A K ⟶ B := by
      let raw : C(tensorRaw A K, B) :=
        ⟨Sum.elim (fun _ => B.point) f, continuous_const.sumElim f.continuous⟩
      have hc (a : tensorRaw A K) (ha : tensorCollapsed A K a) : raw a = B.point := by
        cases a with
        | inl u => rfl
        | inr p =>
          change f (p.1, p.2) = B.point
          change p.1 = A.point at ha
          rw [ha, hf]
      have hr (a b : tensorRaw A K) (h : tensorRel A K a b) : raw a = raw b :=
        (hc a h.1).trans (hc b h.2).symm
      exact ⟨⟨Quot.lift raw hr, continuous_quot_lift hr raw.continuous⟩, rfl⟩
    have tensorSpaceDesc_tensorPoint (A : BasedSpace.{0}) (K : TopCat.{0}) (B : BasedSpace.{0})
        (f : C(A × K, B)) (hf : ∀ k, f (A.point, k) = B.point) (a : A) (k : K) :
        (tensorSpaceDesc A K B f hf).map (tensorPoint A K a k) = f (a, k) := rfl
    have tensorSpace_hom_ext {A B : BasedSpace.{0}} {K : TopCat.{0}}
        (f g : tensorSpace A K ⟶ B)
        (h : ∀ (a : A) (k : K), f.map (tensorPoint A K a k) = g.map (tensorPoint A K a k)) :
        f = g := by
      apply BasedSpace.Hom.ext
      apply ContinuousMap.ext
      intro z
      induction z using Quot.inductionOn with | h a
      cases a with
      | inl u => cases u; exact f.point.trans g.point.symm
      | inr p => exact h p.1 p.2
    let suspensionDesc (A B : BasedSpace.{0}) (f : C(A × I, B))
        (hf : ∀ p, BasedSpace.SuspensionCollapsed A p → f p = B.point) : A.suspension ⟶ B := by
      have hr (a b : A × I) (h : BasedSpace.SuspensionRelation A a b) : f a = f b :=
        (hf a h.1).trans (hf b h.2).symm
      exact ⟨⟨Quot.lift f hr, continuous_quot_lift hr f.continuous⟩,
        hf (A.point, 0) (Or.inl rfl)⟩
    have suspensionDesc_projection (A B : BasedSpace.{0}) (f : C(A × I, B))
        (hf : ∀ p, BasedSpace.SuspensionCollapsed A p → f p = B.point) (a : A) (t : I) :
        (suspensionDesc A B f hf).map (BasedSpace.suspensionProjection A (a, t)) = f (a, t) := rfl
    let tensorSuspForward (A : BasedSpace.{0}) (K : TopCat.{0}) [LocallyCompactSpace K] :
        tensorSpace A.suspension K ⟶ (tensorSpace A K).suspension := by
      let raw (q : A × I) (k : K) : (tensorSpace A K).suspension :=
        BasedSpace.suspensionProjection (tensorSpace A K) (tensorPoint A K q.1 k, q.2)
      have hc (q : A × I) (hq : BasedSpace.SuspensionCollapsed A q) (k : K) :
          raw q k = (tensorSpace A K).suspension.point := by
        apply BasedSpace.suspensionProjection_collapsed
        rcases hq with hq | hq | hq
        · exact Or.inl (hq ▸ tensorPoint_point A K k)
        · exact Or.inr (Or.inl hq)
        · exact Or.inr (Or.inr hq)
      have hr (k : K) (q r : A × I) (h : BasedSpace.SuspensionRelation A q r) :
          raw q k = raw r k := (hc q h.1 k).trans (hc r h.2 k).symm
      let f : C(A.suspension × K, (tensorSpace A K).suspension) :=
        ⟨fun p => Quot.lift (fun q => raw q p.2) (hr p.2) p.1, by
          apply isQuotientMap_quot_mk.continuous_lift_prod_left
          exact (BasedSpace.suspensionProjection (tensorSpace A K)).continuous.comp
            (((tensorPoint_continuous A K).comp
              (continuous_fst.fst.prodMk continuous_snd)).prodMk continuous_fst.snd)⟩
      exact tensorSpaceDesc A.suspension K (tensorSpace A K).suspension f
        (fun k => hc (A.point, 0) (Or.inl rfl) k)
    have tensorSuspForward_point (A : BasedSpace.{0}) (K : TopCat.{0}) [LocallyCompactSpace K]
        (a : A) (k : K) (t : I) :
        (tensorSuspForward A K).map (tensorPoint A.suspension K
          (BasedSpace.suspensionProjection A (a, t)) k) =
        BasedSpace.suspensionProjection (tensorSpace A K) (tensorPoint A K a k, t) := rfl
    let tensorSuspBackward (A : BasedSpace.{0}) (K : TopCat.{0}) :
        (tensorSpace A K).suspension ⟶ tensorSpace A.suspension K :=
      suspensionDesc (tensorSpace A K) (tensorSpace A.suspension K)
        (tensorBond (Prespectrum.suspensionSpectrum A) K 0) (by
          intro p hp
          rcases hp with hp | hp | hp
          · change tensorBond (Prespectrum.suspensionSpectrum A) K 0 (p.1, p.2) = _
            rw [hp]
            exact tensorBond_point (Prespectrum.suspensionSpectrum A) K 0 p.2
          · exact tensorBond_endpoint (Prespectrum.suspensionSpectrum A) K 0 p.2 (Or.inl hp) p.1
          · exact tensorBond_endpoint (Prespectrum.suspensionSpectrum A) K 0 p.2 (Or.inr hp) p.1)
    have tensorSuspBackward_point (A : BasedSpace.{0}) (K : TopCat.{0})
        (a : A) (k : K) (t : I) :
        (tensorSuspBackward A K).map
          (BasedSpace.suspensionProjection (tensorSpace A K) (tensorPoint A K a k, t)) =
        tensorPoint A.suspension K (BasedSpace.suspensionProjection A (a, t)) k := rfl
    let tensorSuspIso (A : BasedSpace.{0}) (K : TopCat.{0}) [LocallyCompactSpace K] :
        tensorSpace A.suspension K ≅ (tensorSpace A K).suspension := {
      hom := tensorSuspForward A K
      inv := tensorSuspBackward A K
      hom_inv_id := by
        apply tensorSpace_hom_ext
        intro a k
        induction a using Quot.inductionOn with | h p
        change (tensorSuspBackward A K).map ((tensorSuspForward A K).map
          (tensorPoint A.suspension K (BasedSpace.suspensionProjection A (p.1, p.2)) k)) = _
        rw [tensorSuspForward_point, tensorSuspBackward_point]
        rfl
      inv_hom_id := by
        apply BasedSpace.Hom.ext
        apply ContinuousMap.ext
        intro z
        induction z using Quot.inductionOn with | h p
        rcases p with ⟨a, t⟩
        induction a using Quot.inductionOn with | h q
        cases q with
        | inl u =>
          cases u
          change (tensorSuspForward A K).map
            ((tensorSuspBackward A K).map (BasedSpace.suspensionProjection (tensorSpace A K)
              ((tensorSpace A K).point, t))) = _
          rw [BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl),
            (tensorSuspBackward A K).point, (tensorSuspForward A K).point]
          exact (BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)).symm
        | inr q =>
          change (tensorSuspForward A K).map ((tensorSuspBackward A K).map
            (BasedSpace.suspensionProjection (tensorSpace A K) (tensorPoint A K q.1 q.2, t))) = _
          rw [tensorSuspBackward_point, tensorSuspForward_point]
          rfl }
    -- Ω1: the specified free evaluation is natural; transports record its actual generating layer.
    let levelHom (n : ℕ) {X Y : Prespectrum.{0}} (f : X ⟶ Y) : X.level n ⟶ Y.level n :=
      ⟨f.level n, f.point n⟩
    have levelHom_comp (n : ℕ) {X Y Z : Prespectrum.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
        levelHom n (f ≫ g) = levelHom n f ≫ levelHom n g := rfl
    have free_level (n : ℕ) (A : BasedSpace.{0}) : (Prespectrum.free n A).level n = A := by
      induction n with
      | zero => rfl
      | succ n ih =>
        have hfree : Prespectrum.free (n + 1) A =
            Prespectrum.desuspension (Prespectrum.free n A) :=
          Function.iterate_succ_apply' Prespectrum.desuspension n (Prespectrum.suspensionSpectrum A)
        rw [hfree]
        exact ih
    have cast_comp_heq {A B C : BasedSpace.{0}} (h : A = B) (f : B ⟶ C) :
        HEq ((eqToHom h ≫ f).map) f.map := by
      cases h
      simpa only [eqToHom_refl, Category.id_comp] using (HEq.rfl : HEq f.map f.map)
    have free_eval_eq (n : ℕ) (A : BasedSpace.{0}) (X : Prespectrum.{0})
        (f : Prespectrum.free n A ⟶ X) : Prespectrum.freeEvaluation n A X f =
          eqToHom (free_level n A).symm ≫ levelHom n f := by
      apply BasedSpace.Hom.ext
      have hf : HEq (Prespectrum.freeEvaluation n A X f).map (f.level n) :=
        (Prespectrum.freeEvaluation_exists n A X).choose_spec f
      have hc : HEq ((eqToHom (free_level n A).symm ≫ levelHom n f).map) (f.level n) :=
        cast_comp_heq (free_level n A).symm (levelHom n f)
      exact eq_of_heq (hf.trans hc.symm)
    have free_eval_post (n : ℕ) (A : BasedSpace.{0}) {X Y : Prespectrum.{0}}
        (f : Prespectrum.free n A ⟶ X) (g : X ⟶ Y) :
        Prespectrum.freeEvaluation n A Y (f ≫ g) =
          Prespectrum.freeEvaluation n A X f ≫ levelHom n g := by
      rw [free_eval_eq n A Y (f ≫ g), free_eval_eq n A X f, levelHom_comp, Category.assoc]
    let freeGen (n : ℕ) (A : BasedSpace.{0}) : A ⟶ (Prespectrum.free n A).level n :=
      Prespectrum.freeEvaluation n A (Prespectrum.free n A) (𝟙 _)
    let freeMap (n : ℕ) {A B : BasedSpace.{0}} (f : A ⟶ B) :
        Prespectrum.free n A ⟶ Prespectrum.free n B :=
      (Prespectrum.freeEvaluation n A (Prespectrum.free n B)).symm (f ≫ freeGen n B)
    have freeMap_eval (n : ℕ) {A B : BasedSpace.{0}} (f : A ⟶ B) :
        Prespectrum.freeEvaluation n A (Prespectrum.free n B) (freeMap n f) = f ≫ freeGen n B :=
      (Prespectrum.freeEvaluation n A (Prespectrum.free n B)).apply_symm_apply _
    have gen_freeMap (n : ℕ) {A B : BasedSpace.{0}} (f : A ⟶ B) :
        freeGen n A ≫ levelHom n (freeMap n f) = f ≫ freeGen n B := by
      calc
        freeGen n A ≫ levelHom n (freeMap n f) =
          Prespectrum.freeEvaluation n A (Prespectrum.free n B) (𝟙 _ ≫ freeMap n f) :=
          (free_eval_post n A (𝟙 _) (freeMap n f)).symm
        _ = f ≫ freeGen n B := by rw [Category.id_comp]; exact freeMap_eval n f
    have freeMap_id (n : ℕ) (A : BasedSpace.{0}) : freeMap n (𝟙 A) = 𝟙 (Prespectrum.free n A) := by
      apply (Prespectrum.freeEvaluation n A (Prespectrum.free n A)).injective
      rw [freeMap_eval]
      exact Category.id_comp _
    have freeMap_comp (n : ℕ) {A B C : BasedSpace.{0}} (f : A ⟶ B) (g : B ⟶ C) :
        freeMap n (f ≫ g) = freeMap n f ≫ freeMap n g := by
      apply (Prespectrum.freeEvaluation n A (Prespectrum.free n C)).injective
      simp only [freeMap_eval, free_eval_post, Category.assoc, gen_freeMap]
    let freeFunctor (n : ℕ) : BasedSpace.{0} ⥤ Prespectrum.{0} := {
      obj := Prespectrum.free n
      map := freeMap n
      map_id := freeMap_id n
      map_comp := freeMap_comp n }
    have free_eval_pre (n : ℕ) {A B : BasedSpace.{0}} (f : A ⟶ B)
        (X : Prespectrum.{0}) (g : Prespectrum.free n B ⟶ X) :
        Prespectrum.freeEvaluation n A X (freeMap n f ≫ g) =
          f ≫ Prespectrum.freeEvaluation n B X g := by
      rw [free_eval_post, freeMap_eval, Category.assoc]
      have hg := free_eval_post n B (𝟙 _) g
      rw [Category.id_comp] at hg
      exact congrArg (fun h => f ≫ h) hg.symm
    have basedIso_hom_inv {A B : BasedSpace.{0}} (e : A ≅ B) (a : A) :
        e.inv.map (e.hom.map a) = a :=
      congrArg (fun f : A ⟶ A => f.map a) e.hom_inv_id
    have basedIso_inv_hom {A B : BasedSpace.{0}} (e : A ≅ B) (b : B) :
        e.hom.map (e.inv.map b) = b :=
      congrArg (fun f : B ⟶ B => f.map b) e.inv_hom_id
    let suspensionIso {A B : BasedSpace.{0}} (e : A ≅ B) : A.suspension ≅ B.suspension := {
      hom := BasedSpace.suspendMap e.hom
      inv := BasedSpace.suspendMap e.inv
      hom_inv_id := by
        apply BasedSpace.Hom.ext
        apply ContinuousMap.ext
        intro z
        induction z using Quot.inductionOn with | h p
        change BasedSpace.suspensionProjection A (e.inv.map (e.hom.map p.1), p.2) = _
        rw [basedIso_hom_inv]
        rfl
      inv_hom_id := by
        apply BasedSpace.Hom.ext
        apply ContinuousMap.ext
        intro z
        induction z using Quot.inductionOn with | h p
        change BasedSpace.suspensionProjection B (e.hom.map (e.inv.map p.1), p.2) = _
        rw [basedIso_inv_hom]
        rfl }
    let prespectrumIsoOfLevels {X Y : Prespectrum.{0}} (e : ∀ n, X.level n ≅ Y.level n)
        (he : ∀ n x t, (e (n + 1)).hom.map (X.bond n (x, t)) =
          Y.bond n ((e n).hom.map x, t)) : X ≅ Y := {
      hom := { level := fun n => (e n).hom.map, point := fun n => (e n).hom.point, bond := he }
      inv := {
        level := fun n => (e n).inv.map
        point := fun n => (e n).inv.point
        bond := by
          intro n y t
          have h := he n ((e n).inv.map y) t
          rw [basedIso_inv_hom] at h
          exact (congrArg (e (n + 1)).inv.map h).symm.trans
            (basedIso_hom_inv (e (n + 1)) _) }
      hom_inv_id := by
        apply Prespectrum.Hom.ext
        funext n
        exact congrArg BasedSpace.Hom.map (e n).hom_inv_id
      inv_hom_id := by
        apply Prespectrum.Hom.ext
        funext n
        exact congrArg BasedSpace.Hom.map (e n).inv_hom_id }
    let tensorIterIso (A : BasedSpace.{0}) (K : TopCat.{0}) [LocallyCompactSpace K] :
        ∀ n, tensorSpace (A.iterateSuspension n) K ≅ (tensorSpace A K).iterateSuspension n :=
      fun n => Nat.rec (Iso.refl _) (fun n e =>
        tensorSuspIso (A.iterateSuspension n) K ≪≫ suspensionIso e) n
    have tensorIterIso_bond (A : BasedSpace.{0}) (K : TopCat.{0}) [LocallyCompactSpace K]
        (n : ℕ) (a : A.iterateSuspension n) (k : K) (t : I) :
        (tensorIterIso A K (n + 1)).hom.map
          (tensorPoint (A.iterateSuspension (n + 1)) K
            (BasedSpace.suspensionProjection (A.iterateSuspension n) (a, t)) k) =
          BasedSpace.suspensionProjection ((tensorSpace A K).iterateSuspension n)
            ((tensorIterIso A K n).hom.map (tensorPoint (A.iterateSuspension n) K a k), t) := rfl
    let tensorSuspensionSpectrumIso (A : BasedSpace.{0}) (K : TopCat.{0}) [LocallyCompactSpace K] :
        tensor (Prespectrum.suspensionSpectrum A) K ≅ Prespectrum.suspensionSpectrum (tensorSpace A K) :=
      prespectrumIsoOfLevels (tensorIterIso A K) (by
        intro n x t
        induction x using Quot.inductionOn with | h q
        cases q with
        | inl u =>
          cases u
          change (tensorIterIso A K (n + 1)).hom.map ((tensorSpace (A.iterateSuspension (n + 1)) K).point) =
            BasedSpace.suspensionProjection _ ((tensorIterIso A K n).hom.map
              ((tensorSpace (A.iterateSuspension n) K).point), t)
          rw [(tensorIterIso A K (n + 1)).hom.point, (tensorIterIso A K n).hom.point]
          exact (BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)).symm
        | inr q => exact tensorIterIso_bond A K n q.1 q.2 t)
    let zeroSpace : BasedSpace.{0} := ⟨TopCat.of PUnit, PUnit.unit⟩
    have tensorZero_eq (K : TopCat.{0}) (z : tensorSpace zeroSpace K) :
        z = (tensorSpace zeroSpace K).point := by
      induction z using Quot.inductionOn with | h q
      cases q with
      | inl u => cases u; rfl
      | inr q => exact (congrArg (fun a => tensorPoint zeroSpace K a q.2)
          (Subsingleton.elim q.1 zeroSpace.point)).trans (tensorPoint_point zeroSpace K q.2)
    let tensorZeroIso (K : TopCat.{0}) : tensorSpace zeroSpace K ≅ zeroSpace := {
      hom := ⟨ContinuousMap.const _ zeroSpace.point, rfl⟩
      inv := ⟨ContinuousMap.const _ (tensorSpace zeroSpace K).point, rfl⟩
      hom_inv_id := by
        apply BasedSpace.Hom.ext
        apply ContinuousMap.ext
        intro z
        exact (tensorZero_eq K z).symm
      inv_hom_id := by
        apply BasedSpace.Hom.ext
        apply ContinuousMap.ext
        intro z
        exact Subsingleton.elim _ _ }
    let levelIso {X Y : Prespectrum.{0}} (e : X ≅ Y) (n : ℕ) : X.level n ≅ Y.level n := {
      hom := levelHom n e.hom
      inv := levelHom n e.inv
      hom_inv_id := congrArg (levelHom n) e.hom_inv_id
      inv_hom_id := congrArg (levelHom n) e.inv_hom_id }
    let desuspensionIso {X Y : Prespectrum.{0}} (e : X ≅ Y) :
        Prespectrum.desuspension X ≅ Prespectrum.desuspension Y :=
      prespectrumIsoOfLevels (fun n => match n with
        | 0 => Iso.refl zeroSpace
        | n + 1 => levelIso e n) (by
        intro n x t
        cases n with
        | zero => exact e.hom.point 0
        | succ n => exact e.hom.bond n x t)
    let tensorDesuspensionIso (X : Prespectrum.{0}) (K : TopCat.{0}) :
        tensor (Prespectrum.desuspension X) K ≅ Prespectrum.desuspension (tensor X K) :=
      prespectrumIsoOfLevels (fun n => match n with
        | 0 => tensorZeroIso K
        | n + 1 => Iso.refl (tensorSpace (X.level n) K)) (by
        intro n x t
        cases n with
        | zero =>
          change tensorBond (Prespectrum.desuspension X) K 0 (x, t) =
            (tensorSpace (X.level 0) K).point
          rw [tensorZero_eq K x]
          exact tensorBond_point (Prespectrum.desuspension X) K 0 t
        | succ n => rfl)
    let tensorFreeIso (n : ℕ) (A : BasedSpace.{0}) (K : TopCat.{0}) [LocallyCompactSpace K] :
        tensor (Prespectrum.free n A) K ≅ Prespectrum.free n (tensorSpace A K) := by
      induction n with
      | zero => exact tensorSuspensionSpectrumIso A K
      | succ n ih =>
        have hs (B : BasedSpace.{0}) : Prespectrum.free (n + 1) B =
            Prespectrum.desuspension (Prespectrum.free n B) :=
          Function.iterate_succ_apply' Prespectrum.desuspension n (Prespectrum.suspensionSpectrum B)
        rw [hs A, hs (tensorSpace A K)]
        exact tensorDesuspensionIso (Prespectrum.free n A) K ≪≫ desuspensionIso ih
    sorry
  obtain ⟨R, η, hR, hη⟩ := local_replacement
  exact ⟨{
    replacement := R
    unit := η
    isLocal := hR
    universal := (unit_criterion R η).2 hη }⟩

noncomputable def completionModel : CompletionModel := Classical.choice completionModel_exists

noncomputable def completedLocalization : Prespectrum.{0} ⥤ CompletedSpectrum where
  obj X := ⟨completionModel.replacement.obj X, completionModel.isLocal X⟩
  map f := sourceLocalization.map (completionModel.replacement.map f)
  map_id X := by
    change sourceLocalization.map (completionModel.replacement.map (𝟙 X)) = 𝟙 _
    simp
  map_comp f g := by
    change sourceLocalization.map (completionModel.replacement.map (f ≫ g)) =
      sourceLocalization.map (completionModel.replacement.map f) ≫
      sourceLocalization.map (completionModel.replacement.map g)
    simp

end KIP126.StableHomotopy.Implementation
