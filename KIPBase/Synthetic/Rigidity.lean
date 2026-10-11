/-
  KIPBase.Synthetic.Rigidity
  §3.5 Synthetic rigidity — E₂ computation of νX (§3.6),
  Adams vs λ-Bockstein (§3.8, cofiber sequence Σ^{0,-r}νX →[λʳ] νX → νX/λʳ),
  E∞ comparison between synthetic and classical Adams (§3.12)
-/
import KIPBase.Mathlib
import KIPBase.Synthetic.Adams
import KIPBase.Synthetic.AdamsVanishing
import KIPBase.Synthetic.LambdaE2
import KIPBase.Synthetic.Nu
import KIPBase.StableHomotopy.Adams

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v u' v'

variable (𝒮 : Type u) [StableHomotopy.StableHomotopyCategory.{u, v} 𝒮]
variable (Syn : Type u') [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-! ### E∞-page of the synthetic Adams SS -/

/-- KIP Corollary A.9, Proposition 3.12: The E∞-data for the synthetic Adams
    spectral sequence of ν(X). -/
axiom SynAdamsEInfty (𝒮 : Type u) [StableHomotopy.StableHomotopyCategory.{u, v} 𝒮]
    (Syn : Type u') [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]
    (X : 𝒮) : EInftyData AddCommGrpCat.{0} (ℤ × ℤ × ℤ)

/-- Formalization bridge: The E∞-data is associated with the synthetic Adams
    SS for ν(X). Links `SynAdamsEInfty` to `SynAdamsSS`. -/
axiom synAdamsEInfty_ss (X : 𝒮) :
    (SynAdamsEInfty 𝒮 Syn X).ss = SynAdamsSS Syn ((nu 𝒮 Syn).obj X)

/-! ### Rigidity theorem

The rigidity theorem (KIP Theorem A.8) states:
  E₂^{s,t,w}(SynAdamsSS(νX)) ≅ E₂^{s,t}(AdamsSS(X)) ⊗ F₂[λ]_w
with differential correspondence d_r^syn(x) = λ^{r-1} · d_r^cl(x).

The free λ-page data below records the part of this description needed to
transport essential differentials. -/

/-- KIP Theorem A.8 (rigidity — degeneration transfer): If the classical
    Adams SS degenerates at page N, then the synthetic Adams SS for ν(X)
    also degenerates at page N. -/
axiom rigidity_degeneration (X : 𝒮) (N : ℤ) :
    (StableHomotopy.AdamsSS 𝒮 X).DegeneratesAt N →
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).DegeneratesAt N

/-- The synthetic Adams differential with its target written in the
standard tridegree `(s+r,t+r-1,w)`. -/
noncomputable def synAdamsDifferentialNormalized (Y : Syn) (r s t w : ℤ) :
    (SynAdamsSS Syn Y).Page r (s, t, w) ⟶
      (SynAdamsSS Syn Y).Page r (s + r, t + r - 1, w) :=
  (SynAdamsSS Syn Y).d r (s, t, w) ≫
    eqToHom (congrArg (fun k => (SynAdamsSS Syn Y).Page r k) (by
      rw [synAdamsSS_diffDeg]
      ext <;> dsimp <;> omega))

/-- The classical Adams differential with its target written in the
standard bidegree `(s+r,t+r-1)`. -/
noncomputable def classicalAdamsDifferentialNormalized (X : 𝒮)
    (r s t : ℤ) :
    (StableHomotopy.AdamsSS 𝒮 X).Page r (s, t) ⟶
      (StableHomotopy.AdamsSS 𝒮 X).Page r (s + r, t + r - 1) :=
  (StableHomotopy.AdamsSS 𝒮 X).d r (s, t) ≫
    eqToHom (congrArg
      (fun k => (StableHomotopy.AdamsSS 𝒮 X).Page r k) (by
        rw [StableHomotopy.adamsSS_diffDeg]
        ext <;> dsimp [StableHomotopy.adamsDiffDeg] <;> omega))

/-- In the range `r-2 ≤ t-w`, the `r`-page of the synthetic Adams sequence
of `νX` is still on the free part of its λ-tower.  All weights in this range
identify with one generator object, and the actual λ map is the identity
under those identifications. -/
structure NuAdamsFreeLambdaPages (X : 𝒮) where
  generator : (r s t : ℤ) → AddCommGrpCat.{0}
  generatorClassicalEquiv : ∀ (r s t : ℤ),
    ↑(generator r s t) ≃+
      ↑((StableHomotopy.AdamsSS 𝒮 X).Page r (s, t))
  componentIso : ∀ (r : ℤ) (_hr : 2 ≤ r) (s t w : ℤ)
      (_h : r - 2 ≤ t - w),
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w) ≅
      generator r s t
  lambda_compat : ∀ (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ)
      (h : r - 2 ≤ t - w),
    let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
    let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
    L.lambda r (s, t, w) ≫
        eqToHom (congrArg (fun j => E.Page r j) (by
          change (s, t, w) + (0, 0, -1) = (s, t, w - 1)
          ext <;> simp [sub_eq_add_neg])) ≫
        (componentIso r hr s t (w - 1) (by omega)).hom =
      (componentIso r hr s t w h).hom
  differential_compat : ∀ (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ)
      (h : r - 2 ≤ t - w)
      (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w)),
    generatorClassicalEquiv r (s + r) (t + r - 1)
        ((componentIso r hr (s + r) (t + r - 1) w (by omega)).hom
          ((synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X)
            r s t w).hom x)) =
      (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom
        (generatorClassicalEquiv r s t
          ((componentIso r hr s t w h).hom x))

/-- KIP Theorem A.8, free λ-page form.  This replaces the former
`w < 0` vanishing axiom, which had the wrong grading: λ lowers weight, so a
free λ-tower is not generally zero in negative weights. -/
axiom rigidity_free_lambda_pages (X : 𝒮) :
  NuAdamsFreeLambdaPages 𝒮 Syn X

namespace NuAdamsFreeLambdaPages

/-- In the free range, a synthetic Adams page component is the
corresponding classical Adams page. -/
noncomputable def componentClassicalEquiv (X : 𝒮)
    (R : NuAdamsFreeLambdaPages 𝒮 Syn X)
    (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (h : r - 2 ≤ t - w) :
    ↑((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w)) ≃+
      ↑((StableHomotopy.AdamsSS 𝒮 X).Page r (s, t)) :=
  (addEquivOfAddCommGrpCatIso (R.componentIso r hr s t w h)).trans
    (R.generatorClassicalEquiv r s t)

/-- On a free source component, the normalized synthetic differential is
the classical Adams differential under the rigidity identifications. -/
theorem componentClassicalEquiv_differential (X : 𝒮)
    (R : NuAdamsFreeLambdaPages 𝒮 Syn X)
    (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (h : r - 2 ≤ t - w)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w)) :
    R.componentClassicalEquiv 𝒮 Syn X r hr (s + r) (t + r - 1) w
        (by omega)
        ((synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X)
          r s t w).hom x) =
      (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom
        (R.componentClassicalEquiv 𝒮 Syn X r hr s t w h x) :=
  R.differential_compat r hr s t w h x

/-- The actual λ action is an isomorphism between adjacent components in
the free range. -/
noncomputable def freeStep (X : 𝒮) (R : NuAdamsFreeLambdaPages 𝒮 Syn X)
    (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (h : r - 2 ≤ t - w) :
    FreeLambdaPageStep
      (synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)) r (s, t, w) := by
  let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
  let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
  let es := R.componentIso r hr s t w h
  let shiftEq : (s, t, w) + (0, 0, -1) = (s, t, w - 1) := by
    ext <;> simp [sub_eq_add_neg]
  let et : E.Page r ((s, t, w) + (0, 0, -1)) ≅ R.generator r s t :=
    eqToIso (congrArg (fun j => E.Page r j) shiftEq) ≪≫
      R.componentIso r hr s t (w - 1) (by omega)
  refine { iso := es ≪≫ et.symm, lambda_eq := ?_ }
  apply (cancel_mono et.hom).mp
  change L.lambda r (s, t, w) ≫ et.hom =
    (es.hom ≫ et.inv) ≫ et.hom
  rw [Category.assoc, et.inv_hom_id, Category.comp_id]
  simpa only [E, L, es, et, shiftEq, Iso.trans_hom, eqToIso,
    Category.assoc] using R.lambda_compat r hr s t w h

end NuAdamsFreeLambdaPages

/-! ### Lifting classical differentials before inverting λ

The existing comparison on the free λ-tail is the finite-page input of the
λ-inverted comparison. We construct representatives of classical classes
in that tail and prove their differential formula using the actual
iterated λ action. No new comparison assumption is introduced. -/

/-- The existing iterated page λ-map, with its final weight displayed. -/
noncomputable def synAdamsLambdaPowNormalized (Y : Syn) (n : ℕ)
    (r s t w : ℤ) :
    (SynAdamsSS Syn Y).Page r (s, t, w) ⟶
      (SynAdamsSS Syn Y).Page r (s, t, w - (n : ℤ)) :=
  (synAdamsSS_zlambda_module Syn Y).lambdaPow n r (s, t, w) ≫
    eqToHom (congrArg (fun k => (SynAdamsSS Syn Y).Page r k) (by
      rw [SynAdamsLambdaModule.lambdaIndex_eq]
      ext <;> simp [sub_eq_add_neg]))

namespace NuAdamsFreeLambdaPages

theorem componentClassicalEquiv_lambdaPow (X : 𝒮)
    (R : NuAdamsFreeLambdaPages 𝒮 Syn X)
    (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (h : r - 2 ≤ t - w)
    (n : ℕ) (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w)) :
    R.componentClassicalEquiv 𝒮 Syn X r hr s t (w - n) (by omega)
        ((synAdamsLambdaPowNormalized Syn ((nu 𝒮 Syn).obj X) n r s t w).hom x) =
      R.componentClassicalEquiv 𝒮 Syn X r hr s t w h x := by
  let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
  let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
  let identify (j : ℤ × ℤ × ℤ) (v : ℤ) (hj : j = (s, t, v))
      (hv : r - 2 ≤ t - v) : E.Page r j ⟶ R.generator r s t :=
    eqToHom (congrArg (fun k => E.Page r k) hj) ≫
      (R.componentIso r hr s t v hv).hom
  have identify_eq (j : ℤ × ℤ × ℤ) (v v' : ℤ)
      (hj : j = (s, t, v)) (hj' : j = (s, t, v'))
      (hv : r - 2 ≤ t - v) (hv' : r - 2 ≤ t - v') :
      identify j v hj hv = identify j v' hj' hv' := by
    have he : v = v' := congrArg (fun k => k.2.2) (hj.symm.trans hj')
    subst v'
    rfl
  have step (j : ℤ × ℤ × ℤ) (v : ℤ) (hj : j = (s, t, v))
      (hv : r - 2 ≤ t - v) :
      L.lambda r j ≫ identify (j + (0, 0, -1)) (v - 1)
        (by rw [hj]; ext <;> dsimp <;> omega) (by omega) =
        identify j v hj hv := by
    subst j
    exact (R.lambda_compat r hr s t v hv).trans
      (Category.id_comp (R.componentIso r hr s t v hv).hom).symm
  have idx (n : ℕ) : SynAdamsLambdaModule.lambdaIndex n (s, t, w) =
      (s, t, w - (n : ℤ)) := by
    rw [SynAdamsLambdaModule.lambdaIndex_eq]
    ext <;> dsimp <;> omega
  have hmap : ∀ n : ℕ,
      L.lambdaPow n r (s, t, w) ≫
        identify (SynAdamsLambdaModule.lambdaIndex n (s, t, w))
          (w - n) (idx n) (by omega) =
      (R.componentIso r hr s t w h).hom := by
    intro n
    induction n with
    | zero =>
      exact (Category.id_comp _).trans
        ((identify_eq (s, t, w) (w - (0 : ℕ)) w (idx 0) rfl
          (by omega) h).trans (Category.id_comp _))
    | succ n ih =>
      have hstep : L.lambda r (SynAdamsLambdaModule.lambdaIndex n (s, t, w)) ≫
          identify (SynAdamsLambdaModule.lambdaIndex (n + 1) (s, t, w))
            (w - ((n + 1 : ℕ) : ℤ)) (idx (n + 1)) (by omega) =
        identify (SynAdamsLambdaModule.lambdaIndex n (s, t, w))
          (w - n) (idx n) (by omega) := by
        apply (congrArg (fun q =>
          L.lambda r (SynAdamsLambdaModule.lambdaIndex n (s, t, w)) ≫ q)
          (identify_eq _ (w - ((n + 1 : ℕ) : ℤ)) (w - (n : ℤ) - 1)
            (idx (n + 1)) (by rw [idx]; ext <;> dsimp; omega)
            (by omega) (by omega))).trans
        exact step _ (w - n) (idx n) (by omega)
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun q => L.lambdaPow n r (s, t, w) ≫ q) hstep).trans ih)
  have hmap' :
      synAdamsLambdaPowNormalized Syn ((nu 𝒮 Syn).obj X) n r s t w ≫
        (R.componentIso r hr s t (w - n) (by omega)).hom =
      (R.componentIso r hr s t w h).hom :=
    (Category.assoc _ _ _).trans (hmap n)
  exact congrArg (fun f => R.generatorClassicalEquiv r s t (f.hom x)) hmap'

/-- The representative of a classical page class in a specified free
weight component. The representative is constructed by the existing
comparison isomorphism. -/
noncomputable def classicalLift (X : 𝒮)
    (R : NuAdamsFreeLambdaPages 𝒮 Syn X)
    (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (h : r - 2 ≤ t - w)
    (x : (StableHomotopy.AdamsSS 𝒮 X).Page r (s, t)) :
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w) :=
  (R.componentClassicalEquiv 𝒮 Syn X r hr s t w h).symm x

/-- Multiplication by an actual power of λ changes the chosen free weight
of the lift and leaves its classical class unchanged. -/
theorem classicalLift_lambdaPow (X : 𝒮)
    (R : NuAdamsFreeLambdaPages 𝒮 Syn X)
    (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (h : r - 2 ≤ t - w)
    (n : ℕ) (x : (StableHomotopy.AdamsSS 𝒮 X).Page r (s, t)) :
    (synAdamsLambdaPowNormalized Syn ((nu 𝒮 Syn).obj X) n r s t w).hom
        (R.classicalLift 𝒮 Syn X r hr s t w h x) =
      R.classicalLift 𝒮 Syn X r hr s t (w - n) (by omega) x := by
  apply (R.componentClassicalEquiv 𝒮 Syn X r hr s t (w - n) (by omega)).injective
  exact (R.componentClassicalEquiv_lambdaPow 𝒮 Syn X r hr s t w h n _).trans
    (((R.componentClassicalEquiv 𝒮 Syn X r hr s t w h).apply_symm_apply x).trans
      ((R.componentClassicalEquiv 𝒮 Syn X r hr s t (w - n) (by omega)).apply_symm_apply x).symm)

/-- The lifts are compatible with equality of the displayed weights. -/
theorem classicalLift_transport (X : 𝒮)
    (R : NuAdamsFreeLambdaPages 𝒮 Syn X)
    (r : ℤ) (hr : 2 ≤ r) (s t w w' : ℤ) (hw : w = w')
    (h : r - 2 ≤ t - w) (h' : r - 2 ≤ t - w')
    (x : (StableHomotopy.AdamsSS 𝒮 X).Page r (s, t)) :
    (eqToHom (congrArg
        (fun v => (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, v)) hw)).hom
        (R.classicalLift 𝒮 Syn X r hr s t w h x) =
      R.classicalLift 𝒮 Syn X r hr s t w' h' x := by
  subst w'
  rfl

/-- The reverse differential correspondence on a specified free component:
starting from a classical differential constructs its synthetic lift. -/
theorem classicalLift_differential_iff (X : 𝒮)
    (R : NuAdamsFreeLambdaPages 𝒮 Syn X)
    (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (h : r - 2 ≤ t - w)
    (x : (StableHomotopy.AdamsSS 𝒮 X).Page r (s, t))
    (y : (StableHomotopy.AdamsSS 𝒮 X).Page r (s + r, t + r - 1)) :
    (synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X) r s t w).hom
        (R.classicalLift 𝒮 Syn X r hr s t w h x) =
      R.classicalLift 𝒮 Syn X r hr (s + r) (t + r - 1) w (by omega) y ↔
    (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom x = y := by
  let e := R.componentClassicalEquiv 𝒮 Syn X r hr (s + r) (t + r - 1) w (by omega)
  rw [← e.injective.eq_iff]
  rw [R.componentClassicalEquiv_differential 𝒮 Syn X r hr s t w h]
  simp only [classicalLift, e, AddEquiv.apply_symm_apply]

end NuAdamsFreeLambdaPages

/-- A classical Adams differential is exactly its synthetic lift multiplied
by the weight-forced power `lambda^(r-1)`.  The source and target are first
lifted at the same depth `a` in their free lambda towers; multiplication by
`lambda^(r-1)` then moves the target to the weight of the synthetic
differential. -/
theorem synAdams_classical_differential_lambda_lift_eq_iff (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) (a : ℕ) (ha : r - 2 ≤ a)
    (x : (StableHomotopy.AdamsSS 𝒮 X).Page (r : ℤ) (s, t))
    (y : (StableHomotopy.AdamsSS 𝒮 X).Page (r : ℤ)
      (s + r, t + r - 1)) :
    let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
    let R := rigidity_free_lambda_pages 𝒮 Syn X
    let xLift := R.classicalLift 𝒮 Syn X r (by omega)
      s t (t - a) (by omega) x
    let yLift := R.classicalLift 𝒮 Syn X r (by omega)
      (s + r) (t + r - 1) (t + r - 1 - a) (by omega) y
    (synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X)
        r s t (t - a)).hom xLift =
      (eqToHom (congrArg
        (fun w => E.Page (r : ℤ) (s + r, t + r - 1, w))
        (show t + r - 1 - a - ((r - 1 : ℕ) : ℤ) = t - a by omega))).hom
        ((synAdamsLambdaPowNormalized Syn ((nu 𝒮 Syn).obj X)
          (r - 1) r (s + r) (t + r - 1) (t + r - 1 - a)).hom yLift) ↔
      (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom x = y := by
  dsimp only
  let R := rigidity_free_lambda_pages 𝒮 Syn X
  let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
  let transport := eqToHom (congrArg
    (fun w => E.Page (r : ℤ) (s + r, t + r - 1, w))
    (show t + r - 1 - a - ((r - 1 : ℕ) : ℤ) = t - a by omega))
  have htarget : transport.hom
      ((synAdamsLambdaPowNormalized Syn ((nu 𝒮 Syn).obj X)
          (r - 1) r (s + r) (t + r - 1) (t + r - 1 - a)).hom
        (R.classicalLift 𝒮 Syn X r (by omega)
          (s + r) (t + r - 1) (t + r - 1 - a) (by omega) y)) =
      R.classicalLift 𝒮 Syn X r (by omega)
        (s + r) (t + r - 1) (t - a) (by omega) y := by
    exact (congrArg transport.hom
      (R.classicalLift_lambdaPow 𝒮 Syn X r (by omega)
        (s + r) (t + r - 1) (t + r - 1 - a) (by omega)
        (r - 1) y)).trans
      (R.classicalLift_transport 𝒮 Syn X r (by omega)
        (s + r) (t + r - 1) _ (t - a) (by omega)
        (by omega) (by omega) y)
  rw [htarget]
  exact R.classicalLift_differential_iff 𝒮 Syn X r (by omega)
    s t (t - a) (by omega) x y

/-- Clearing λ denominators in the existing classical comparison gives
both directions of the essential differential formula. With source and
target lifts at the same λ-exponent `a`, the target is multiplied by
exactly `λ^(r-1)`. The exponent follows from the difference of their
generator weights. -/
theorem synAdams_classical_differential_lambda_lift_iff (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) (a : ℕ) (ha : r - 2 ≤ a)
    (x : (StableHomotopy.AdamsSS 𝒮 X).Page (r : ℤ) (s, t))
    (y : (StableHomotopy.AdamsSS 𝒮 X).Page (r : ℤ)
      (s + r, t + r - 1)) :
    let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
    let R := rigidity_free_lambda_pages 𝒮 Syn X
    let xLift := R.classicalLift 𝒮 Syn X r (by omega) s t (t - a) (by omega) x
    let yLift := R.classicalLift 𝒮 Syn X r (by omega)
      (s + r) (t + r - 1) (t + r - 1 - a) (by omega) y
    let yLambda :=
      (eqToHom (congrArg (fun w => E.Page (r : ℤ) (s + r, t + r - 1, w))
        (show t + r - 1 - a - ((r - 1 : ℕ) : ℤ) = t - a by omega))).hom
        ((synAdamsLambdaPowNormalized Syn ((nu 𝒮 Syn).obj X)
          (r - 1) r (s + r) (t + r - 1) (t + r - 1 - a)).hom yLift)
    ((synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X)
        r s t (t - a)).hom xLift = yLambda ∧ yLambda ≠ 0) ↔
      ((classicalAdamsDifferentialNormalized 𝒮 X r s t).hom x = y ∧ y ≠ 0) := by
  dsimp only
  let R := rigidity_free_lambda_pages 𝒮 Syn X
  let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
  let transport := eqToHom (congrArg
    (fun w => E.Page (r : ℤ) (s + r, t + r - 1, w))
    (show t + r - 1 - a - ((r - 1 : ℕ) : ℤ) = t - a by omega))
  have htarget : transport.hom
      ((synAdamsLambdaPowNormalized Syn ((nu 𝒮 Syn).obj X)
          (r - 1) r (s + r) (t + r - 1) (t + r - 1 - a)).hom
        (R.classicalLift 𝒮 Syn X r (by omega)
          (s + r) (t + r - 1) (t + r - 1 - a) (by omega) y)) =
      R.classicalLift 𝒮 Syn X r (by omega) (s + r) (t + r - 1) (t - a)
        (by omega) y := by
    exact (congrArg transport.hom
      (R.classicalLift_lambdaPow 𝒮 Syn X r (by omega)
        (s + r) (t + r - 1) (t + r - 1 - a) (by omega) (r - 1) y)).trans
      (R.classicalLift_transport 𝒮 Syn X r (by omega)
        (s + r) (t + r - 1) _ (t - a) (by omega) (by omega) (by omega) y)
  change ((_ = transport.hom _) ∧ transport.hom _ ≠ 0) ↔ _
  rw [htarget]
  apply and_congr
  · exact R.classicalLift_differential_iff 𝒮 Syn X r (by omega)
      s t (t - a) (by omega) x y
  · exact not_congr
      (R.componentClassicalEquiv 𝒮 Syn X r (by omega)
        (s + r) (t + r - 1) (t - a) (by omega)).symm.map_eq_zero_iff


/-- Every specified classical differential, including a zero differential,
gives the corresponding synthetic differential with the weight-forced
factor `λ^(r-1)`. The lifts are the constructed free-tail representatives. -/
theorem synAdams_classical_differential_lambda_lift (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) (a : ℕ) (ha : r - 2 ≤ a)
    (x : (StableHomotopy.AdamsSS 𝒮 X).Page (r : ℤ) (s, t))
    (y : (StableHomotopy.AdamsSS 𝒮 X).Page (r : ℤ)
      (s + r, t + r - 1))
    (hxy : (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom x = y) :
    let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
    let R := rigidity_free_lambda_pages 𝒮 Syn X
    let xLift := R.classicalLift 𝒮 Syn X r (by omega) s t (t - a) (by omega) x
    let yLift := R.classicalLift 𝒮 Syn X r (by omega)
      (s + r) (t + r - 1) (t + r - 1 - a) (by omega) y
    (synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X)
        r s t (t - a)).hom xLift =
      (eqToHom (congrArg (fun w => E.Page (r : ℤ) (s + r, t + r - 1, w))
        (show t + r - 1 - a - ((r - 1 : ℕ) : ℤ) = t - a by omega))).hom
        ((synAdamsLambdaPowNormalized Syn ((nu 𝒮 Syn).obj X)
          (r - 1) r (s + r) (t + r - 1) (t + r - 1 - a)).hom yLift) := by
  by_cases hy : y = 0
  · rcases hy with rfl
    dsimp only
    have hd := ((rigidity_free_lambda_pages 𝒮 Syn X).classicalLift_differential_iff
      𝒮 Syn X r (by omega) s t (t - a) (by omega) x 0).2 hxy
    simpa only [NuAdamsFreeLambdaPages.classicalLift, map_zero] using hd
  · exact ((synAdams_classical_differential_lambda_lift_iff
      𝒮 Syn X r hr s t a ha x y).2 ⟨hxy, hy⟩).1

/-- KIP Theorem A.8 (rigidity — above-diagonal vanishing): For w > t,
    E_r^{s,t,w}(SynAdamsSS(νX)) = 0 for all r ≥ 2. This reflects the
    F₂[λ]-module structure: the polynomial degree w is bounded by t. -/
axiom rigidity_above_diag_vanishing (X : 𝒮) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (htw : t < w) :
    IsZero ((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w))

/-- No differential can enter the generator diagonal: its source has
`t-r+1 < w=t`, which already vanishes on E₂. Hence every boundary
subobject on this diagonal, including the limiting one, is the initial
boundary subobject. Outgoing differentials are not assumed to vanish. -/
theorem synAdams_nu_diagonal_boundaries (X : 𝒮) (s t : ℤ)
    (n : WithTop ℕ) :
    ((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).ssData (s, t, t)).B n =
      ((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).ssData (s, t, t)).B 0 := by
  apply synAdams_boundaries_eq_initial_of_e2_incoming
  intro r hr
  rw [synAdamsSS_diffDeg]
  apply rigidity_above_diag_vanishing 𝒮 Syn X 2 (by omega)
  dsimp
  omega

/-- Every finite or limiting page on the generator diagonal embeds into
E₂ by the inclusion of its surviving cycles. This is constructed from the
nested subobjects, rather than by choosing an abstract group embedding. -/
noncomputable def synAdams_nu_diagonal_toE2 (X : 𝒮) (s t : ℤ)
    (n : WithTop ℕ) :
    ((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).ssData (s, t, t)).page n ⟶
      (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page 2 (s, t, t) :=
  pageToInitialOfBoundariesEq _ n (synAdams_nu_diagonal_boundaries 𝒮 Syn X s t n) ≫
    eqToHom (by
      simp only [SpectralSequence.Page, synAdamsSS_r0, sub_self, Int.toNat_zero]
      rfl)

/-- A surviving diagonal class has a unique underlying E₂ class. -/
theorem synAdams_nu_diagonal_toE2_injective (X : 𝒮) (s t : ℤ)
    (n : WithTop ℕ) :
    Function.Injective (synAdams_nu_diagonal_toE2 𝒮 Syn X s t n).hom := by
  apply (AddCommGrpCat.mono_iff_injective _).mp
  dsimp only [synAdams_nu_diagonal_toE2]
  infer_instance

/-- Displayed-page form of the canonical diagonal inclusion.  The page
`n+2` of synthetic Adams is the `n`th layer of its underlying `SSData`. -/
noncomputable def synAdams_nu_diagonal_displayed_toE2 (X : 𝒮) (s t : ℤ)
    (n : ℕ) :
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page ((n + 2 : ℕ) : ℤ) (s, t, t) ⟶
      (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page 2 (s, t, t) :=
  eqToHom (by
    simp only [SpectralSequence.Page, synAdamsSS_r0]
    congr 2
    omega) ≫
    synAdams_nu_diagonal_toE2 𝒮 Syn X s t n

/-- The earlier diagonal inclusion agrees with the general canonical
later-page-to-E2 map. -/
theorem synAdams_nu_diagonal_displayed_toE2_eq (X : 𝒮) (s t : ℤ)
    (n : ℕ) :
    synAdams_nu_diagonal_displayed_toE2 𝒮 Syn X s t n =
      synAdams_displayedPageToE2OfBoundariesEq
        ((nu 𝒮 Syn).obj X) n (s, t, t)
          (synAdams_nu_diagonal_boundaries 𝒮 Syn X s t n) := by
  unfold synAdams_nu_diagonal_displayed_toE2
    synAdams_nu_diagonal_toE2
    synAdams_displayedPageToE2OfBoundariesEq
  congr 1 <;> apply proof_irrel_heq

/-- A surviving class on the displayed diagonal page has a unique E₂
class. -/
theorem synAdams_nu_diagonal_displayed_toE2_injective (X : 𝒮) (s t : ℤ)
    (n : ℕ) :
    Function.Injective
      (synAdams_nu_diagonal_displayed_toE2 𝒮 Syn X s t n).hom := by
  dsimp only [synAdams_nu_diagonal_displayed_toE2]
  apply Function.Injective.comp
    (synAdams_nu_diagonal_toE2_injective 𝒮 Syn X s t n)
  exact (AddCommGrpCat.mono_iff_injective _).mp (by infer_instance)

/-- In the synthetic Adams spectral sequence of `νX`, an essential
`d_r(x)=y` remains essential after multiplication by λ, and conversely.

The proof has two inputs. Adams naturality gives
`d_r(λx)=λd_r(x)`. If the source can be nonzero then `w≤t`; hence the
target has λ-exponent `(t+r-1)-w ≥ r-1`, which lies in the free range of
the `r`-page. Multiplication by λ is therefore injective on the target. -/
theorem synAdams_pageDifferentialEssential_lambda_iff (X : 𝒮)
    (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w))
    (y : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r
      ((s, t, w) + (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).diffDeg r)) :
    let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
    let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
    PageDifferentialEssential E r (s, t, w) x y ↔
      ((L.lambdaShiftedDifferential r (s, t, w)).hom
          ((L.lambda r (s, t, w)).hom x) =
        (L.lambda r ((s, t, w) + E.diffDeg r)).hom y ∧
      (L.lambda r ((s, t, w) + E.diffDeg r)).hom y ≠ 0) := by
  dsimp only
  let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
  let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
  change PageDifferentialEssential E r (s, t, w) x y ↔
    ((L.lambdaShiftedDifferential r (s, t, w)).hom
        ((L.lambda r (s, t, w)).hom x) =
      (L.lambda r ((s, t, w) + E.diffDeg r)).hom y ∧
    (L.lambda r ((s, t, w) + E.diffDeg r)).hom y ≠ 0)
  by_cases hw : w ≤ t
  · let R := rigidity_free_lambda_pages 𝒮 Syn X
    have htarget : r - 2 ≤ (t + r - 1) - w := by omega
    let F₀ := R.freeStep 𝒮 Syn X r hr (s + r) (t + r - 1) w htarget
    have hdeg : (s, t, w) + E.diffDeg r =
        (s + r, t + r - 1, w) := by
      dsimp only [E]
      rw [synAdamsSS_diffDeg]
      ext <;> dsimp <;> omega
    let F : FreeLambdaPageStep L r ((s, t, w) + E.diffDeg r) := by
      rw [hdeg]
      exact F₀
    exact L.pageDifferentialEssential_lambda_iff r (s, t, w) x y F
  · have hzero : IsZero (E.Page r (s, t, w)) := by
      dsimp only [E]
      exact rigidity_above_diag_vanishing 𝒮 Syn X r hr s t w (by omega)
    letI := addCommGrpCatSubsingletonOfIsZero (E.Page r (s, t, w)) hzero
    have hx : x = 0 := Subsingleton.elim _ _
    constructor
    · rintro ⟨hxy, hy⟩
      exfalso
      apply hy
      calc
        y = (E.d r (s, t, w)).hom x := hxy.symm
        _ = 0 := by rw [hx, map_zero]
    · rintro ⟨hxy, hly⟩
      exfalso
      apply hly
      calc
        (L.lambda r ((s, t, w) + E.diffDeg r)).hom y =
            (L.lambdaShiftedDifferential r (s, t, w)).hom
              ((L.lambda r (s, t, w)).hom x) := hxy.symm
        _ = 0 := by rw [hx, map_zero, map_zero]

/-- Dividing an Adams differential by one λ gives a unique nonzero cycle
on the same page, in the weight appropriate to the actual cofiber boundary.
The λ-preimage is constructed from the free range; its cycle property follows
from λ-naturality, target injectivity, and `d² = 0`.

This is a page-level statement. It does not yet assert that this cycle is
permanent or that it detects the actual cofiber boundary on homotopy groups. -/
theorem synAdams_differential_lambda_preimage
    (X : 𝒮) (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (hw : w ≤ t)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w)) :
    let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
    let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
    let j := (s + r, t + r - 1, w + 1)
    let hindex : (s, t, w) + E.diffDeg r = j + (0, 0, -1) := by
      dsimp only [E, j]
      rw [synAdamsSS_diffDeg]
      ext <;> dsimp <;> omega
    let z := (eqToHom (congrArg (fun k => E.Page r k) hindex)).hom
      ((E.d r (s, t, w)).hom x)
    ∃ y : E.Page r j,
      (L.lambda r j).hom y = z ∧
      (E.d r j).hom y = 0 ∧
      (y ≠ 0 ↔ (E.d r (s, t, w)).hom x ≠ 0) ∧
      ∀ y' : E.Page r j, (L.lambda r j).hom y' = z → y' = y := by
  dsimp only
  let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
  let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
  let R := rigidity_free_lambda_pages 𝒮 Syn X
  let j : ℤ × ℤ × ℤ := (s + r, t + r - 1, w + 1)
  have hindex : (s, t, w) + E.diffDeg r = j + (0, 0, -1) := by
    dsimp only [E, j]
    rw [synAdamsSS_diffDeg]
    ext <;> dsimp <;> omega
  let transport := eqToIso (congrArg (fun k => E.Page r k) hindex)
  let z := transport.hom.hom ((E.d r (s, t, w)).hom x)
  let F : FreeLambdaPageStep L r j :=
    R.freeStep 𝒮 Syn X r hr (s + r) (t + r - 1) (w + 1) (by omega)
  let y := F.iso.inv.hom z
  have hly : (L.lambda r j).hom y = z := by
    rw [F.lambda_eq]
    exact ConcreteCategory.congr_hom F.iso.inv_hom_id z
  have hdz : (E.d r (j + (0, 0, -1))).hom z = 0 := by
    have htransport : ∀ (i i' : ℤ × ℤ × ℤ) (h : i = i')
        (a : E.Page r i),
        (E.d r i).hom a = 0 →
          (E.d r i').hom
            ((eqToHom (congrArg (fun k => E.Page r k) h)).hom a) = 0 := by
      intro i i' h a ha
      subst i'
      exact ha
    apply htransport _ _ hindex
    exact ConcreteCategory.congr_hom (E.d_comp_d r (s, t, w)) x
  have htargetIndex : j + E.diffDeg r =
      (s + r + r, t + r - 1 + r - 1, w + 1) := by
    dsimp only [E, j]
    rw [synAdamsSS_diffDeg]
    ext <;> dsimp <;> omega
  let FT : FreeLambdaPageStep L r (j + E.diffDeg r) := by
    rw [htargetIndex]
    exact R.freeStep 𝒮 Syn X r hr (s + r + r)
      (t + r - 1 + r - 1) (w + 1) (by omega)
  have hdy : (E.d r j).hom y = 0 := by
    apply FT.lambda_injective
    have hcomm := ConcreteCategory.congr_hom
      (L.lambdaShiftedDifferential_naturality r j) y
    change (L.lambdaShiftedDifferential r j).hom ((L.lambda r j).hom y) =
      (L.lambda r (j + E.diffDeg r)).hom ((E.d r j).hom y) at hcomm
    rw [← hcomm, hly, map_zero]
    change (eqToHom (congrArg (fun k => E.Page r k)
      (show (j + (0, 0, -1)) + E.diffDeg r =
        (j + E.diffDeg r) + (0, 0, -1) by abel))).hom
          ((E.d r (j + (0, 0, -1))).hom z) = 0
    rw [hdz, map_zero]
  have hy : y ≠ 0 ↔ (E.d r (s, t, w)).hom x ≠ 0 := by
    have hz : y = 0 ↔ z = 0 := by
      constructor
      · intro h
        simpa only [h, map_zero] using hly.symm
      · intro h
        apply F.lambda_injective
        simpa only [h, map_zero] using hly
    have hz' : z = 0 ↔ (E.d r (s, t, w)).hom x = 0 := by
      exact (addEquivOfAddCommGrpCatIso transport).map_eq_zero_iff
    exact not_congr (hz.trans hz')
  refine ⟨y, hly, hdy, hy, ?_⟩
  intro y' hy'
  exact F.lambda_injective (hy'.trans hly.symm)

/-- Every iterated λ-map on the target of a synthetic Adams differential is
injective when the source is on or below the top λ-weight.  The target
already has exponent at least `r-1`, so all subsequent λ-steps lie in the
free range. -/
theorem synAdams_lambdaPowTarget_injective (X : 𝒮)
    (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (hlower : 0 ≤ t - w) (m : ℕ) :
    let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
    let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
    Function.Injective (L.lambdaPowTarget m r (s, t, w)).hom := by
  dsimp only
  let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
  let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
  let R := rigidity_free_lambda_pages 𝒮 Syn X
  apply L.lambdaPowTarget_injective m r (s, t, w)
  intro i hi
  have hindex : SynAdamsLambdaModule.lambdaIndex i (s, t, w) + E.diffDeg r =
      (s + r, t + r - 1, w - (i : ℤ)) := by
    dsimp only [E]
    rw [SynAdamsLambdaModule.lambdaIndex_eq, synAdamsSS_diffDeg]
    ext <;> dsimp <;> omega
  rw [hindex]
  exact R.freeStep 𝒮 Syn X r hr (s + r) (t + r - 1)
    (w - (i : ℤ)) (by omega)

/-- Clearing a finite λ denominator preserves and reflects a specified
essential differential. The inverse implication uses injectivity on the
differential target, which follows from the free λ-range. -/
theorem synAdams_pageDifferentialEssential_lambdaPow_iff (X : 𝒮)
    (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (hlower : 0 ≤ t - w) (m : ℕ)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w))
    (y : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r
      ((s, t, w) + (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).diffDeg r)) :
    let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
    let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
    PageDifferentialEssential E r (s, t, w) x y ↔
      ((L.lambdaPowShiftedDifferential m r (s, t, w)).hom
          ((L.lambdaPow m r (s, t, w)).hom x) =
        (L.lambdaPowTarget m r (s, t, w)).hom y ∧
      (L.lambdaPowTarget m r (s, t, w)).hom y ≠ 0) := by
  dsimp only
  let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
  let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
  have hinj := synAdams_lambdaPowTarget_injective 𝒮 Syn X r hr s t w hlower m
  have hcomm := ConcreteCategory.congr_hom
    (L.lambdaPow_naturality m r (s, t, w)) x
  change (L.lambdaPowShiftedDifferential m r (s, t, w)).hom
      ((L.lambdaPow m r (s, t, w)).hom x) =
    (L.lambdaPowTarget m r (s, t, w)).hom ((E.d r (s, t, w)).hom x) at hcomm
  constructor
  · rintro ⟨hxy, hy⟩
    refine ⟨hcomm.trans (congrArg (L.lambdaPowTarget m r (s, t, w)).hom hxy), ?_⟩
    intro hzero
    exact hy (hinj (hzero.trans ((L.lambdaPowTarget m r (s, t, w)).hom.map_zero).symm))
  · rintro ⟨hxy, hy⟩
    refine ⟨hinj (hcomm.symm.trans hxy), ?_⟩
    intro hzero
    exact hy ((congrArg (L.lambdaPowTarget m r (s, t, w)).hom hzero).trans
      (L.lambdaPowTarget m r (s, t, w)).hom.map_zero)

/-- Move an arbitrary source class far enough down its λ-tower to enter the
free range.  The first equality is iterated λ-naturality.  The second then
identifies the shifted synthetic differential with the classical Adams
differential of `X`.  Injectivity of the target λ-map, proved above, makes
these two equalities determine the original synthetic differential. -/
theorem synAdams_differential_from_classical_after_lambdaPow (X : 𝒮)
    (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) (hlower : 0 ≤ t - w)
    (m : ℕ) (hfree : r - 2 ≤ t - w + m)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w)) :
    let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
    let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
    let R := rigidity_free_lambda_pages 𝒮 Syn X
    let shiftEq : SynAdamsLambdaModule.lambdaIndex m (s, t, w) =
        (s, t, w - (m : ℤ)) := by
      rw [SynAdamsLambdaModule.lambdaIndex_eq]
      ext <;> dsimp <;> omega
    let xshift : E.Page r (s, t, w - (m : ℤ)) :=
      (eqToHom (congrArg (fun k => E.Page r k) shiftEq)).hom
        ((L.lambdaPow m r (s, t, w)).hom x)
    (L.lambdaPowShiftedDifferential m r (s, t, w)).hom
        ((L.lambdaPow m r (s, t, w)).hom x) =
      (L.lambdaPowTarget m r (s, t, w)).hom
        ((E.d r (s, t, w)).hom x) ∧
    R.componentClassicalEquiv 𝒮 Syn X r hr
        (s + r) (t + r - 1) (w - (m : ℤ)) (by omega)
        ((synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X)
          r s t (w - (m : ℤ))).hom xshift) =
      (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom
        (R.componentClassicalEquiv 𝒮 Syn X r hr
          s t (w - (m : ℤ)) (by omega) xshift) ∧
    Function.Injective (L.lambdaPowTarget m r (s, t, w)).hom := by
  dsimp only
  let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
  let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
  let R := rigidity_free_lambda_pages 𝒮 Syn X
  let shiftEq : SynAdamsLambdaModule.lambdaIndex m (s, t, w) =
      (s, t, w - (m : ℤ)) := by
    rw [SynAdamsLambdaModule.lambdaIndex_eq]
    ext <;> dsimp <;> omega
  let xshift : E.Page r (s, t, w - (m : ℤ)) :=
    (eqToHom (congrArg (fun k => E.Page r k) shiftEq)).hom
      ((L.lambdaPow m r (s, t, w)).hom x)
  constructor
  · have h := congrArg (fun f => f.hom x)
      (L.lambdaPow_naturality m r (s, t, w))
    simpa only [AddCommGrpCat.coe_comp, Function.comp_apply] using h
  · constructor
    · exact R.componentClassicalEquiv_differential 𝒮 Syn X r hr
        s t (w - (m : ℤ)) (by omega) xshift
    · exact synAdams_lambdaPowTarget_injective 𝒮 Syn X r hr
        s t w hlower m

/-! ### λ-Bockstein spectral sequence

The comparison uses the ESS of the boundary morphism
  νX/λ → Σ^{1,-1}νX
in the cofiber sequence of `λ : Σ^{0,-1}νX → νX`.
Its construction is in `Synthetic.ExtensionSS`.

The theorem below records only the synthetic Adams starting page. The
comparison of pages and differentials remains a separate proof obligation. -/

/-- The synthetic Adams sequence of `νX` starts at page two. -/
theorem synAdamsNu_r₀ (X : 𝒮) :
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).r₀ = 2 :=
  synAdamsSS_r0 Syn ((nu 𝒮 Syn).obj X)

/-- Compatibility name for the former starting-page axiom.
Despite its historical name, this statement does not assert an isomorphism. -/
theorem lambda_bockstein_iso (X : 𝒮) :
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).r₀ = 2 :=
  synAdamsNu_r₀ 𝒮 Syn X

/-- Preserve the develop starting-page name without a separate axiom. -/
theorem lambda_bockstein_start_page (X : 𝒮) :
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).r₀ = 2 :=
  synAdamsNu_r₀ 𝒮 Syn X

/-! ### E∞ computations -/

/-- E∞ vanishing for ν(X) (KIP Prop 3.12):
    For t < w, E∞^{s,t,w}(νX) = 0.
    The permanent cycles in weight w cannot contribute below the
    diagonal t = w. -/
theorem einfty_nuX (X : 𝒮) (s t w : ℤ) (htw : t < w) :
    IsZero ((SynAdamsEInfty 𝒮 Syn X).EInfty (s, t, w)) := by
  -- Strategy: use rigidity_above_diag_vanishing to show all pages vanish,
  -- then propagate to E∞ via EInftyData.eInfty_isZero_of_page_isZero.
  apply EInftyData.eInfty_isZero_of_page_isZero
  intro r hr
  -- Rewrite the SS to use SynAdamsSS via synAdamsEInfty_ss
  rw [synAdamsEInfty_ss 𝒮 Syn X]
  -- The starting page is r₀ = 2 (from synAdamsSS_r0)
  -- We need 2 ≤ r, which follows from r₀ = 2 and hr : r₀ ≤ r
  have hr₀ : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).r₀ = 2 :=
    synAdamsSS_r0 Syn ((nu 𝒮 Syn).obj X)
  have h2r : 2 ≤ r := by
    have := synAdamsEInfty_ss (𝒮 := 𝒮) (Syn := Syn) X
    rw [this] at hr
    rw [hr₀] at hr
    exact hr
  exact rigidity_above_diag_vanishing 𝒮 Syn X r h2r s t w htw

/-- KIP Corollary A.9, Proposition 3.12: E∞ weight monotonicity for ν(X).
    For w₁ ≤ w₂ ≤ t, there is a natural surjection
    E∞^{s,t,w₁}(νX) ↠ E∞^{s,t,w₂}(νX).
    This reflects the quotient map Z∞/B_{1+t-w₁} → Z∞/B_{1+t-w₂}
    arising from B_{1+t-w₁} ⊆ B_{1+t-w₂}. -/
axiom einfty_nuX_weight_map (X : 𝒮) (s t w₁ w₂ : ℤ)
    (hw : w₁ ≤ w₂) (hw₂ : w₂ ≤ t) :
    (SynAdamsEInfty 𝒮 Syn X).EInfty (s, t, w₁) ⟶
      (SynAdamsEInfty 𝒮 Syn X).EInfty (s, t, w₂)

/-- KIP Corollary A.9, Proposition 3.12: The weight maps are
    epimorphisms (surjections). -/
axiom einfty_nuX_weight_map_epi (X : 𝒮) (s t w₁ w₂ : ℤ)
    (hw : w₁ ≤ w₂) (hw₂ : w₂ ≤ t) :
    Epi (einfty_nuX_weight_map 𝒮 Syn X s t w₁ w₂ hw hw₂)

/-- Structured E₂ calculation for a finite λ-quotient.  Besides the
componentwise truncated-module calculation, it records that the actual map
induced by `νX ⟶ νX/λ^n` is the canonical quotient map: on every retained
weight component it is an isomorphism. -/
structure NuModLambdaPageData (X : 𝒮) (n : ℕ) (s t w : ℤ) where
  quotientEquiv :
    ↑((SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) n)).Page 2
      (s, t, w)) ≃+
      ↑(nuModLambdaE2Component 𝒮 X n s t w)
  quotientPageMap_isIso_of_mem_strip :
    0 ≤ t - w ∧ t - w < n →
      IsIso (synAdamsPageMap (Syn := Syn)
        ((XModLambdaN.inclNatTrans n).app ((nu 𝒮 Syn).obj X))
        2 (s, t, w))
  quotientPageMap_isIso_of_safe_range : ∀ (r : ℤ),
    2 ≤ r → 0 ≤ t - w → t - w + r - 2 < n →
      IsIso (synAdamsPageMap (Syn := Syn)
        ((XModLambdaN.inclNatTrans n).app ((nu 𝒮 Syn).obj X))
        r (s, t, w))

/-- KIP Corollary A.11, Proposition 3.13, including naturality of the E₂
calculation with respect to the actual finite-quotient map. -/
axiom einfty_nuX_mod_lambda (X : 𝒮) (n : ℕ) (hn : 0 < n)
    (s t w : ℤ) : NuModLambdaPageData 𝒮 Syn X n s t w

/-- The E₂-page of `νX/λ^n` is supported in the strip
`0 ≤ t-w < n`.  This is now a consequence of the full E₂ computation. -/
theorem synAdams_nu_mod_lambda_e2_isZero_of_outside (X : 𝒮)
    (n : ℕ) (hn : 0 < n) (s t w : ℤ)
    (h : t - w < 0 ∨ (n : ℤ) ≤ t - w) :
    IsZero ((SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) n)).Page 2
      (s, t, w)) := by
  rw [IsZero.iff_id_eq_zero]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  change a = 0
  let e := (einfty_nuX_mod_lambda 𝒮 Syn X n hn s t w).quotientEquiv
  have hmodel : IsZero (nuModLambdaE2Component 𝒮 X n s t w) := by
    rw [nuModLambdaE2Component,
      TruncatedLambdaE2.component_eq_zero_of_outside]
    · exact IsInitial.isZero initialIsInitial
    · exact h
  letI := addCommGrpCatSubsingletonOfIsZero
    (nuModLambdaE2Component 𝒮 X n s t w) hmodel
  apply e.injective
  have he : e a = e 0 := Subsingleton.elim _ _
  simpa using he

/-- Inside the strip `0 ≤ t-w < n`, every weight component of the
synthetic Adams E₂-page of `νX/λ^n` is the classical Adams E₂ group of `X`.
Together with `synAdams_nu_mod_lambda_e2_isZero_of_outside`, this is the
complete componentwise description of the finite quotient E₂-page. -/
noncomputable def synAdams_nu_mod_lambda_e2_equiv_of_mem_strip (X : 𝒮)
    (n : ℕ) (s t w : ℤ) (h : 0 ≤ t - w ∧ t - w < n) :
    ↑((SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) n)).Page 2
      (s, t, w)) ≃+
      ↑((StableHomotopy.AdamsSS 𝒮 X).Page 2 (s, t)) :=
  (einfty_nuX_mod_lambda 𝒮 Syn X n (by omega) s t w).quotientEquiv.trans
    (addEquivOfAddCommGrpCatIso
      (nuModLambdaE2InStripIso 𝒮 X n s t w h))

/-! ### Differentials of finite λ-quotients -/

/-- The quotient map `νX ⟶ νX/λ^n`. -/
noncomputable def nuModLambdaIncl (X : 𝒮) (n : ℕ) :
    (nu 𝒮 Syn).obj X ⟶ XModLambdaN ((nu 𝒮 Syn).obj X) n :=
  (XModLambdaN.inclNatTrans n).app ((nu 𝒮 Syn).obj X)

/-- The map induced by the quotient inclusion on a synthetic Adams page. -/
noncomputable def nuModLambdaAdamsPageMap (X : 𝒮) (n : ℕ)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r k ⟶
      (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) n)).Page r k :=
  synAdamsPageMap (Syn := Syn) (nuModLambdaIncl 𝒮 Syn X n) r k

/-- On every retained E₂ component, the actual finite-quotient page map is
an isomorphism.  This is the naturality part of the structured E₂
calculation, rather than a consequence of an abstract group equivalence. -/
theorem nuModLambdaAdamsE2PageMapIsIso (X : 𝒮) (n : ℕ)
    (hn : 0 < n) (s t w : ℤ) (h : 0 ≤ t - w ∧ t - w < n) :
    IsIso (nuModLambdaAdamsPageMap 𝒮 Syn X n 2 (s, t, w)) := by
  exact (einfty_nuX_mod_lambda 𝒮 Syn X n hn s t w).quotientPageMap_isIso_of_mem_strip h

/-- Before an outgoing differential reaches the upper edge of the finite
λ-strip, the actual quotient map is an isomorphism on the source page. -/
theorem nuModLambdaAdamsPageMapIsIso_of_safe_range (X : 𝒮) (n : ℕ)
    (hn : 0 < n) (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ)
    (hlower : 0 ≤ t - w) (hupper : t - w + r - 2 < n) :
    IsIso (nuModLambdaAdamsPageMap 𝒮 Syn X n r (s, t, w)) := by
  exact (einfty_nuX_mod_lambda 𝒮 Syn X n hn s t w).quotientPageMap_isIso_of_safe_range
    r hr hlower hupper

/-- Formula for the Adams differential on every class represented by a
class of `νX`: apply the differential of `νX`, then pass to the finite
λ-quotient.  The target map includes the grading transport between the two
copies of the Adams differential degree. -/
theorem synAdams_nu_mod_lambda_differential_formula (X : 𝒮) (n : ℕ)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    nuModLambdaAdamsPageMap 𝒮 Syn X n r k ≫
        (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) n)).d r k =
      (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).d r k ≫
        synAdamsDifferentialTargetMap (Syn := Syn)
          (nuModLambdaIncl 𝒮 Syn X n) r k :=
  synAdamsPageMap_comm_d (Syn := Syn) (nuModLambdaIncl 𝒮 Syn X n) r k

/-- Element form of `synAdams_nu_mod_lambda_differential_formula`:
`d_r(q_r x) = q_r(d_r x)`. -/
theorem synAdams_nu_mod_lambda_differential_formula_apply (X : 𝒮)
    (n : ℕ) (r : ℤ) (k : ℤ × ℤ × ℤ)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r k) :
    ((SynAdamsSS Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) n)).d r k).hom
        ((nuModLambdaAdamsPageMap 𝒮 Syn X n r k).hom x) =
      (synAdamsDifferentialTargetMap (Syn := Syn)
        (nuModLambdaIncl 𝒮 Syn X n) r k).hom
        (((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).d r k).hom x) := by
  have h := congrArg (fun f => f.hom x)
    (synAdams_nu_mod_lambda_differential_formula 𝒮 Syn X n r k)
  simpa only [AddCommGrpCat.coe_comp, Function.comp_apply] using h

/-- If the quotient page map is surjective at a grading, the preceding
formula determines the quotient differential on every class at that
grading. -/
theorem synAdams_nu_mod_lambda_differential_formula_of_surjective (X : 𝒮)
    (n : ℕ) (r : ℤ) (k : ℤ × ℤ × ℤ)
    (hsurj : Function.Surjective
      (nuModLambdaAdamsPageMap 𝒮 Syn X n r k).hom)
    (z : (SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) n)).Page r k) :
    ∃ x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r k,
      (nuModLambdaAdamsPageMap 𝒮 Syn X n r k).hom x = z ∧
      ((SynAdamsSS Syn
          (XModLambdaN ((nu 𝒮 Syn).obj X) n)).d r k).hom z =
        (synAdamsDifferentialTargetMap (Syn := Syn)
          (nuModLambdaIncl 𝒮 Syn X n) r k).hom
          (((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).d r k).hom x) := by
  obtain ⟨x, rfl⟩ := hsurj z
  exact ⟨x, rfl,
    synAdams_nu_mod_lambda_differential_formula_apply 𝒮 Syn X n r k x⟩

/-- Complete formula in the range where the differential target remains in
the finite λ-strip. Every quotient class has a representative on the
`νX` page, and its differential is the image of the `νX` differential. -/
theorem synAdams_nu_mod_lambda_differential_formula_of_target_in_strip
    (X : 𝒮) (n : ℕ) (hn : 0 < n) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (hlower : 0 ≤ t - w)
    (htarget : t - w + r - 1 < n)
    (z : (SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) n)).Page r (s, t, w)) :
    ∃ x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w),
      (nuModLambdaAdamsPageMap 𝒮 Syn X n r (s, t, w)).hom x = z ∧
      ((SynAdamsSS Syn
          (XModLambdaN ((nu 𝒮 Syn).obj X) n)).d r (s, t, w)).hom z =
        (synAdamsDifferentialTargetMap (Syn := Syn)
          (nuModLambdaIncl 𝒮 Syn X n) r (s, t, w)).hom
          (((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).d r
            (s, t, w)).hom x) := by
  letI : IsIso (nuModLambdaAdamsPageMap 𝒮 Syn X n r (s, t, w)) :=
    nuModLambdaAdamsPageMapIsIso_of_safe_range 𝒮 Syn X n hn r hr
      s t w hlower (by omega)
  apply synAdams_nu_mod_lambda_differential_formula_of_surjective
    𝒮 Syn X n r (s, t, w)
  intro y
  refine ⟨(inv (nuModLambdaAdamsPageMap 𝒮 Syn X n r (s, t, w))).hom y, ?_⟩
  simp

/-- In the free source range, the finite-quotient differential is explicitly
the classical Adams differential of `X`: first lift the quotient class to
`νX`, identify that free component with the classical page, and apply the
classical differential. -/
theorem synAdams_nu_mod_lambda_differential_from_classical_of_free_source
    (X : 𝒮) (n : ℕ) (hn : 0 < n) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (hlower : 0 ≤ t - w)
    (hfree : r - 2 ≤ t - w) (htarget : t - w + r - 1 < n)
    (z : (SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) n)).Page r (s, t, w)) :
    let R := rigidity_free_lambda_pages 𝒮 Syn X
    ∃ x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, w),
      (nuModLambdaAdamsPageMap 𝒮 Syn X n r (s, t, w)).hom x = z ∧
      ((SynAdamsSS Syn
          (XModLambdaN ((nu 𝒮 Syn).obj X) n)).d r (s, t, w)).hom z =
        (synAdamsDifferentialTargetMap (Syn := Syn)
          (nuModLambdaIncl 𝒮 Syn X n) r (s, t, w)).hom
          (((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).d r
            (s, t, w)).hom x) ∧
      R.componentClassicalEquiv 𝒮 Syn X r hr
          (s + r) (t + r - 1) w (by omega)
          ((synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X)
            r s t w).hom x) =
        (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom
          (R.componentClassicalEquiv 𝒮 Syn X r hr
            s t w hfree x) := by
  dsimp only
  obtain ⟨x, hx, hd⟩ :=
    synAdams_nu_mod_lambda_differential_formula_of_target_in_strip
      𝒮 Syn X n hn r hr s t w hlower htarget z
  let R := rigidity_free_lambda_pages 𝒮 Syn X
  exact ⟨x, hx, hd,
    R.componentClassicalEquiv_differential 𝒮 Syn X r hr
      s t w hfree x⟩

/-- Complete finite-quotient differential formula in terms of the classical
Adams differential of `X`.  A quotient class is first lifted to the
synthetic Adams page of `νX`.  After multiplying the lift by a sufficiently
large power of λ, rigidity identifies its differential with the classical
one.  Naturality relates this shifted differential to the original one, and
injectivity of λ on the target makes the original differential unique. -/
theorem synAdams_nu_mod_lambda_differential_from_classical
    (X : 𝒮) (n : ℕ) (hn : 0 < n) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (hlower : 0 ≤ t - w)
    (htarget : t - w + r - 1 < n)
    (m : ℕ) (hfree : r - 2 ≤ t - w + m)
    (z : (SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) n)).Page r (s, t, w)) :
    let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
    let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
    let R := rigidity_free_lambda_pages 𝒮 Syn X
    let shiftEq : SynAdamsLambdaModule.lambdaIndex m (s, t, w) =
        (s, t, w - (m : ℤ)) := by
      rw [SynAdamsLambdaModule.lambdaIndex_eq]
      ext <;> dsimp <;> omega
    ∃ x : E.Page r (s, t, w),
      (nuModLambdaAdamsPageMap 𝒮 Syn X n r (s, t, w)).hom x = z ∧
      ((SynAdamsSS Syn
          (XModLambdaN ((nu 𝒮 Syn).obj X) n)).d r (s, t, w)).hom z =
        (synAdamsDifferentialTargetMap (Syn := Syn)
          (nuModLambdaIncl 𝒮 Syn X n) r (s, t, w)).hom
          ((E.d r (s, t, w)).hom x) ∧
      let xshift : E.Page r (s, t, w - (m : ℤ)) :=
        (eqToHom (congrArg (fun k => E.Page r k) shiftEq)).hom
          ((L.lambdaPow m r (s, t, w)).hom x)
      (L.lambdaPowShiftedDifferential m r (s, t, w)).hom
          ((L.lambdaPow m r (s, t, w)).hom x) =
        (L.lambdaPowTarget m r (s, t, w)).hom
          ((E.d r (s, t, w)).hom x) ∧
      R.componentClassicalEquiv 𝒮 Syn X r hr
          (s + r) (t + r - 1) (w - (m : ℤ)) (by omega)
          ((synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X)
            r s t (w - (m : ℤ))).hom xshift) =
        (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom
          (R.componentClassicalEquiv 𝒮 Syn X r hr
            s t (w - (m : ℤ)) (by omega) xshift) ∧
      Function.Injective (L.lambdaPowTarget m r (s, t, w)).hom := by
  dsimp only
  obtain ⟨x, hx, hd⟩ :=
    synAdams_nu_mod_lambda_differential_formula_of_target_in_strip
      𝒮 Syn X n hn r hr s t w hlower htarget z
  refine ⟨x, hx, hd, ?_⟩
  exact synAdams_differential_from_classical_after_lambdaPow
    𝒮 Syn X r hr s t w hlower m hfree x

/-- If the source exponent lies outside the quotient strip, the source page
is zero and hence so is its outgoing Adams differential. -/
theorem synAdams_nu_mod_lambda_d_eq_zero_of_source_outside (X : 𝒮)
    (n : ℕ) (hn : 0 < n) (r s t w : ℤ)
    (houtside : t - w < 0 ∨ (n : ℤ) ≤ t - w) :
    (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) n)).d r
      (s, t, w) = 0 :=
  (synAdams_page_isZero_of_e2 _ r (s, t, w)
    (synAdams_nu_mod_lambda_e2_isZero_of_outside 𝒮 Syn X n hn
      s t w houtside)).eq_of_src _ _

/-- If the target exponent leaves the strip `0 ≤ t-w < n`, the Adams
differential of `νX/λ^n` is zero. Since `d_r` raises the λ-exponent by
`r-1`, this is the condition `n ≤ t-w+r-1`. -/
theorem synAdams_nu_mod_lambda_d_eq_zero_of_target_outside (X : 𝒮)
    (n : ℕ) (hn : 0 < n) (r s t w : ℤ)
    (houtside : (n : ℤ) ≤ t - w + r - 1) :
    (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) n)).d r
      (s, t, w) = 0 := by
  let E := SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) n)
  have htarget : IsZero (E.Page r ((s, t, w) + E.diffDeg r)) := by
    rw [synAdamsSS_diffDeg]
    apply synAdams_page_isZero_of_e2
    apply synAdams_nu_mod_lambda_e2_isZero_of_outside 𝒮 Syn X n hn
    right
    dsimp
    omega
  exact htarget.eq_of_tgt _ _

/-- On its surviving diagonal, the E₂-page of `νX/λ` is the classical
Adams E₂-page of `X`. -/
noncomputable def synAdams_nu_mod_lambda_one_e2_diagonal_equiv (X : 𝒮)
    (s t w : ℤ) (h : w = t) :
    ↑((SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) 1)).Page 2
      (s, t, w)) ≃+
      ↑((StableHomotopy.AdamsSS 𝒮 X).Page 2 (s, t)) :=
  synAdams_nu_mod_lambda_e2_equiv_of_mem_strip 𝒮 Syn X 1 s t w (by omega)

/-- The existing quotient support theorem forces degeneration by page
`max 2 (n+1)`, without a bound on Adams filtration. -/
theorem synAdams_mod_lambda_degenerates (X : 𝒮) (n : ℕ) (hn : 0 < n) :
    (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) n)).DegeneratesAt
      (max 2 ((n : ℤ) + 1)) :=
  synAdams_degenerates_of_e2_strip _ n
    (synAdams_nu_mod_lambda_e2_isZero_of_outside 𝒮 Syn X n hn)

/-- The limiting Adams page of a finite λ-quotient is its first uniformly
stable page `max 2 (n+1)`.  This reads the limit from the proved strip
degeneration and does not impose boundedness on the Adams filtration. -/
noncomputable def synAdams_mod_lambda_eInftyIso_stablePage
    (X : 𝒮) (n : ℕ) (hn : 0 < n) (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) n)).ssData k).eInfty ≅
      (SynAdamsSS Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) n)).Page
          (max 2 ((n : ℤ) + 1)) k :=
  synAdams_eInftyIso_page_of_degenerates _
    (max 2 ((n : ℤ) + 1)) (by omega)
    (synAdams_mod_lambda_degenerates 𝒮 Syn X n hn) k

/-- Any convergence witness for a finite λ-quotient identifies its
associated graded with the stable finite page computed above. -/
noncomputable def synAdams_mod_lambda_associatedGradedIso_stablePage
    (X : 𝒮) (n : ℕ) (hn : 0 < n)
    {A : ℤ × ℤ → AddCommGrpCat.{0}} {F : Filtration A}
    (conv : Convergence
      (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) n)) A F)
    (k : ℤ × ℤ × ℤ) :
    F.associatedGraded (conv.reindex k).1 (conv.reindex k).2 ≅
      (SynAdamsSS Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) n)).Page
          (max 2 ((n : ℤ) + 1)) k :=
  (conv.iso k).symm ≪≫
    synAdams_mod_lambda_eInftyIso_stablePage 𝒮 Syn X n hn k

/-- For a displayed Adams page `r ≥ 2`, the quotient by `λ^(r-1)`
has stabilized by page `r`. -/
noncomputable def synAdams_mod_lambda_pred_eInftyIso_page
    (X : 𝒮) (r : ℕ) (hr : 2 ≤ r) (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).ssData k).eInfty ≅
      (SynAdamsSS Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).Page (r : ℤ) k := by
  have hpage : max 2 ((((r - 1 : ℕ) : ℤ)) + 1) = (r : ℤ) := by
    omega
  have hd := synAdams_mod_lambda_degenerates
    𝒮 Syn X (r - 1) (by omega)
  rw [hpage] at hd
  exact synAdams_eInftyIso_page_of_degenerates
    (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1)) r (by omega) hd k

/-- On the diagonal generator, the limiting Adams page of
`νX/λ^(r-1)` is canonically the `r`-page of `νX`.  The second isomorphism
is the inverse of the actual finite-quotient page map, whose safe-range
inequality is `r-2 < r-1`. -/
noncomputable def nuModLambdaPredGeneratorEInftyIsoPage
    (X : 𝒮) (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) :
    ((SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).ssData
        (s, t, t)).eInfty ≅
      (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ) (s, t, t) := by
  let q := nuModLambdaAdamsPageMap 𝒮 Syn X (r - 1) (r : ℤ) (s, t, t)
  letI : IsIso q :=
    nuModLambdaAdamsPageMapIsIso_of_safe_range 𝒮 Syn X (r - 1)
      (by omega) (r : ℤ) (by omega) s t t (by omega) (by omega)
  exact synAdams_mod_lambda_pred_eInftyIso_page 𝒮 Syn X r hr (s, t, t) ≪≫
    (asIso q).symm

/-- Successor-indexed finite-quotient comparison built from the natural
stabilized-page isomorphism. It identifies the limit for
`nu X / lambda^(n+1)` with page `n+2` of `nu X`. -/
noncomputable def nuModLambdaSuccGeneratorEInftyIsoPage
    (X : 𝒮) (n : ℕ) (s t : ℤ) :
    ((SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) (n + 1))).ssData
        (s, t, t)).eInfty ≅
      (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page
        ((n + 2 : ℕ) : ℤ) (s, t, t) := by
  have hd := synAdams_mod_lambda_degenerates
    𝒮 Syn X (n + 1) (by omega)
  have hpage : max 2 ((((n + 1 : ℕ) : ℤ)) + 1) =
      ((n + 2 : ℕ) : ℤ) := by omega
  rw [hpage] at hd
  let q := nuModLambdaAdamsPageMap 𝒮 Syn X (n + 1)
    ((n + 2 : ℕ) : ℤ) (s, t, t)
  letI : IsIso q :=
    nuModLambdaAdamsPageMapIsIso_of_safe_range 𝒮 Syn X (n + 1)
      (by omega) ((n + 2 : ℕ) : ℤ) (by omega) s t t
      (by omega) (by omega)
  exact synAdams_eInftyIso_page_natAddTwo
      (XModLambdaN ((nu 𝒮 Syn).obj X) (n + 1)) n hd (s, t, t) ≪≫
    (asIso q).symm

/-- In the canonical Adams convergence of `νX/λ^(r-1)`, the associated
graded at the diagonal generator degree is the `r`-page of `νX`.  Thus the
finite λ-quotient comparison is stated directly at the filtered abutment
used by the boundary ESS. -/
noncomputable def nuModLambdaPredGeneratorAssociatedGradedIsoPage
    (X : 𝒮) (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) :
    (synAdamsConvergence Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).filtration.associatedGraded
        s (t - s, t) ≅
      (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ) (s, t, t) := by
  let conv := synAdamsConvergence Syn
    (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))
  have hindex : conv.convergence.reindex (s, t, t) = (s, (t - s, t)) := by
    rw [conv.reindex_eq]
  let e := conv.convergence.iso (s, t, t)
  rw [hindex] at e
  exact e.symm ≪≫
    nuModLambdaPredGeneratorEInftyIsoPage 𝒮 Syn X r hr s t

/-- Every specified diagonal Adams page class has an actual filtered
representative in the finite quotient by `λ^(r-1)`. The representative is
constructed using the epimorphism onto the associated graded; its existence
is not a comparison hypothesis. No boundedness of the filtration is used. -/
theorem nuModLambdaPredGenerator_exists_filteredRepresentative
    (X : 𝒮) (r : ℕ) (hr : 2 ≤ r) (s t : ℤ)
    {T : AddCommGrpCat.{0}} [Projective T]
    (x : T ⟶ (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ) (s, t, t)) :
    ∃ a : T ⟶ Subobject.underlying.obj
        ((synAdamsConvergence Syn
          (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).filtration.F s (t - s, t)),
      a ≫ (synAdamsConvergence Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).filtration.toAssociatedGraded
          s (t - s, t) ≫
        (nuModLambdaPredGeneratorAssociatedGradedIsoPage
          𝒮 Syn X r hr s t).hom = x := by
  let F := (synAdamsConvergence Syn
    (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).filtration
  let e := nuModLambdaPredGeneratorAssociatedGradedIsoPage 𝒮 Syn X r hr s t
  let p := F.toAssociatedGraded s (t - s, t)
  let a := Projective.factorThru (x ≫ e.inv) p
  refine ⟨a, ?_⟩
  change a ≫ p ≫ e.hom = x
  rw [← Category.assoc, Projective.factorThru_comp, Category.assoc,
    e.inv_hom_id, Category.comp_id]

/-- Two filtered representatives of the same specified Adams page class
differ by one higher filtration layer in the finite quotient. This states
the ambiguity as an actual lift, rather than as equality of abstract groups. -/
theorem nuModLambdaPredGenerator_representative_difference
    (X : 𝒮) (r : ℕ) (hr : 2 ≤ r) (s t : ℤ)
    {T : AddCommGrpCat.{0}}
    (a b : T ⟶ Subobject.underlying.obj
      ((synAdamsConvergence Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).filtration.F s (t - s, t)))
    (hab : a ≫ (synAdamsConvergence Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).filtration.toAssociatedGraded
          s (t - s, t) ≫
        (nuModLambdaPredGeneratorAssociatedGradedIsoPage
          𝒮 Syn X r hr s t).hom =
      b ≫ (synAdamsConvergence Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).filtration.toAssociatedGraded
          s (t - s, t) ≫
        (nuModLambdaPredGeneratorAssociatedGradedIsoPage
          𝒮 Syn X r hr s t).hom) :
    ∃ c : T ⟶ Subobject.underlying.obj
        ((synAdamsConvergence Syn
          (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).filtration.F
            (s + 1) (t - s, t)),
      c ≫ Subobject.ofLE _ _
        ((synAdamsConvergence Syn
          (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).filtration.mono s (t - s, t))
        = a - b := by
  let F := (synAdamsConvergence Syn
    (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).filtration
  let e := nuModLambdaPredGeneratorAssociatedGradedIsoPage 𝒮 Syn X r hr s t
  let i := Subobject.ofLE (F.F (s + 1) (t - s, t)) (F.F s (t - s, t))
    (F.mono s (t - s, t))
  have hab' : a ≫ F.toAssociatedGraded s (t - s, t) =
      b ≫ F.toAssociatedGraded s (t - s, t) := by
    apply (cancel_mono e.hom).1
    simpa only [Category.assoc] using hab
  have hz : (a - b) ≫ cokernel.π i = 0 := by
    change (a - b) ≫ F.toAssociatedGraded s (t - s, t) = 0
    rw [Preadditive.sub_comp, hab', sub_self]
  exact ⟨Abelian.monoLift i (a - b) hz, Abelian.monoLift_comp i (a - b) hz⟩

/-! ### Actual homotopy representatives of diagonal page classes -/

/-- The actual detection map from the filtered Hom group of
`νX/λ^(r-1)` onto the diagonal `r`-page of `νX`. The page identification
has already been constructed from E₂ support and the actual quotient map. -/
noncomputable def nuModLambdaPredGeneratorDetection
    (X : 𝒮) (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) :
    synAdamsFiltration Syn (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))
      (t - s) t s →+
        ↑((SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ) (s, t, t)) :=
  (nuModLambdaPredGeneratorAssociatedGradedIsoPage 𝒮 Syn X r hr s t).hom.hom.comp
    ((synAdamsConvergence Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).homotopyGradedProjection
        s (t - s, t))

/-- Every diagonal page class is detected by an actual homotopy class
in the finite quotient, without any projectivity hypothesis on that class. -/
theorem nuModLambdaPredGeneratorDetection_surjective
    (X : 𝒮) (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) :
    Function.Surjective (nuModLambdaPredGeneratorDetection 𝒮 Syn X r hr s t) :=
  ((AddCommGrpCat.epi_iff_surjective
    (nuModLambdaPredGeneratorAssociatedGradedIsoPage 𝒮 Syn X r hr s t).hom).mp
      inferInstance).comp
    ((synAdamsConvergence Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).homotopyGradedProjection_surjective
        s (t - s, t))

/-- The kernel is exactly the next actual Adams-filtration subgroup.
Thus a nonzero page class has filtration exactly `s`, not merely at least
`s`, in the finite quotient. -/
theorem nuModLambdaPredGeneratorDetection_eq_zero_iff
    (X : 𝒮) (r : ℕ) (hr : 2 ≤ r) (s t : ℤ)
    (a : synAdamsFiltration Syn (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))
      (t - s) t s) :
    nuModLambdaPredGeneratorDetection 𝒮 Syn X r hr s t a = 0 ↔
      a.val ∈ synAdamsFiltration Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1)) (t - s) t (s + 1) := by
  let A := synAdamsConvergence Syn (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))
  let e := nuModLambdaPredGeneratorAssociatedGradedIsoPage 𝒮 Syn X r hr s t
  have hinj : Function.Injective e.hom :=
    (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance
  unfold nuModLambdaPredGeneratorDetection
  change e.hom.hom (A.homotopyGradedProjection s (t - s, t) a) = 0 ↔ _
  rw [← A.homotopyGradedProjection_eq_zero_iff s (t - s, t) a]
  constructor
  · intro h
    apply hinj
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- Equality of detected page classes is equivalent to the difference
of their actual representatives belonging to the next filtration layer. -/
theorem nuModLambdaPredGeneratorDetection_eq_iff
    (X : 𝒮) (r : ℕ) (hr : 2 ≤ r) (s t : ℤ)
    (a b : synAdamsFiltration Syn (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))
      (t - s) t s) :
    nuModLambdaPredGeneratorDetection 𝒮 Syn X r hr s t a =
        nuModLambdaPredGeneratorDetection 𝒮 Syn X r hr s t b ↔
      a.val - b.val ∈ synAdamsFiltration Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1)) (t - s) t (s + 1) := by
  rw [← sub_eq_zero, ← map_sub]
  exact nuModLambdaPredGeneratorDetection_eq_zero_iff 𝒮 Syn X r hr s t (a - b)

/-- A specified diagonal Adams class has a representative that is an
actual sphere map into the finite quotient. The nonzero condition is
equivalent to failure of membership in the next filtration subgroup. -/
theorem nuModLambdaPredGenerator_exists_actualRepresentative
    (X : 𝒮) (r : ℕ) (hr : 2 ≤ r) (s t : ℤ)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ) (s, t, t)) :
    ∃ (a : Smn (Syn := Syn) (t - s) t ⟶
        XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))
      (ha : a ∈ synAdamsFiltration Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1)) (t - s) t s),
      nuModLambdaPredGeneratorDetection 𝒮 Syn X r hr s t ⟨a, ha⟩ = x ∧
      (x ≠ 0 ↔ a ∉ synAdamsFiltration Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1)) (t - s) t (s + 1)) := by
  obtain ⟨a, ha⟩ := nuModLambdaPredGeneratorDetection_surjective 𝒮 Syn X r hr s t x
  refine ⟨a.val, a.property, ha, ?_⟩
  rw [← ha]
  exact not_congr (nuModLambdaPredGeneratorDetection_eq_zero_iff 𝒮 Syn X r hr s t a)

/-- For the first λ-quotient, the second Adams page is supported on `t=w`.
The support condition is proved from the existing finite-quotient theorem. -/
theorem synAdams_mod_lambda_one_e2_diagonal (X : 𝒮)
    (s t w : ℤ) (h : t ≠ w) :
    IsZero ((SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) 1)).Page 2
      (s, t, w)) := by
  apply synAdams_nu_mod_lambda_e2_isZero_of_outside 𝒮 Syn X 1 (by decide) s t w
  omega

/-- The synthetic Adams spectral sequence of `νX/λ` collapses at E₂. -/
theorem synAdams_mod_lambda_one_degenerates (X : 𝒮) :
    (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) 1)).DegeneratesAt 2 :=
  synAdams_degenerates_of_e2_diagonal _
    (synAdams_mod_lambda_one_e2_diagonal 𝒮 Syn X)

/-- All meaningful finite Adams pages of `νX/λ` identify with E₂. -/
noncomputable def synAdams_mod_lambda_one_pageIso (X : 𝒮)
    (r : ℤ) (hr : 2 ≤ r) (k : ℤ × ℤ × ℤ) :
    (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) 1)).Page r k ≅
      (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) 1)).Page 2 k :=
  synAdams_pageIso_e2_of_diagonal _
    (synAdams_mod_lambda_one_e2_diagonal 𝒮 Syn X) r hr k

/-- The limiting Adams page of `νX/λ` is its second page. This is the
source-side input to the λ-boundary ESS, not the full ESS comparison. -/
noncomputable def synAdams_mod_lambda_one_eInftyIso (X : 𝒮)
    (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) 1)).ssData k).eInfty ≅
      (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) 1)).Page 2 k :=
  synAdams_eInftyIso_e2_of_diagonal _
    (synAdams_mod_lambda_one_e2_diagonal 𝒮 Syn X) k

/-- Any given convergence witness for `νX/λ` identifies its associated
graded with E₂; no additional degeneration hypothesis is needed. -/
noncomputable def synAdams_mod_lambda_one_associatedGradedIso (X : 𝒮)
    {A : ℤ × ℤ → AddCommGrpCat.{0}} {F : Filtration A}
    (conv : Convergence
      (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) 1)) A F)
    (k : ℤ × ℤ × ℤ) :
    F.associatedGraded (conv.reindex k).1 (conv.reindex k).2 ≅
      (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) 1)).Page 2 k :=
  (conv.iso k).symm ≪≫ synAdams_mod_lambda_one_eInftyIso 𝒮 Syn X k

end KIPBase.Synthetic
