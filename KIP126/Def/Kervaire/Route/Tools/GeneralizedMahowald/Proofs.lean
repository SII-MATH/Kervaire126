import KIP126.Def.Kervaire.Route.Tools.GeneralizedMahowald.Predicates
import KIP126.Def.Kervaire.Route.Tools.Inputs.Data

import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
import KIP126.Def.Synthetic.Detection.Proofs
import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs

/-! Reusable paper-rule proof and explicit unfinished obligations.
No computation delivery or selected stage witness is a premise. The theorem
retains the displayed mathematical comparison premises on the same model; source-to-model assembly remains in Interface. Existing public theorem
names are retained for compatibility. The remaining proof gaps certify no log rows. -/
namespace KIP126.Main.Solution.Tools

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Kervaire.Route KIP126.Classical.Adams
open KIP126.Literature.Route

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

open KIP126.Synthetic.SpectralSequence KIP126.Classical.Adams.PageRepresentatives
open KIP126.Core.SpectralSequence KIP126.Synthetic.PageExtension

/- In the top nonzero weight of a finite quotient, two detected targets
coincide as actual homotopy classes. Thus an extension gives a strict
preimage of any specified representative with that target label. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem finite_top_extension_preimage
    (synthetic : SyntheticInputs D) (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (r : ℕ) (n s t : ℤ)
    (x : E2 H (X.obj D.auxiliary) s t)
    (y : E2 H (Y.obj D.auxiliary) (s+n) (t+n))
    (W : FiniteExtensionWitness D X Y f r n s t x y)
    (htop : (r:ℤ)-1 ≤ n-normalizedExponent H f+1)
    (b : BiHom (t-s) (t+normalizedExponent H f)
      (XModLambdaN (D.nu.functor.obj (Y.obj D.auxiliary)) (r-1)))
    (hb : Detects (D.convergence (.quotient (r-1) (.nu Y)))
      (s+n,(t-s)+(s+n),t+normalizedExponent H f)
      (finiteTargetForExtension D X Y f (r-1) n s t W.length_lower y)
      (homotopyRegrade (by dsimp; omega) rfl b)) :
    ∃ a : BiHom (t-s) (t+normalizedExponent H f)
      ((SyntheticObject.quotient (r-1) (extensionSourceObject D X Y f)).obj D.nu D.auxiliary),
      a ≫ finiteExtensionMap D X Y f (r-1) = b ∧
      Detects (D.convergence (.quotient (r-1) (extensionSourceObject D X Y f)))
        (s,(t-s)+s,t+normalizedExponent H f)
        (finiteSourceForExtension D X Y f (r-1) s t x)
        (homotopyRegrade (by dsimp; omega) rfl a) := by
  have finite_quotient_high_filtration_zero_int
      (synthetic : SyntheticInputs D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
      (a : BiHom m w (XModLambdaN (D.nu.functor.obj (X.obj D.auxiliary)) q))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) : a = 0 := by
    have hz (j : ℤ) (hj : s ≤ j) :
        IsZero (((D.family.nuQuotient D.nu (X.obj D.auxiliary) q).sequence.ssData
          (j,m+j,w)).eInfty) := by
      have hwin : ¬ (0 ≤ (m+j)-w ∧ (m+j)-w < q) := by omega
      haveI : Subsingleton (finiteEInftyModel H (X.obj D.auxiliary) q (j,m+j) w) := by
        simp only [finiteEInftyModel, hwin, ite_false]
        infer_instance
      haveI : Subsingleton (((D.family.nuQuotient D.nu (X.obj D.auxiliary) q).sequence.ssData
          (j,m+j,w)).eInfty) :=
        (synthetic.eInfty.presentation.finite (X.obj D.auxiliary) q hq (j,m+j) w).injective.subsingleton
      exact ModuleCat.isZero_of_subsingleton _
    apply D.homotopySeparated (.quotient q (.nu X)) m w a
    intro j
    by_cases hj : s ≤ (j:ℤ)
    · exact ((D.convergence (.quotient q (.nu X))).filtrationAtLeast_iff_of_eInfty_isZero
        s j m w hj (fun k hk _ => hz k hk) a).mp ha
    · exact towerFiltrationSubmodule_antitone (nuCoefficientUnit H.unit D.nu) _ (m,w)
        (by omega) ha
  have finite_top_detection_unique
      (synthetic : SyntheticInputs D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (s t w : ℤ) (hwindow : (q:ℤ) ≤ t+1-w)
      (x : (D.family.nuQuotient D.nu (X.obj D.auxiliary) q).E₂ (s,t,w))
      (a b : BiHom (t-s) w (XModLambdaN (D.nu.functor.obj (X.obj D.auxiliary)) q))
      (ha : Detects (D.convergence (.quotient q (.nu X))) (s,t,w) x a)
      (hb : Detects (D.convergence (.quotient q (.nu X))) (s,t,w) x b) : a=b := by
    apply sub_eq_zero.mp
    exact finite_quotient_high_filtration_zero_int synthetic X q hq (t-s) w (s+1)
      (by omega) (a-b)
      (detects_sub_filtration (D.convergence (.quotient q (.nu X))) (s,t,w) ha hb)
  have extension_equation_representatives
      {A B : Syn} (g : A ⟶ B)
      (ca : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family A)
      (cb : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family B)
      (p : ℤ × ℤ) (s n : ℤ)
      (x : ((D.family.obj A).sequence.ssData (s,p.1+s,p.2)).eInfty)
      (y : ((D.family.obj B).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
      (h : ExtensionEquation g ca cb p s n x y) :
      ∃ (a : (Subobject.underlying.obj
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p) : ModuleCat ℤ))
        (b : (Subobject.underlying.obj
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) B).F (s+n) p) : ModuleCat ℤ)),
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p).arrow a ≫ g =
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) B).F (s+n) p).arrow b ∧
        (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s p a =
          (extensionSourceIso (nuCoefficientUnit H.unit D.nu) g ca p s).hom x ∧
        (towerFiltration (nuCoefficientUnit H.unit D.nu) B).toAssociatedGraded (s+n) p b =
          (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g cb p (s+n)).hom y := by
    obtain ⟨hn, ⟨z,hz⟩⟩ := h
    refine ⟨z.1 (ULift.up 1), z.2 (ULift.up 1), ?_, ?_, ?_⟩
    · have he := congrArg (fun e => e.2.2 (ULift.up 1)) hz
      dsimp only [FilteredComplex.Solutions.equation] at he
      simp only [extensionComplex, underlyingComplex_d_one] at he
      change (syntheticHomotopyMap g p)
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p).arrow (z.1 (ULift.up 1))) -
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) B).F (s+n) p).arrow (z.2 (ULift.up 1)) = 0 at he
      exact sub_eq_zero.mp he
    · have he := congrArg (fun e => e.1 (ULift.up 1)) hz
      dsimp only [FilteredComplex.Solutions.equation] at he
      change (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s p
        (z.1 (ULift.up 1)) = elementMap _ (ULift.up 1) at he
      simpa [elementMap] using he
    · have he := congrArg (fun e => e.2.1 (ULift.up 1)) hz
      dsimp only [FilteredComplex.Solutions.equation] at he
      change (towerFiltration (nuCoefficientUnit H.unit D.nu) B).toAssociatedGraded (s+n) p
        (z.2 (ULift.up 1)) = elementMap _ (ULift.up 1) at he
      simpa [elementMap] using he
  have source_frame_detects
      {A B : Syn} (g : A ⟶ B)
      (ca : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family A)
      (p : ℤ × ℤ) (s : ℤ)
      (x : ((D.family.obj A).sequence.ssData (s,p.1+s,p.2)).eInfty)
      (x0 : (D.family.obj A).E₂ (s,p.1+s,p.2))
      (hx : HasInfinityRepresentative _ 2 _ x0 x)
      (a : (Subobject.underlying.obj
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p) : ModuleCat ℤ))
      (ha : (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s p a =
        (extensionSourceIso (nuCoefficientUnit H.unit D.nu) g ca p s).hom x) :
      Detects ca (s,p.1+s,p.2) x0
        (homotopyRegrade (by dsimp; omega) rfl
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p).arrow a)) := by
    have lift_frame (m m' w s : ℤ) (hm : m=m') {V : ModuleCat.{v} ℤ} (e : V)
        (I : V ≅ (towerFiltration (nuCoefficientUnit H.unit D.nu) A).associatedGraded s (m',w))
        (a : (Subobject.underlying.obj
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m,w)) : ModuleCat ℤ))
        (ha : (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s (m,w) a =
          (I ≪≫ eqToIso (congrArg
            (fun z => (towerFiltration (nuCoefficientUnit H.unit D.nu) A).associatedGraded s (z,w)) hm.symm)).hom e) :
        ∃ a' : (Subobject.underlying.obj
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m',w)) : ModuleCat ℤ),
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m',w)).arrow a' =
            homotopyRegrade hm rfl (((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m,w)).arrow a) ∧
          I.hom e = (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s (m',w) a' := by
      subst m'
      refine ⟨a,rfl,?_⟩
      simpa only [eqToIso_refl, Iso.trans_refl] using ha.symm
    obtain ⟨a',ha',hga⟩ := lift_frame p.1 ((p.1+s)-s) p.2 s (by omega) x
      (ca.identification (s,p.1+s,p.2)) a ha
    exact ⟨x,hx,a',ha',hga⟩
  let unit := nuCoefficientUnit H.unit D.nu
  let A := (SyntheticObject.quotient (r-1) (extensionSourceObject D X Y f)).obj D.nu D.auxiliary
  let B := XModLambdaN (D.nu.functor.obj (Y.obj D.auxiliary)) (r-1)
  let p := (t-s,t+normalizedExponent H f)
  obtain ⟨a,b',hab,hax,hby⟩ := extension_equation_representatives
    (finiteExtensionMap D X Y f (r-1)) _ _ p s n W.source W.target W.equation
  have ha := source_frame_detects (finiteExtensionMap D X Y f (r-1))
    (D.convergence (.quotient (r-1) (extensionSourceObject D X Y f))) p s W.source
    _ W.source_rep a hax
  have hb' := source_frame_detects (𝟙 B)
    (D.convergence (.quotient (r-1) (.nu Y))) p (s+n) W.target
    _ W.target_rep b' hby
  have hr := W.page_ge_two
  have heq := finite_top_detection_unique synthetic Y (r-1) (by omega)
    (s+n) ((t-s)+(s+n)) (t+normalizedExponent H f) (by omega)
    _ _ _ hb' hb
  have heq' : ((towerFiltration unit B).F (s+n) p).arrow b' = b := by
    have hinj (u v w : ℤ) (huv : u=v) :
        Function.Injective (homotopyRegrade huv (rfl : w=w) (X:=B)) := by
      subst v
      exact Function.injective_id
    exact hinj _ _ _ _ heq
  refine ⟨((towerFiltration unit A).F s p).arrow a, hab.trans heq', ha⟩

/- Strictly related homotopy representatives give an extension equation
with the specified detected labels, by using their filtration witnesses. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem extension_equation_of_detected_pair
    {A B : Syn} (g : A ⟶ B)
    (ca : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family A)
    (cb : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family B)
    (p : ℤ × ℤ) (s n : ℤ) (hn : 0 ≤ n)
    (x0 : (D.family.obj A).E₂ (s,p.1+s,p.2))
    (y0 : (D.family.obj B).E₂ (s+n,p.1+(s+n),p.2))
    (a : BiHom p.1 p.2 A) (b : BiHom p.1 p.2 B)
    (ha : Detects ca (s,p.1+s,p.2) x0 (homotopyRegrade (by dsimp; omega) rfl a))
    (hb : Detects cb (s+n,p.1+(s+n),p.2) y0 (homotopyRegrade (by dsimp; omega) rfl b))
    (hab : a ≫ g=b) :
    ∃ x y, HasInfinityRepresentative _ 2 _ x0 x ∧
      HasInfinityRepresentative _ 2 _ y0 y ∧ ExtensionEquation g ca cb p s n x y := by
  have frame_of_source_detects
      {A B : Syn} (g : A ⟶ B)
      (ca : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family A)
      (p : ℤ × ℤ) (s : ℤ)
      (x0 : (D.family.obj A).E₂ (s,p.1+s,p.2))
      (a0 : BiHom p.1 p.2 A)
      (ha0 : Detects ca (s,p.1+s,p.2) x0 (homotopyRegrade (by dsimp; omega) rfl a0)) :
      ∃ x : ((D.family.obj A).sequence.ssData (s,p.1+s,p.2)).eInfty,
        HasInfinityRepresentative _ 2 _ x0 x ∧
        ∃ a : (Subobject.underlying.obj
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p) : ModuleCat ℤ),
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p).arrow a = a0 ∧
          (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s p a =
            (extensionSourceIso (nuCoefficientUnit H.unit D.nu) g ca p s).hom x := by
    have lower_frame (m m' w s : ℤ) (hm : m=m') {V : ModuleCat.{v} ℤ} (e : V)
        (I : V ≅ (towerFiltration (nuCoefficientUnit H.unit D.nu) A).associatedGraded s (m',w))
        (a0 : BiHom m w A)
        (a' : (Subobject.underlying.obj
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m',w)) : ModuleCat ℤ))
        (ha' : ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m',w)).arrow a' = homotopyRegrade hm rfl a0)
        (hga : I.hom e = (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s (m',w) a') :
        ∃ a : (Subobject.underlying.obj
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m,w)) : ModuleCat ℤ),
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m,w)).arrow a = a0 ∧
          (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s (m,w) a =
            (I ≪≫ eqToIso (congrArg
              (fun z => (towerFiltration (nuCoefficientUnit H.unit D.nu) A).associatedGraded s (z,w)) hm.symm)).hom e := by
      subst m'
      exact ⟨a',ha',hga.symm⟩
    obtain ⟨e,he,a',ha',hga⟩ := ha0
    obtain ⟨a,ha,hg⟩ := lower_frame p.1 ((p.1+s)-s) p.2 s (by omega) e
      (ca.identification (s,p.1+s,p.2)) a0 a' ha' hga
    exact ⟨e,he,a,ha,hg⟩
  obtain ⟨x,hx,a',ha',hax⟩ := frame_of_source_detects g ca p s x0 a ha
  obtain ⟨y,hy,b',hb',hby⟩ := frame_of_source_detects (𝟙 B) cb p (s+n) y0 b hb
  have hom_ext_one {V : ModuleCat.{v} ℤ}
      (f g : ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ V)
      (h : f (ULift.up 1) = g (ULift.up 1)) : f=g := by
    apply ModuleCat.hom_ext
    have hh : f.hom.comp ULift.moduleEquiv.symm.toLinearMap =
        g.hom.comp ULift.moduleEquiv.symm.toLinearMap := LinearMap.ext_ring h
    ext z
    exact DFunLike.congr_fun hh z.down
  refine ⟨x,y,hx,hy,hn,⟨⟨elementMap a',elementMap b'⟩,?_⟩⟩
  apply Prod.ext
  · apply hom_ext_one
    change (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s p
      (elementMap a' (ULift.up 1)) = elementMap _ (ULift.up 1)
    simpa [elementMap] using hax
  · apply Prod.ext
    · apply hom_ext_one
      change (towerFiltration (nuCoefficientUnit H.unit D.nu) B).toAssociatedGraded (s+n) p
        (elementMap b' (ULift.up 1)) = elementMap _ (ULift.up 1)
      have hby' : (towerFiltration (nuCoefficientUnit H.unit D.nu) B).toAssociatedGraded (s+n) p b' =
          (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g cb p (s+n)).hom y := hby
      simpa [elementMap] using hby'
    · apply hom_ext_one
      change (syntheticHomotopyMap g p)
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p).arrow (elementMap a' (ULift.up 1))) -
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) B).F (s+n) p).arrow (elementMap b' (ULift.up 1)) = 0
      have hab' : syntheticHomotopyMap g p a = (b : syntheticHomotopy B p) := hab
      simpa [elementMap, ha', hb'] using sub_eq_zero.mpr hab'

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- MainPaper Theorem 6.12. May's signed smash-boundary input supplies
Lemma 6.11's geometric step; the compatible normalized triangle and both
no-crossing alternatives remain explicit in the conclusion's predicate. -/
theorem generalizedMahowald (synthetic : SyntheticInputs D) (may : MayInput Syn)
    (T : TriangleData D.auxiliary) :
    KIP126.Kervaire.Route.Tools.GeneralizedMahowaldLaw D T := by
  intro he htriangle n m l s t
  dsimp only
  intro x y xBar yBar suspendedX hn hm hl
    hx hy hxBar hyBar hsusp hh hd hcross hg
  let eg : ℤ := normalizedExponent H T.g
  let ef : ℤ := normalizedExponent H T.f
  let eh : ℤ := normalizedExponent H T.h
  let pg : ℕ := (m-eg+2).toNat
  let q : ℕ := pg-1
  let i : ℕ := (n+l+eg-1).toNat
  let Q : ℕ := (n+m+eh).toNat
  let sf : ℤ := s+l
  let tf : ℤ := t+l-1
  have hpg : 2 ≤ pg := by dsimp [pg,eg]; omega
  have hq : 0 < q := by dsimp [q]; omega
  have hqZ : (q:ℤ)=m-eg+1 := by dsimp [q,pg]; omega
  have hi : 0 < i := by dsimp [i,eg,ef,eh] at *; omega
  have hiZ : (i:ℤ)=n+l+eg-1 := by dsimp [i,eg,ef,eh] at *; omega
  have hQ : 0 < Q := by dsimp [Q,eg,ef,eh] at *; omega
  have hQZ : (Q:ℤ)=n+m+eh := by dsimp [Q,eg,ef,eh] at *; omega
  have hn0 : 0 ≤ n := by have := Nat.zero_le (normalizedExponent H T.f); omega
  have hnf : ef ≤ n := by dsimp [ef]; omega
  let Wg : FiniteExtensionWitness D T.Y T.Z T.g pg m (sf+n) (tf+n) y yBar :=
    Classical.choice hg
  let Zν := D.nu.functor.obj (T.Z.obj D.auxiliary)
  let boundary (aZ : BiHom (t-s) t (XModLambdaN Zν i)) :
      BiHom ((tf+n)-(sf+n)) (tf+n+eg) (XModLambdaN Zν q) :=
    homotopyRegrade (by dsimp [tf,sf]; omega) (by dsimp [tf]; omega)
      (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN Zν q)
        (by simpa only [Nat.add_sub_cancel_left] using
          (aZ ≫ ((D.quotientTower Zν).triangle hi (show i < i + q by omega)).delta)))
  have boundary_representative :
      ∃ aZ : BiHom (t-s) t (XModLambdaN Zν i),
        Detects (D.convergence (.quotient i (.nu T.Z))) (s,t,t)
          (regradeE2 (by simp) (finiteTargetLabel D T.Z i s t 0 xBar)) aZ ∧
        Detects (D.convergence (.quotient q (.nu T.Z)))
          (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg)
          (finiteTargetForExtension D T.Y T.Z T.g q m (sf+n) (tf+n) Wg.length_lower yBar)
          (homotopyRegrade (by dsimp; omega) rfl (boundary aZ)) := by
    -- MH1, MainPaper lines 1869–1894: represent d_r(xBar)=yBar by
    -- the ACTUAL delta_(i,i+q) in this quotient tower. Its target lies
    -- in the top weight of the q=m-e(g)+1 quotient. The missing step
    -- is the delta/classical-label comparison, retaining the chosen
    -- trigradings; it is not an assumed strict g-preimage.
    sorry
  obtain ⟨aZ,haZ,hdelta⟩ := boundary_representative
  have may_boundary_lift :
      ∀ ag : BiHom ((tf+n)-(sf+n)) (tf+n+eg)
          ((SyntheticObject.quotient q (extensionSourceObject D T.Y T.Z T.g)).obj D.nu D.auxiliary),
        Detects (D.convergence (.quotient q (extensionSourceObject D T.Y T.Z T.g)))
          (sf+n,((tf+n)-(sf+n))+(sf+n),tf+n+eg)
          (finiteSourceForExtension D T.Y T.Z T.g q (sf+n) (tf+n) y)
          (homotopyRegrade (by dsimp; omega) rfl ag) →
        ag ≫ finiteExtensionMap D T.Y T.Z T.g q = boundary aZ →
        (∃ c : BiHom (tf-sf) tf (XModLambdaN (nuZero D T.X) Q),
          c ≫ (D.quotientTower (nuZero D T.X)).rho 1 Q hQ = firstLabel D T.X sf tf x) ∧
        ∃ y' : E2 H (T.Y.obj D.auxiliary) (sf+n) (tf+n),
          y'-y ∈ boundaries H (T.Y.obj D.auxiliary) (n+m+l-(m-eg)) (sf+n,tf+n) ∧
          ∃ (af : BiHom (tf-sf) (tf+ef)
                ((SyntheticObject.quotient Q (extensionSourceObject D T.X T.Y T.f)).obj D.nu D.auxiliary))
            (bf : BiHom (tf-sf) (tf+ef)
                (XModLambdaN (D.nu.functor.obj (T.Y.obj D.auxiliary)) Q)),
            Detects (D.convergence (.quotient Q (extensionSourceObject D T.X T.Y T.f)))
              (sf,(tf-sf)+sf,tf+ef) (finiteSourceForExtension D T.X T.Y T.f Q sf tf x)
              (homotopyRegrade (by dsimp; omega) rfl af) ∧
            Detects (D.convergence (.quotient Q (.nu T.Y)))
              (sf+n,(tf-sf)+(sf+n),tf+ef) (finiteTargetForExtension D T.X T.Y T.f Q n sf tf hnf y')
              (homotopyRegrade (by dsimp; omega) rfl bf) ∧
            af ≫ finiteExtensionMap D T.X T.Y T.f Q = bf := by
    intro ag hag hstrict
    -- MH2, MainPaper lines 1875–1917: hcross synchronizes the h-extension
    -- with the delta representative aZ; htriangle and may.boundary then
    -- give the actual lift through lambda^Q and the strict f_Q square.
    -- hsusp identifies the ordinary suspension label with x. Transport
    -- through lambda powers must retain the finite B_(n+m+l-(m-e(g)))
    -- ambiguity in y', not merely equality in the infinity quotient.
    -- May supplies a signed homotopy relation; removing its sign requires
    -- the mod-2 label comparison, not an assertion of characteristic two
    -- for the homotopy groups. No FiniteExtension conclusion is assumed here.
    sorry
  obtain ⟨ag,hag,hagDetect⟩ := finite_top_extension_preimage D synthetic
    T.Y T.Z T.g pg m (sf+n) (tf+n) y yBar Wg (by dsimp [pg,eg]; omega)
    (boundary aZ) hdelta
  obtain ⟨⟨c,hc⟩,y',hcong,af,bf,haf,hbf,hfstrict⟩ := may_boundary_lift ag hagDetect hag
  have hxLater : IsCycle H (T.X.obj D.auxiliary) (n+m+eh) (sf,tf) x := by
    refine ⟨by dsimp [ef,eg,eh] at *; omega,?_⟩
    have hc' := (synthetic.finite_lift T.X Q hQ sf tf x).mpr ⟨c,hc⟩
    simpa only [hQZ] using hc'
  have hyLater : IsCycle H (T.Y.obj D.auxiliary)
      (((Q+1:ℕ):ℤ)-1-n+normalizedExponent H T.f) (sf+n,tf+n) y' := by
    have hlevel : ((Q+1:ℕ):ℤ)-1-n+normalizedExponent H T.f = m-eg+1 := by
      simp only [Nat.cast_add,Nat.cast_one,hQZ]
      dsimp [ef,eg,eh] at *
      omega
    rw [hlevel]
    refine ⟨by dsimp [eg]; omega,?_⟩
    have hby := boundaries_le_cycles H (T.Y.obj D.auxiliary) (sf+n,tf+n)
      (n+m+l-(m-eg)) (m-eg+1) hcong
    have hadd := (cycles H (T.Y.obj D.auxiliary) (m-eg+1) (sf+n,tf+n)).add_mem hby hy.2
    simpa only [sub_add_cancel] using hadd
  obtain ⟨xf,yf,hxf,hyf,heq⟩ := extension_equation_of_detected_pair D
    (finiteExtensionMap D T.X T.Y T.f Q) _ _ (tf-sf,tf+ef) sf n hn0 _ _ af bf haf hbf hfstrict
  refine ⟨hxLater,y',?_,⟨by dsimp [ef,eg,eh] at *; omega,hcong⟩⟩
  have hpage : (n+m+1+normalizedExponent H T.h).toNat = Q+1 := by
    dsimp [Q,eh,ef,eg] at *
    omega
  rw [hpage]
  refine ⟨{
    page_ge_two := by omega
    length_lower := hnf
    length_upper := by simp only [Nat.cast_add,Nat.cast_one,hQZ]; dsimp [ef,eg,eh] at *; omega
    source_cycle := by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,hQZ] using hxLater
    target_cycle := hyLater
    source := xf
    target := yf
    source_rep := hxf
    target_rep := hyf
    equation := heq }⟩

end KIP126.Main.Solution.Tools
