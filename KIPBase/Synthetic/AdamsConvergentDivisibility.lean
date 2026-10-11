import KIPBase.Synthetic.GeometricAdamsFree
import KIPBase.Synthetic.Rigidity

/-!
# Divisibility from the free lambda E2 page and Adams convergence

The free-lambda description gives divisibility of every correction leading
term.  This file supplies the convergence step: vanishing of all successive
graded terms pushes a filtered homotopy class arbitrarily deep, Hausdorffness
kills the resulting infinitely filtered class, and lambda-cofiber exactness
turns that vanishing into actual lambda divisibility.
-/

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v u' v'

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]

namespace SynAdamsConvergenceData

variable {X : Syn}

/-- Hausdorff Adams convergence kills an actual homotopy class lying in
every filtration layer.  This is the elementwise form needed after the
successive correction process. -/
theorem homotopy_eq_zero_of_mem_all
    (A : SynAdamsConvergenceData X) (degree : ℤ × ℤ)
    (hH : A.filtration.IsHausdorffAt degree)
    (a : Smn (Syn := Syn) degree.1 degree.2 ⟶ X)
    (ha : ∀ s : ℤ,
      a ∈ synAdamsFiltration Syn X degree.1 degree.2 s) :
    a = 0 := by
  let x := (A.abutmentEquiv degree).symm a
  let f : AddCommGrpCat.of ℤ ⟶ A.abutment degree :=
    AddCommGrpCat.ofHom
      { toFun := fun z => z • x
        map_zero' := zero_zsmul x
        map_add' := fun p q => add_zsmul x p q }
  have hle : ∀ s : ℤ, imageSubobject f ≤ A.filtration.F s degree := by
    intro s
    let xs := (A.filtrationEquiv s degree).symm ⟨a, ha s⟩
    let g : AddCommGrpCat.of ℤ ⟶
        Subobject.underlying.obj (A.filtration.F s degree) :=
      AddCommGrpCat.ofHom
        { toFun := fun z => z • xs
          map_zero' := zero_zsmul xs
          map_add' := fun p q => add_zsmul xs p q }
    have hx : (A.filtration.F s degree).arrow.hom xs = x := by
      apply (A.abutmentEquiv degree).injective
      calc
        A.abutmentEquiv degree
            ((A.filtration.F s degree).arrow.hom xs) =
            (A.filtrationEquiv s degree xs).1 :=
          A.filtrationEquiv_comm s degree xs
        _ = a := congrArg Subtype.val
          ((A.filtrationEquiv s degree).apply_symm_apply ⟨a, ha s⟩)
        _ = A.abutmentEquiv degree x :=
          ((A.abutmentEquiv degree).apply_symm_apply a).symm
    apply imageSubobject_le f g
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change (A.filtration.F s degree).arrow.hom (z • xs) = z • x
    rw [map_zsmul, hx]
  have hS : imageSubobject f = ⊥ := hH (imageSubobject f) hle
  have hi : image.ι f = 0 := by
    apply (cancel_epi (imageSubobjectIso f).hom).mp
    rw [imageSubobject_arrow]
    rw [← Subobject.ofLE_arrow
      (show imageSubobject f ≤ (⊥ : Subobject (A.abutment degree))
        from le_of_eq hS)]
    simp only [Subobject.bot_arrow, comp_zero]
  have hf : f = 0 := eq_zero_of_image_eq_zero hi
  have hx0 : x = 0 := by
    have h := ConcreteCategory.congr_hom hf (1 : ℤ)
    simpa [f] using h
  calc
    a = A.abutmentEquiv degree x :=
      ((A.abutmentEquiv degree).apply_symm_apply a).symm
    _ = A.abutmentEquiv degree 0 := congrArg (A.abutmentEquiv degree) hx0
    _ = 0 := map_zero _

/-- If every second-page component above a specified filtration vanishes,
then a class in that filtration is zero under Hausdorff Adams convergence.
The proof repeatedly uses `gr^j = 0` to move the same class from filtration
`j` to filtration `j+1`; no boundedness assumption is used. -/
theorem homotopy_eq_zero_of_e2_vanishing_above
    (A : SynAdamsConvergenceData X) (degree : ℤ × ℤ)
    (hH : A.filtration.IsHausdorffAt degree)
    (s0 : ℤ) (a : Smn (Syn := Syn) degree.1 degree.2 ⟶ X)
    (ha : a ∈ synAdamsFiltration Syn X degree.1 degree.2 s0)
    (hzero : ∀ j : ℤ, s0 ≤ j →
      IsZero ((SynAdamsSS Syn X).Page 2
        (j, degree.1 + j, degree.2))) :
    a = 0 := by
  have hdeep : ∀ k : ℕ,
      a ∈ synAdamsFiltration Syn X degree.1 degree.2
        (s0 + (k : ℤ)) := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih =>
      let j : ℤ := s0 + (k : ℤ)
      let ak : synAdamsFiltration Syn X degree.1 degree.2 j := ⟨a, ih⟩
      have hE2 : IsZero ((SynAdamsSS Syn X).Page 2
          (j, degree.1 + j, degree.2)) := hzero j (by omega)
      have hEinf : IsZero (((SynAdamsSS Syn X).ssData
          (j, degree.1 + j, degree.2)).eInfty) :=
        synAdams_eInfty_isZero_of_e2 X _ hE2
      have hreindex : A.convergence.reindex
          (j, degree.1 + j, degree.2) = (j, degree) := by
        rw [A.reindex_eq]
        ext <;> dsimp <;> omega
      have hgr : IsZero (A.filtration.associatedGraded j degree) := by
        have hz := hEinf.of_iso
          (A.convergence.iso (j, degree.1 + j, degree.2)).symm
        rw [hreindex] at hz
        exact hz
      letI := addCommGrpCatSubsingletonOfIsZero _ hgr
      have hp : A.homotopyGradedProjection j degree ak = 0 :=
        Subsingleton.elim _ _
      have hn :=
        (A.homotopyGradedProjection_eq_zero_iff j degree ak).mp hp
      rw [Nat.cast_succ]
      simpa only [j, ak, add_assoc] using hn
  have fil_mono_of_le : ∀ {p q : ℤ}, p ≤ q →
      A.filtration.F q degree ≤ A.filtration.F p degree := by
    intro p q hpq
    suffices ∀ n : ℕ,
        A.filtration.F (p + (n : ℤ)) degree ≤
          A.filtration.F p degree by
      have key := this (q - p).toNat
      rwa [show p + ((q - p).toNat : ℤ) = q by omega] at key
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        A.filtration.F (p + ((n + 1 : ℕ) : ℤ)) degree =
            A.filtration.F (p + (n : ℤ) + 1) degree := by
          congr 1
          omega
        _ ≤ A.filtration.F (p + (n : ℤ)) degree :=
          A.filtration.mono _ _
        _ ≤ A.filtration.F p degree := ih
  apply A.homotopy_eq_zero_of_mem_all degree hH a
  intro s
  let k : ℕ := (s - s0).toNat
  let j : ℤ := s0 + (k : ℤ)
  have hsj : s ≤ j := by dsimp [j, k]; omega
  let xj := (A.filtrationEquiv j degree).symm ⟨a, hdeep k⟩
  let xs := (Subobject.ofLE _ _ (fil_mono_of_le hsj)).hom xj
  have hxs : (A.filtrationEquiv s degree xs).1 = a := by
    have hj : A.abutmentEquiv degree
        ((A.filtration.F j degree).arrow.hom xj) = a := by
      rw [A.filtrationEquiv_comm]
      exact congrArg Subtype.val
        ((A.filtrationEquiv j degree).apply_symm_apply ⟨a, hdeep k⟩)
    rw [← A.filtrationEquiv_comm]
    rw [show (A.filtration.F s degree).arrow.hom xs =
        (A.filtration.F j degree).arrow.hom xj by
      dsimp [xs]
      exact ConcreteCategory.congr_hom
        (Subobject.ofLE_arrow (fil_mono_of_le hsj)) xj]
    exact hj
  exact hxs ▸ (A.filtrationEquiv s degree xs).property

end SynAdamsConvergenceData

variable (S : Type u') [StableHomotopy.StableHomotopyCategory.{u', v'} S]

/-- In a finite lambda quotient of `nu X`, a homotopy class lying beyond the
width of its free-lambda E2 strip is zero, provided the canonical Adams
filtration is Hausdorff in that homotopy degree. -/
theorem nuModLambda_deep_filtration_eq_zero
    (X : S) (r : ℕ) (hr : 0 < r) (m w s0 : ℤ)
    (hdepth : (r : ℤ) ≤ m + s0 - w)
    (hH : (synAdamsConvergence Syn
      (XModLambdaN ((nu S Syn).obj X) r)).filtration.IsHausdorffAt (m, w))
    (a : Smn (Syn := Syn) m w ⟶ XModLambdaN ((nu S Syn).obj X) r)
    (ha : a ∈ synAdamsFiltration Syn
      (XModLambdaN ((nu S Syn).obj X) r) m w s0) :
    a = 0 := by
  let A := synAdamsConvergence Syn
    (XModLambdaN ((nu S Syn).obj X) r)
  apply A.homotopy_eq_zero_of_e2_vanishing_above (m, w) hH s0 a ha
  intro j hj
  exact synAdams_nu_mod_lambda_e2_isZero_of_outside
    S Syn X r hr j (m + j) w (Or.inr (by omega))

/-- A class of `nu X` whose reduction modulo `lambda^r` lies beyond the
free-lambda E2 strip is actually divisible by `lambda^r`.  Vanishing in the
cofiber comes from the preceding convergence theorem; the divisor then comes
from the exact lambda-cofiber triangle. -/
theorem nu_lambdaPow_divisible_of_quotient_deep_filtration
    (X : S) (r : ℕ) (hr : 0 < r) (m w s0 : ℤ)
    (hdepth : (r : ℤ) ≤ m + s0 - w)
    (hH : (synAdamsConvergence Syn
      (XModLambdaN ((nu S Syn).obj X) r)).filtration.IsHausdorffAt (m, w))
    (b : Smn (Syn := Syn) m w ⟶ (nu S Syn).obj X)
    (hb : b ≫ syn_functorial_cofiber.cofibι
        (lambdaPow r ((nu S Syn).obj X)) ∈
      synAdamsFiltration Syn
        (XModLambdaN ((nu S Syn).obj X) r) m w s0) :
    ∃ b' : Smn (Syn := Syn) m w ⟶
        (SyntheticCategory.biShift (0, -(r : ℤ))).obj ((nu S Syn).obj X),
      b' ≫ lambdaPow r ((nu S Syn).obj X) = b := by
  have hzero : b ≫ syn_functorial_cofiber.cofibι
      (lambdaPow r ((nu S Syn).obj X)) = 0 :=
    nuModLambda_deep_filtration_eq_zero (Syn := Syn) S X r hr m w s0
      hdepth hH _ hb
  have hker : b ∈ (LambdaPowerBoundary.inclHom
      (Smn (Syn := Syn) m w) ((nu S Syn).obj X) r).ker := hzero
  rw [← LambdaPowerBoundary.mul_range] at hker
  exact hker

/-- The suspended form of lambda-cofiber exactness used for the boundary of
a relative disk.  If the image of a suspended boundary in the cofiber of
`lambda^r` is zero, then the boundary itself is divisible by suspended
`lambda^r`. -/
theorem shift_lambdaPow_divisible_of_quotient_zero
    (Y : Syn) (r : ℕ) (m w : ℤ)
    (b : Smn (Syn := Syn) m w ⟶ (shiftFunctor Syn (1 : ℤ)).obj Y)
    (hzero : b ≫ (shiftFunctor Syn (1 : ℤ)).map
        (syn_functorial_cofiber.cofibι (lambdaPow r Y)) = 0) :
    ∃ b' : Smn (Syn := Syn) m w ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -(r : ℤ))).obj Y),
      b' ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow r Y) = b := by
  let F := shiftFunctor Syn (1 : ℤ)
  let e := FreeLambdaHomotopy.sphereSuspensionIso (Syn := Syn) m w
  obtain ⟨b0, hb0⟩ := F.map_surjective (e.hom ≫ b)
  have hzero0 : b0 ≫ syn_functorial_cofiber.cofibι (lambdaPow r Y) = 0 := by
    apply F.map_injective
    rw [F.map_comp, hb0, Category.assoc, hzero, comp_zero, F.map_zero]
  have hker : b0 ∈
      (LambdaPowerBoundary.inclHom (Smn (Syn := Syn) (m - 1) w) Y r).ker :=
    hzero0
  rw [← LambdaPowerBoundary.mul_range] at hker
  obtain ⟨b0', hb0'⟩ := hker
  change b0' ≫ lambdaPow r Y = b0 at hb0'
  refine ⟨e.inv ≫ F.map b0', ?_⟩
  change (e.inv ≫ F.map b0') ≫ F.map (lambdaPow r Y) = b
  rw [Category.assoc, ← F.map_comp, hb0', hb0, e.inv_hom_id_assoc]

/-- Complete suspended boundary closure.  Desuspend the boundary of the
relative disk, reduce it modulo `lambda^r`, and suppose that this reduction
has reached a filtration beyond the finite free-lambda strip.  Hausdorff
Adams convergence makes the reduction zero, cofiber exactness divides the
desuspended boundary by `lambda^r`, and suspension gives the required
divisor of the original disk boundary. -/
theorem shift_nu_lambdaPow_divisible_of_desuspended_quotient_deep_filtration
    (X : S) (r : ℕ) (hr : 0 < r) (m w s0 : ℤ)
    (hdepth : (r : ℤ) ≤ (m - 1) + s0 - w)
    (hH : (synAdamsConvergence Syn
      (XModLambdaN ((nu S Syn).obj X) r)).filtration.IsHausdorffAt
        (m - 1, w))
    (b : Smn (Syn := Syn) m w ⟶
      (shiftFunctor Syn (1 : ℤ)).obj ((nu S Syn).obj X))
    (b0 : Smn (Syn := Syn) (m - 1) w ⟶ (nu S Syn).obj X)
    (hdesuspend : (shiftFunctor Syn (1 : ℤ)).map b0 =
      (FreeLambdaHomotopy.sphereSuspensionIso (Syn := Syn) m w).hom ≫ b)
    (hb0 : b0 ≫ syn_functorial_cofiber.cofibι
        (lambdaPow r ((nu S Syn).obj X)) ∈
      synAdamsFiltration Syn
        (XModLambdaN ((nu S Syn).obj X) r) (m - 1) w s0) :
    ∃ b' : Smn (Syn := Syn) m w ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -(r : ℤ))).obj
            ((nu S Syn).obj X)),
      b' ≫ (shiftFunctor Syn (1 : ℤ)).map
        (lambdaPow r ((nu S Syn).obj X)) = b := by
  obtain ⟨b0', hb0'⟩ :=
    nu_lambdaPow_divisible_of_quotient_deep_filtration (Syn := Syn)
      S X r hr (m - 1) w s0 hdepth hH b0 hb0
  let F := shiftFunctor Syn (1 : ℤ)
  let e := FreeLambdaHomotopy.sphereSuspensionIso (Syn := Syn) m w
  refine ⟨e.inv ≫ F.map b0', ?_⟩
  change (e.inv ≫ F.map b0') ≫
      F.map (lambdaPow r ((nu S Syn).obj X)) = b
  rw [Category.assoc, ← F.map_comp, hb0', hdesuspend,
    e.inv_hom_id_assoc]

end KIPBase.Synthetic
