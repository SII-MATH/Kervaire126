import KIPBase.Synthetic.GeometricAdams
import KIPBase.Synthetic.LambdaE2
import Mathlib.Algebra.Category.Grp.Colimits

/-!
# Free λ homotopy on the associated graded of a filtration

The structural input is a free graded λ-module model compatible with the
actual multiplication maps. Injectivity and the homotopy of finite cofibers
are conclusions. No page comparison or geometric realization is assumed.
-/

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits

universe u v

namespace FreeLambdaE2

/-- A power of λ is injective in every weight of a free λ-module, including
weights where its source is zero. -/
theorem lambdaPow_injective_all (A : AddCommGrpCat.{v}) (t w : ℤ) (n : ℕ) :
    Function.Injective (lambdaPow A t w n).hom := by
  by_cases h : w + (n : ℤ) ≤ t
  · exact lambdaPow_injective A t w n h
  · have hz : IsZero (component A t (w + n)) := by
      rw [component, if_neg h]
      exact IsInitial.isZero initialIsInitial
    letI := addCommGrpCatSubsingletonOfIsZero _ hz
    intro x y _
    exact Subsingleton.elim x y

end FreeLambdaE2

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]

/-- A degreewise free λ-module description of actual homotopy groups.
The two equivalences express the module coordinates before and after the
weight shift. Compatibility is with the actual `lambdaPow` on the object;
it is not an independent action on a spectral-sequence page. -/
structure FreeLambdaHomotopy (Y : Syn) (generatorWeight : ℤ → ℤ) where
  generator : ℤ → AddCommGrpCat.{v}
  componentEquiv : ∀ m w : ℤ,
    (Smn (Syn := Syn) m w ⟶ Y) ≃+
      FreeLambdaE2.component (generator m) (generatorWeight m) w
  shiftedComponentEquiv : ∀ (m w : ℤ) (n : ℕ),
    (Smn (Syn := Syn) m w ⟶
      (SyntheticCategory.biShift (0, -(n : ℤ))).obj Y) ≃+
        FreeLambdaE2.component (generator m) (generatorWeight m) (w + n)
  lambda_compatible : ∀ (m w : ℤ) (n : ℕ)
    (a : Smn (Syn := Syn) m w ⟶
      (SyntheticCategory.biShift (0, -(n : ℤ))).obj Y),
    componentEquiv m w (LambdaPowerBoundary.mulHom (Smn m w) Y n a) =
      (FreeLambdaE2.lambdaPow (generator m) (generatorWeight m) w n).hom
        (shiftedComponentEquiv m w n a)

namespace FreeLambdaHomotopy

variable {Y : Syn} {generatorWeight : ℤ → ℤ}

/-- Actual λ-power injectivity is derived from the free module model. -/
theorem mulHom_injective (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ) :
    Function.Injective (LambdaPowerBoundary.mulHom (Smn m w) Y n) := by
  intro a b hab
  apply (R.shiftedComponentEquiv m w n).injective
  apply FreeLambdaE2.lambdaPow_injective_all (R.generator m) (generatorWeight m) w n
  rw [← R.lambda_compatible, ← R.lambda_compatible, hab]

/-- The sphere representing the preceding homotopy degree suspends to the
given sphere. This uses the existing synthetic shift identifications. -/
noncomputable def sphereSuspensionIso (m w : ℤ) :
    (shiftFunctor Syn (1 : ℤ)).obj (Smn (Syn := Syn) (m - 1) w) ≅ Smn m w :=
  ((SyntheticCategory.biShift_compat (Syn := Syn) 1).app _).symm ≪≫
    (SyntheticCategory.biShift_comp (m - 1, w) (1, 0)).app S_0_0 ≪≫
      eqToIso (by simp [Smn])

/-- Injectivity on the suspended term of the cofiber exact sequence follows
from the same freeness in the preceding homotopy degree. -/
theorem shiftMulHom_injective (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ) :
    Function.Injective (LambdaPowerBoundary.shiftMulHom (Smn m w) Y n) := by
  intro a b hab
  let F := shiftFunctor Syn (1 : ℤ)
  let e := sphereSuspensionIso (Syn := Syn) m w
  obtain ⟨a', ha⟩ := F.map_surjective (e.hom ≫ a)
  obtain ⟨b', hb⟩ := F.map_surjective (e.hom ≫ b)
  have heq : a' ≫ lambdaPow n Y = b' ≫ lambdaPow n Y := by
    apply F.map_injective
    rw [F.map_comp, F.map_comp, ha, hb, Category.assoc, Category.assoc]
    exact congrArg (fun f => e.hom ≫ f) hab
  have h := R.mulHom_injective (m - 1) w n heq
  apply (cancel_epi e.hom).mp
  rw [← ha, ← hb, h]

/-- In the free range, actual lambda multiplication is surjective as well
as injective. This follows directly from the free coordinates. -/
theorem mulHom_surjective (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ) (h : w + (n : ℤ) ≤ generatorWeight m) :
    Function.Surjective (LambdaPowerBoundary.mulHom (Smn m w) Y n) := by
  let e := addEquivOfAddCommGrpCatIso
    (FreeLambdaE2.lambdaPowIso (R.generator m) (generatorWeight m) w n h)
  intro b
  refine ⟨(R.shiftedComponentEquiv m w n).symm
    (e.symm (R.componentEquiv m w b)), ?_⟩
  apply (R.componentEquiv m w).injective
  rw [R.lambda_compatible, AddEquiv.apply_symm_apply]
  exact e.apply_symm_apply _

/-- Suspended lambda multiplication is onto in the corresponding free
range. -/
theorem shiftMulHom_surjective (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ) (h : w + (n : ℤ) ≤ generatorWeight (m - 1)) :
    Function.Surjective (LambdaPowerBoundary.shiftMulHom (Smn m w) Y n) := by
  let F := shiftFunctor Syn (1 : ℤ)
  let e := sphereSuspensionIso (Syn := Syn) m w
  intro b
  obtain ⟨b', hb⟩ := F.map_surjective (e.hom ≫ b)
  obtain ⟨a', ha⟩ := R.mulHom_surjective (m - 1) w n h b'
  refine ⟨e.inv ≫ F.map a', ?_⟩
  change (e.inv ≫ F.map a') ≫ F.map (lambdaPow n Y) = b
  rw [Category.assoc, ← F.map_comp]
  change e.inv ≫ F.map (LambdaPowerBoundary.mulHom _ Y n a') = b
  rw [ha, hb, e.inv_hom_id_assoc]

/-- Every possible leading term of a boundary correction strictly deeper
than filtration `s+r` is divisible by `lambda^r`.

The boundary term lies in the suspended homotopy of `layer j` and is
represented by `S^{m,m+s}`.  The free-lambda description of that layer has
generator weight `(m-1)+j` after suspension.  Thus `s+r<j` is exactly the
free-range inequality which makes multiplication by `lambda^r` onto. -/
theorem deeperBoundaryLeadingTerm_lambdaPow_surjective
    {X : Syn} (G : GeometricAdams.Input X)
    (R : ∀ j : ℕ,
      FreeLambdaHomotopy (G.layer j) (fun m => m + (j : ℤ)))
    (s r j : ℕ) (hj : s + r < j) (m : ℤ) :
    Function.Surjective
      (LambdaPowerBoundary.shiftMulHom
        (Smn (Syn := Syn) m (m + (s : ℤ))) (G.layer j) r) := by
  let F := shiftFunctor Syn (1 : ℤ)
  let e := sphereSuspensionIso (Syn := Syn) m (m + (s : ℤ))
  intro b
  obtain ⟨b', hb⟩ := F.map_surjective (e.hom ≫ b)
  have hfree : m + (s : ℤ) + (r : ℤ) ≤ (m - 1) + (j : ℤ) := by omega
  let modelIso := addEquivOfAddCommGrpCatIso
    (FreeLambdaE2.lambdaPowIso
      ((R j).generator (m - 1)) ((m - 1) + (j : ℤ))
      (m + (s : ℤ)) r hfree)
  let a' := ((R j).shiftedComponentEquiv (m - 1) (m + (s : ℤ)) r).symm
    (modelIso.symm ((R j).componentEquiv (m - 1) (m + (s : ℤ)) b'))
  have ha' : a' ≫ lambdaPow r (G.layer j) = b' := by
    apply ((R j).componentEquiv (m - 1) (m + (s : ℤ))).injective
    change ((R j).componentEquiv (m - 1) (m + (s : ℤ)))
        (LambdaPowerBoundary.mulHom
          (Smn (Syn := Syn) (m - 1) (m + (s : ℤ))) (G.layer j) r a') = _
    rw [(R j).lambda_compatible]
    simp only [a', AddEquiv.apply_symm_apply]
    exact modelIso.apply_symm_apply _
  refine ⟨e.inv ≫ F.map a', ?_⟩
  change (e.inv ≫ F.map a') ≫ F.map (lambdaPow r (G.layer j)) = b
  rw [Category.assoc, ← F.map_comp, ha', hb, e.inv_hom_id_assoc]

/-- Element form of `deeperBoundaryLeadingTerm_lambdaPow_surjective`.
It supplies the actual divided leading term used at one correction step. -/
theorem exists_lambdaPow_divisor_of_deeperBoundaryLeadingTerm
    {X : Syn} (G : GeometricAdams.Input X)
    (R : ∀ j : ℕ,
      FreeLambdaHomotopy (G.layer j) (fun m => m + (j : ℤ)))
    (s r j : ℕ) (hj : s + r < j) (m : ℤ)
    (b : Smn (Syn := Syn) m (m + (s : ℤ)) ⟶
      (shiftFunctor Syn (1 : ℤ)).obj (G.layer j)) :
    ∃ b' : Smn (Syn := Syn) m (m + (s : ℤ)) ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -(r : ℤ))).obj (G.layer j)),
      b' ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow r (G.layer j)) = b := by
  exact deeperBoundaryLeadingTerm_lambdaPow_surjective G R s r j hj m b

/-- The connecting homomorphism of a free layer's finite λ-cofiber is zero.
The proof uses actual cofiber exactness and derived λ-injectivity. -/
theorem boundaryHom_eq_zero (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ) (a : Smn m w ⟶ XModLambdaN Y n) :
    LambdaPowerBoundary.boundaryHom (Smn m w) Y n a = 0 := by
  apply R.shiftMulHom_injective m w n
  exact (LambdaPowerBoundary.boundaryToKernel (Smn m w) Y n a).property.trans
    (map_zero _).symm

/-- Every homotopy class of the layer cofiber lifts along the actual
quotient inclusion. This is a conclusion of freeness, not a new hypothesis. -/
theorem inclHom_surjective (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ) :
    Function.Surjective (LambdaPowerBoundary.inclHom (Smn m w) Y n) := by
  intro a
  have ha : a ∈ (LambdaPowerBoundary.inclHom (Smn m w) Y n).range := by
    rw [LambdaPowerBoundary.incl_range]
    exact R.boundaryHom_eq_zero m w n a
  exact ha

/-- The actual inclusion identifies homotopy of a free layer's cofiber with
the quotient of its homotopy by λ-power multiples. -/
noncomputable def cokernelHomEquiv (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ) :
    ((Smn m w ⟶ Y) ⧸ (LambdaPowerBoundary.mulHom (Smn m w) Y n).range) ≃+
      (Smn m w ⟶ XModLambdaN Y n) :=
  AddEquiv.ofBijective (LambdaPowerBoundary.cokernelIncl (Smn m w) Y n)
    ⟨LambdaPowerBoundary.cokernelIncl_injective (Smn m w) Y n, by
      intro a
      obtain ⟨b, rfl⟩ := R.inclHom_surjective m w n a
      exact ⟨QuotientAddGroup.mk b, rfl⟩⟩

@[simp] theorem cokernelHomEquiv_mk (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ) (a : Smn m w ⟶ Y) :
    R.cokernelHomEquiv m w n (QuotientAddGroup.mk a) =
      LambdaPowerBoundary.inclHom (Smn m w) Y n a := rfl

/-- The free coordinates carry the range of actual λ multiplication to
the range of model λ multiplication. -/
theorem mul_range_map (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ) :
    (LambdaPowerBoundary.mulHom (Smn m w) Y n).range.map
        (R.componentEquiv m w).toAddMonoidHom =
      (FreeLambdaE2.lambdaPow (R.generator m) (generatorWeight m) w n).hom.range := by
  ext y
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨R.shiftedComponentEquiv m w n a, (R.lambda_compatible m w n a).symm⟩
  · rintro ⟨a, rfl⟩
    let b := (R.shiftedComponentEquiv m w n).symm a
    refine ⟨LambdaPowerBoundary.mulHom (Smn m w) Y n b, ⟨b, rfl⟩, ?_⟩
    change R.componentEquiv m w (LambdaPowerBoundary.mulHom (Smn m w) Y n b) = _
    rw [R.lambda_compatible]
    simp [b]

/-- The actual finite λ-cofiber of a free layer has the truncated free
homotopy module. The map is induced by the actual cofiber inclusion. -/
noncomputable def cofiberHomEquiv (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ) :
    (Smn m w ⟶ XModLambdaN Y n) ≃+
      TruncatedLambdaE2.component (R.generator m) (generatorWeight m) w n :=
  (R.cokernelHomEquiv m w n).symm |>.trans
    ((QuotientAddGroup.congr _ _ (R.componentEquiv m w)
      (R.mul_range_map m w n)).trans
        (addEquivOfAddCommGrpCatIso
          ((AddCommGrpCat.cokernelIsoQuotient
            (FreeLambdaE2.lambdaPow (R.generator m) (generatorWeight m) w n)).symm ≪≫
              freeLambdaE2QuotientIso (R.generator m) (generatorWeight m) w n)))

/-- The homotopy calculation commutes with the actual quotient inclusion
and the model's cokernel projection. -/
theorem cofiberHomEquiv_incl (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ) (a : Smn m w ⟶ Y) :
    R.cofiberHomEquiv m w n (LambdaPowerBoundary.inclHom (Smn m w) Y n a) =
      (freeLambdaE2QuotientIso (R.generator m) (generatorWeight m) w n).hom.hom
        ((cokernel.π (FreeLambdaE2.lambdaPow
          (R.generator m) (generatorWeight m) w n)).hom (R.componentEquiv m w a)) := by
  have h : (R.cokernelHomEquiv m w n).symm
      (LambdaPowerBoundary.inclHom (Smn m w) Y n a) = QuotientAddGroup.mk a :=
    (R.cokernelHomEquiv m w n).symm_apply_apply (QuotientAddGroup.mk a)
  simp only [cofiberHomEquiv, AddEquiv.trans_apply, h]
  rfl

/-- Inside the truncated strip, the finite cofiber has one copy of the
generator group. -/
noncomputable def cofiberHomInStripEquiv (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ)
    (h : 0 ≤ generatorWeight m - w ∧ generatorWeight m - w < n) :
    (Smn m w ⟶ XModLambdaN Y n) ≃+ R.generator m :=
  (R.cofiberHomEquiv m w n).trans (addEquivOfAddCommGrpCatIso
    (eqToIso (TruncatedLambdaE2.component_eq_generator_iff _ _ _ _ h)))

/-- In a weight outside the truncated strip, the actual homotopy group of
the layer cofiber vanishes. -/
theorem cofiberHom_subsingleton (R : FreeLambdaHomotopy Y generatorWeight)
    (m w : ℤ) (n : ℕ)
    (h : generatorWeight m - w < 0 ∨ (n : ℤ) ≤ generatorWeight m - w) :
    Subsingleton (Smn m w ⟶ XModLambdaN Y n) := by
  have hz : IsZero
      (TruncatedLambdaE2.component (R.generator m) (generatorWeight m) w n) := by
    rw [TruncatedLambdaE2.component_eq_zero_of_outside _ _ _ _ h]
    exact IsInitial.isZero initialIsInitial
  letI := addCommGrpCatSubsingletonOfIsZero _ hz
  exact (R.cofiberHomEquiv m w n).injective.subsingleton

end FreeLambdaHomotopy

namespace GeometricAdams.Input

variable {X : Syn}

/-- The structural hypothesis for the abstract Adams comparison: the
associated graded homotopy is free in λ, with generator weight `m + s`.
There are no page comparisons, boundary formulas, or realization fields. -/
abbrev FreeLayers (G : GeometricAdams.Input X) :=
  ∀ s : ℕ, FreeLambdaHomotopy (G.layer s) (fun m => m + (s : ℤ))

/-- Compute the actual homotopy of every associated graded layer's finite
λ-cofiber directly from the free graded structure. -/
noncomputable def layerCofiberHomEquiv (G : GeometricAdams.Input X)
    (R : G.FreeLayers) (s : ℕ) (m w : ℤ) (n : ℕ) :
    (Smn m w ⟶ XModLambdaN (G.layer s) n) ≃+
      TruncatedLambdaE2.component ((R s).generator m) (m + (s : ℤ)) w n :=
  (R s).cofiberHomEquiv m w n

/-- The finite cofiber of an associated graded layer vanishes outside
`0 ≤ m+s-w < n`. -/
theorem layerCofiberHom_subsingleton (G : GeometricAdams.Input X)
    (R : G.FreeLayers) (s : ℕ) (m w : ℤ) (n : ℕ)
    (h : m + (s : ℤ) - w < 0 ∨ (n : ℤ) ≤ m + (s : ℤ) - w) :
    Subsingleton (Smn m w ⟶ XModLambdaN (G.layer s) n) :=
  (R s).cofiberHom_subsingleton m w n h

/-- For a single λ-cofiber, only the generator diagonal survives. -/
theorem layerModLambdaHom_subsingleton (G : GeometricAdams.Input X)
    (R : G.FreeLayers) (s : ℕ) (m w : ℤ) (h : w ≠ m + (s : ℤ)) :
    Subsingleton (Smn m w ⟶ XModLambdaN (G.layer s) 1) :=
  G.layerCofiberHom_subsingleton R s m w 1 (by omega)

end GeometricAdams.Input

end KIPBase.Synthetic
