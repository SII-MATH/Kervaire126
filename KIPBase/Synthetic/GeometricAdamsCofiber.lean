import KIPBase.Synthetic.GeometricAdamsFree
import KIPBase.Synthetic.StableLambda

/-!
# Cofiber comparisons and naturality of free-layer quotients

First, an exact functor carries the relative and adjacent layers of a tower
to the corresponding layers of the mapped tower. The comparison includes
both inclusion and boundary formulas.

Second, the actual λ-cofiber homotopy calculation is natural in maps between
free objects. This part uses λ naturality and cofiber exactness directly.

The exact-functor results keep their `CommShift` and `IsTriangulated`
hypotheses explicit. For the finite λ-quotient functor these instances are
derived from stable λ coherence and the stable 3×3 cofiber property.
-/

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn]

namespace CofiberComparison

variable (F : Syn ⥤ Syn) [F.CommShift ℤ] [F.IsTriangulated]

/-- Comparison of distinguished triangles, with identity maps on the first
two objects. No cofiber comparison is taken as input. -/
noncomputable def triangleIso {A B : Syn} (f : A ⟶ B) :
    Triangle.mk (F.map f) (syn_functorial_cofiber.cofibι (F.map f))
        (syn_functorial_cofiber.cofibδ (F.map f)) ≅
      F.mapTriangle.obj (Triangle.mk f (syn_functorial_cofiber.cofibι f)
        (syn_functorial_cofiber.cofibδ f)) :=
  isoTriangleOfIso₁₂ _ _ (syn_functorial_cofiber.cofib_distinguished (F.map f))
    (F.map_distinguished _ (syn_functorial_cofiber.cofib_distinguished f))
    (Iso.refl _) (Iso.refl _) (by
      change F.map f ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
      rw [Category.comp_id, Category.id_comp])

/-- An exact functor preserves the cofiber, with its structure maps. -/
noncomputable def iso {A B : Syn} (f : A ⟶ B) :
    syn_functorial_cofiber.cofib (F.map f) ≅
      F.obj (syn_functorial_cofiber.cofib f) :=
  Triangle.π₃.mapIso (triangleIso F f)

@[reassoc] theorem incl_iso_hom {A B : Syn} (f : A ⟶ B) :
    syn_functorial_cofiber.cofibι (F.map f) ≫ (iso F f).hom =
      F.map (syn_functorial_cofiber.cofibι f) := by
  have h := (triangleIso F f).hom.comm₂
  have h₂ : (triangleIso F f).hom.hom₂ = 𝟙 (F.obj B) :=
    isoTriangleOfIso₁₂_hom_hom₂ ..
  change syn_functorial_cofiber.cofibι (F.map f) ≫ (iso F f).hom =
    (triangleIso F f).hom.hom₂ ≫ F.map (syn_functorial_cofiber.cofibι f) at h
  rw [h₂] at h
  exact h.trans (Category.id_comp _)

@[reassoc] theorem iso_hom_boundary {A B : Syn} (f : A ⟶ B) :
    (iso F f).hom ≫ F.map (syn_functorial_cofiber.cofibδ f) ≫
        (F.commShiftIso (1 : ℤ)).hom.app A =
      syn_functorial_cofiber.cofibδ (F.map f) := by
  have h := (triangleIso F f).hom.comm₃
  have h₁ : (triangleIso F f).hom.hom₁ = 𝟙 (F.obj A) :=
    isoTriangleOfIso₁₂_hom_hom₁ ..
  change syn_functorial_cofiber.cofibδ (F.map f) ≫
      (shiftFunctor Syn (1 : ℤ)).map (triangleIso F f).hom.hom₁ =
    (iso F f).hom ≫ F.map (syn_functorial_cofiber.cofibδ f) ≫
      (F.commShiftIso (1 : ℤ)).hom.app A at h
  rw [h₁] at h
  exact h.symm.trans ((congrArg (fun g => syn_functorial_cofiber.cofibδ (F.map f) ≫ g)
    ((shiftFunctor Syn (1 : ℤ)).map_id (F.obj A))).trans (Category.comp_id _))

end CofiberComparison

namespace GeometricAdams.Input

variable {X : Syn}

/-- Compare every relative interval of the mapped tower with the image of
the original relative interval under an exact functor. -/
noncomputable def mapRelativeIso (G : GeometricAdams.Input X)
    (F : Syn ⥤ Syn) [F.CommShift ℤ] [F.IsTriangulated]
    (a b : ℕ) (hab : a ≤ b) :
    (G.map F).relative a b hab ≅ F.obj (G.relative a b hab) :=
  CofiberComparison.iso F (G.transition a b hab)

@[reassoc] theorem mapRelativeIso_incl (G : GeometricAdams.Input X)
    (F : Syn ⥤ Syn) [F.CommShift ℤ] [F.IsTriangulated]
    (a b : ℕ) (hab : a ≤ b) :
    syn_functorial_cofiber.cofibι ((G.map F).transition a b hab) ≫
        (G.mapRelativeIso F a b hab).hom =
      F.map (syn_functorial_cofiber.cofibι (G.transition a b hab)) :=
  CofiberComparison.incl_iso_hom F (G.transition a b hab)

@[reassoc] theorem mapRelativeIso_boundary (G : GeometricAdams.Input X)
    (F : Syn ⥤ Syn) [F.CommShift ℤ] [F.IsTriangulated]
    (a b : ℕ) (hab : a ≤ b) :
    (G.mapRelativeIso F a b hab).hom ≫ F.map (G.boundary a b hab) ≫
        (F.commShiftIso (1 : ℤ)).hom.app (G.stage b) =
      (G.map F).boundary a b hab :=
  CofiberComparison.iso_hom_boundary F (G.transition a b hab)

/-- A class in a mapped stage lifts to the next mapped stage whenever its
image under the mapped adjacent-layer projection vanishes.  The cofiber
comparison converts that projection to the canonical cofiber inclusion of
the mapped tower, after which `exists_stageLift_of_layer_zero` applies. -/
theorem exists_mapped_stageLift_of_mapped_layer_zero
    (G : GeometricAdams.Input X) (F : Syn ⥤ Syn)
    [F.CommShift ℤ] [F.IsTriangulated]
    (S : Syn) (s : ℕ) (a : S ⟶ (G.map F).stage s)
    (ha : a ≫ F.map (syn_functorial_cofiber.cofibι
      (G.transition s (s + 1) (Nat.le_succ s))) = 0) :
    ∃ a' : S ⟶ (G.map F).stage (s + 1),
      a' ≫ (G.map F).transition s (s + 1) (Nat.le_succ s) = a := by
  have hz : a ≫ syn_functorial_cofiber.cofibι
      ((G.map F).transition s (s + 1) (Nat.le_succ s)) = 0 := by
    apply (cancel_mono (G.mapRelativeIso F s (s + 1) (Nat.le_succ s)).hom).mp
    rw [Category.assoc, G.mapRelativeIso_incl]
    simpa only [Limits.zero_comp] using ha
  exact (G.map F).exists_stageLift_of_layer_zero S s a hz

/-- In particular, associated graded commutes with an exact functor. -/
noncomputable abbrev mapLayerIso (G : GeometricAdams.Input X)
    (F : Syn ⥤ Syn) [F.CommShift ℤ] [F.IsTriangulated] (s : ℕ) :
    (G.map F).layer s ≅ F.obj (G.layer s) :=
  G.mapRelativeIso F s (s + 1) (Nat.le_succ s)

end GeometricAdams.Input

variable [SyntheticCategory Syn]

namespace XModLambdaN

/-- The actual λ-cofiber functor sends a zero object to a zero object. -/
theorem isZero_of_isZero {A : Syn} (hA : IsZero A) (n : ℕ) :
    IsZero (XModLambdaN A n) :=
  Triangle.isZero₃_of_isZero₁₂ _ (triangle_distinguished A n)
    ((SyntheticCategory.biShift (0, -(n : ℤ))).map_isZero hA) hA

/-- Preservation of zero maps follows from the zero-object computation. -/
noncomputable instance functor_preservesZeroMorphisms (n : ℕ) :
    (functor (Syn := Syn) n).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_map_zero_object
    (IsZero.iso (isZero_of_isZero (isZero_zero Syn) n) (isZero_zero Syn))

/-- Finite products commute with the actual λ-cofiber. This is proved by
a map into the product of the actual cofiber triangles and the triangle
five lemma; preservation of triangles by the quotient is not assumed. -/
theorem piComparison_isIso (n : ℕ) {J : Type} [Finite J] (A : J → Syn) :
    IsIso (piComparison (functor n) A) := by
  let F := SyntheticCategory.biShift (Syn := Syn) (0, -(n : ℤ))
  let T : J → Triangle Syn := fun j =>
    Triangle.mk (lambdaPow n (A j))
      (syn_functorial_cofiber.cofibι (lambdaPow n (A j)))
      (syn_functorial_cofiber.cofibδ (lambdaPow n (A j)))
  let U := Triangle.mk (lambdaPow n (∏ᶜ A))
    (syn_functorial_cofiber.cofibι (lambdaPow n (∏ᶜ A)))
    (syn_functorial_cofiber.cofibδ (lambdaPow n (∏ᶜ A)))
  let φ : ∀ j : J, U ⟶ T j := fun j =>
    { hom₁ := F.map (Pi.π A j)
      hom₂ := Pi.π A j
      hom₃ := XModLambdaN.map (Pi.π A j) n
      comm₁ := (lambdaPow_naturality n (Pi.π A j)).symm
      comm₂ := (incl_naturality (Pi.π A j) n).symm
      comm₃ := (proj_naturality (Pi.π A j) n).symm }
  let ψ := productTriangle.lift T φ
  have h₁ : IsIso ψ.hom₁ := by
    change IsIso (piComparison F A)
    infer_instance
  have h₂ : IsIso ψ.hom₂ := by
    change IsIso (Pi.lift (fun j => Pi.π A j))
    have h : Pi.lift (fun j => Pi.π A j) = 𝟙 (∏ᶜ A) := by
      apply Pi.hom_ext
      intro j
      simp only [Pi.lift_π, Category.id_comp]
    rw [h]
    infer_instance
  exact isIso₃_of_isIso₁₂ ψ (triangle_distinguished (∏ᶜ A) n)
    (productTriangle_distinguished T (fun j => triangle_distinguished (A j) n)) h₁ h₂

/-- The finite λ-cofiber functor is additive, derived from its actual
cofiber triangles and λ naturality. -/
noncomputable instance functor_additive (n : ℕ) : (functor (Syn := Syn) n).Additive := by
  letI : ∀ A : WalkingPair → Syn,
      PreservesLimit (Discrete.functor A) (functor (Syn := Syn) n) := by
    intro A
    letI := piComparison_isIso n A
    exact PreservesProduct.of_iso_comparison _ _
  letI : PreservesLimitsOfShape (Discrete WalkingPair) (functor (Syn := Syn) n) :=
    preservesLimitsOfShape_of_discrete _
  exact Functor.additive_of_preserves_binary_products _

/-- A necessary consequence of shift compatibility of the actual quotient
functor: invertibility of λ on an object is preserved by suspension.
This condition is stronger than ordinary naturality of `lambdaPow`. -/
theorem isIso_lambdaPow_shift_of_commShift (n : ℕ)
    [(functor (Syn := Syn) n).CommShift ℤ] (A : Syn) (k : ℤ)
    [IsIso (lambdaPow n A)] :
    IsIso (lambdaPow n ((shiftFunctor Syn k).obj A)) := by
  have hA : IsZero (XModLambdaN A n) :=
    Triangle.isZero₃_of_isIso₁ _ (triangle_distinguished A n)
      (show IsIso (lambdaPow n A) from inferInstance)
  have hshift : IsZero (XModLambdaN ((shiftFunctor Syn k).obj A) n) :=
    ((shiftFunctor Syn k).map_isZero hA).of_iso
      (((functor (Syn := Syn) n).commShiftIso k).app A)
  exact (Triangle.isZero₃_iff_isIso₁ _
    (triangle_distinguished ((shiftFunctor Syn k).obj A) n)).mp hshift

/-- A genuine obstruction to the requested global shift instance: if λ
is invertible on an object but zero on its nonzero suspension, its cofiber
functor cannot commute with suspension. No comparison axiom is used. -/
theorem not_commShift_of_lambda_shift_defect (n : ℕ) (A : Syn) (k : ℤ)
    [IsIso (lambdaPow n A)]
    (hz : lambdaPow n ((shiftFunctor Syn k).obj A) = 0)
    (hne : ¬ IsZero ((shiftFunctor Syn k).obj A)) :
    ¬ Nonempty ((functor (Syn := Syn) n).CommShift ℤ) := by
  rintro ⟨h⟩
  letI := h
  have hi := isIso_lambdaPow_shift_of_commShift n A k
  rw [hz] at hi
  exact hne ((isIsoZero_iff_source_target_isZero _ _).mp hi).2

end XModLambdaN

namespace LambdaPowerBoundary

/-- The homotopy cokernel map induced by an actual map of synthetic
spectra. Well-definedness is proved from λ-power naturality. -/
noncomputable def cokernelMap (T : Syn) {A B : Syn} (f : A ⟶ B) (n : ℕ) :
    ((T ⟶ A) ⧸ (mulHom T A n).range) →+
      ((T ⟶ B) ⧸ (mulHom T B n).range) :=
  QuotientAddGroup.map _ _ (GeometricAdams.Input.postcompose T f) (by
    rintro a ⟨b, rfl⟩
    refine ⟨b ≫ (SyntheticCategory.biShift (0, -(n : ℤ))).map f, ?_⟩
    change (b ≫ _) ≫ lambdaPow n B = (b ≫ lambdaPow n A) ≫ f
    rw [Category.assoc, lambdaPow_naturality, ← Category.assoc])

@[simp] theorem cokernelMap_mk (T : Syn) {A B : Syn} (f : A ⟶ B)
    (n : ℕ) (a : T ⟶ A) :
    cokernelMap T f n (QuotientAddGroup.mk a) = QuotientAddGroup.mk (a ≫ f) := rfl

@[simp] theorem cokernelMap_id (T A : Syn) (n : ℕ)
    (q : (T ⟶ A) ⧸ (mulHom T A n).range) :
    cokernelMap T (𝟙 A) n q = q := by
  induction q using QuotientAddGroup.induction_on with
  | H a => simp only [cokernelMap_mk, Category.comp_id]

theorem cokernelMap_comp (T : Syn) {A B C : Syn} (f : A ⟶ B) (g : B ⟶ C)
    (n : ℕ) (q : (T ⟶ A) ⧸ (mulHom T A n).range) :
    cokernelMap T (f ≫ g) n q = cokernelMap T g n (cokernelMap T f n q) := by
  induction q using QuotientAddGroup.induction_on with
  | H a => simp only [cokernelMap_mk, Category.assoc]

/-- The injection from the homotopy cokernel to actual cofiber homotopy is
natural, without any freeness hypothesis. -/
theorem cokernelIncl_naturality (T : Syn) {A B : Syn} (f : A ⟶ B) (n : ℕ)
    (q : (T ⟶ A) ⧸ (mulHom T A n).range) :
    cokernelIncl T B n (cokernelMap T f n q) =
      cokernelIncl T A n q ≫ XModLambdaN.map f n := by
  induction q using QuotientAddGroup.induction_on with
  | H a =>
    change (a ≫ f) ≫ syn_functorial_cofiber.cofibι (lambdaPow n B) =
      (a ≫ syn_functorial_cofiber.cofibι (lambdaPow n A)) ≫ XModLambdaN.map f n
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun g => a ≫ g) (XModLambdaN.incl_naturality f n)).trans
        (Category.assoc _ _ _).symm)

/-- Multiples of λ to a positive power are multiples of λ itself. This
uses the actual factorization of the power, before taking any quotient. -/
theorem mul_range_le_one (T A : Syn) (n : ℕ) :
    (mulHom T A (n + 1)).range ≤ (mulHom T A 1).range := by
  rintro a ⟨b, rfl⟩
  refine ⟨b ≫ lambdaPowerToOne A n, ?_⟩
  change (b ≫ lambdaPowerToOne A n) ≫ lambdaPow 1 A = b ≫ lambdaPow (n + 1) A
  rw [Category.assoc, lambdaPowerToOne_comp]

/-- Reduction from the finite-power homotopy cokernel to the λ cokernel. -/
noncomputable def cokernelToOne (T A : Syn) (n : ℕ) :
    ((T ⟶ A) ⧸ (mulHom T A (n + 1)).range) →+
      ((T ⟶ A) ⧸ (mulHom T A 1).range) :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id _) (mul_range_le_one T A n)

@[simp] theorem cokernelToOne_mk (T A : Syn) (n : ℕ) (a : T ⟶ A) :
    cokernelToOne T A n (QuotientAddGroup.mk a) = QuotientAddGroup.mk a := rfl

/-- Cokernel reduction is precisely actual cofiber restriction on the
injected homotopy cokernels. -/
theorem cokernelIncl_toOne (T A : Syn) (n : ℕ)
    (q : (T ⟶ A) ⧸ (mulHom T A (n + 1)).range) :
    cokernelIncl T A 1 (cokernelToOne T A n q) =
      cokernelIncl T A (n + 1) q ≫ XModLambdaN.toOne A n := by
  induction q using QuotientAddGroup.induction_on with
  | H a =>
    change a ≫ syn_functorial_cofiber.cofibι (lambdaPow 1 A) =
      (a ≫ syn_functorial_cofiber.cofibι (lambdaPow (n + 1) A)) ≫ XModLambdaN.toOne A n
    exact ((Category.assoc _ _ _).trans
      (congrArg (fun f => a ≫ f) (XModLambdaN.incl_toOne A n))).symm

end LambdaPowerBoundary

namespace FreeLambdaHomotopy

variable {A B : Syn} {weightA weightB : ℤ → ℤ}

/-- For free objects, the previously constructed homotopy-cokernel
identification is natural for every actual object map. -/
theorem cokernelHomEquiv_naturality (RA : FreeLambdaHomotopy A weightA)
    (RB : FreeLambdaHomotopy B weightB) (f : A ⟶ B) (m w : ℤ) (n : ℕ)
    (q : (Smn m w ⟶ A) ⧸ (LambdaPowerBoundary.mulHom (Smn m w) A n).range) :
    RB.cokernelHomEquiv m w n (LambdaPowerBoundary.cokernelMap (Smn m w) f n q) =
      RA.cokernelHomEquiv m w n q ≫ XModLambdaN.map f n :=
  LambdaPowerBoundary.cokernelIncl_naturality (Smn m w) f n q

/-- Reduction on the cokernel model agrees with restriction of every
actual finite-cofiber homotopy class of a free object. -/
theorem cokernelHomEquiv_toOne (RA : FreeLambdaHomotopy A weightA)
    (m w : ℤ) (n : ℕ)
    (a : Smn m w ⟶ XModLambdaN A (n + 1)) :
    RA.cokernelHomEquiv m w 1
        (LambdaPowerBoundary.cokernelToOne (Smn m w) A n
          ((RA.cokernelHomEquiv m w (n + 1)).symm a)) =
      a ≫ XModLambdaN.toOne A n := by
  have h := LambdaPowerBoundary.cokernelIncl_toOne (Smn m w) A n
    ((RA.cokernelHomEquiv m w (n + 1)).symm a)
  change RA.cokernelHomEquiv m w 1 _ =
    RA.cokernelHomEquiv m w (n + 1)
      ((RA.cokernelHomEquiv m w (n + 1)).symm a) ≫ _ at h
  rw [AddEquiv.apply_symm_apply] at h
  exact h

/-- Actual restriction to the first λ-cofiber is surjective on homotopy
of a free object, proved by lifting along the first quotient inclusion. -/
theorem toOne_surjective (RA : FreeLambdaHomotopy A weightA)
    (m w : ℤ) (n : ℕ) :
    Function.Surjective
      (fun a : Smn m w ⟶ XModLambdaN A (n + 1) => a ≫ XModLambdaN.toOne A n) := by
  intro a
  obtain ⟨b, hb⟩ := RA.inclHom_surjective m w 1 a
  refine ⟨LambdaPowerBoundary.inclHom (Smn m w) A (n + 1) b, ?_⟩
  change (b ≫ syn_functorial_cofiber.cofibι (lambdaPow (n + 1) A)) ≫
    XModLambdaN.toOne A n = a
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun f => b ≫ f) (XModLambdaN.incl_toOne A n))).trans hb

/-- Above the generator weight the λ-power source vanishes, so the actual
quotient inclusion is also injective. -/
theorem inclHom_injective (RA : FreeLambdaHomotopy A weightA)
    (m w : ℤ) (n : ℕ) (h : weightA m < w + n) :
    Function.Injective (LambdaPowerBoundary.inclHom (Smn m w) A n) := by
  have hz : IsZero (FreeLambdaE2.component (RA.generator m) (weightA m) (w + n)) := by
    rw [FreeLambdaE2.component, if_neg (by omega)]
    exact IsInitial.isZero initialIsInitial
  letI := addCommGrpCatSubsingletonOfIsZero _ hz
  apply (LambdaPowerBoundary.inclHom (Smn m w) A n).ker_eq_bot_iff.mp
  rw [← LambdaPowerBoundary.mul_range]
  apply le_antisymm _ bot_le
  rintro a ⟨b, rfl⟩
  have hb : b = 0 := (RA.shiftedComponentEquiv m w n).injective (Subsingleton.elim _ _)
  change LambdaPowerBoundary.mulHom (Smn m w) A n b = 0
  rw [hb, map_zero]

/-- In the surviving upper strip, the actual quotient inclusion itself
is an isomorphism on homotopy. -/
noncomputable def inclHomEquiv (RA : FreeLambdaHomotopy A weightA)
    (m w : ℤ) (n : ℕ) (h : weightA m < w + n) :
    (Smn m w ⟶ A) ≃+ (Smn m w ⟶ XModLambdaN A n) :=
  AddEquiv.ofBijective (LambdaPowerBoundary.inclHom (Smn m w) A n)
    ⟨RA.inclHom_injective m w n h, RA.inclHom_surjective m w n⟩

/-- On the generator diagonal, restriction from any positive finite λ
quotient to the first quotient is an actual homotopy isomorphism. -/
noncomputable def toOneDiagonalHomEquiv (RA : FreeLambdaHomotopy A weightA)
    (m : ℤ) (n : ℕ) :
    (Smn m (weightA m) ⟶ XModLambdaN A (n + 1)) ≃+
      (Smn m (weightA m) ⟶ XModLambdaN A 1) :=
  (RA.inclHomEquiv m (weightA m) (n + 1) (by omega)).symm.trans
    (RA.inclHomEquiv m (weightA m) 1 (by omega))

/-- The diagonal isomorphism is induced by the specified `toOne` map,
not merely an abstract identification of its source and target groups. -/
theorem toOneDiagonalHomEquiv_apply (RA : FreeLambdaHomotopy A weightA)
    (m : ℤ) (n : ℕ) (a : Smn m (weightA m) ⟶ XModLambdaN A (n + 1)) :
    RA.toOneDiagonalHomEquiv m n a = a ≫ XModLambdaN.toOne A n := by
  obtain ⟨b, rfl⟩ := RA.inclHom_surjective m (weightA m) (n + 1) a
  have h : (RA.inclHomEquiv m (weightA m) (n + 1) (by omega)).symm
      (LambdaPowerBoundary.inclHom (Smn m (weightA m)) A (n + 1) b) = b :=
    (RA.inclHomEquiv m (weightA m) (n + 1) (by omega)).symm_apply_apply b
  change RA.inclHomEquiv m (weightA m) 1 (by omega)
    ((RA.inclHomEquiv m (weightA m) (n + 1) (by omega)).symm _) = _
  rw [h]
  change b ≫ syn_functorial_cofiber.cofibι (lambdaPow 1 A) =
    (b ≫ syn_functorial_cofiber.cofibι (lambdaPow (n + 1) A)) ≫ XModLambdaN.toOne A n
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun f => b ≫ f) (XModLambdaN.incl_toOne A n))).symm

/-- Thus an actual map on finite-cofiber homotopy is determined by its
values on classes lifted from the original object. -/
theorem cofiberHom_ext (RA : FreeLambdaHomotopy A weightA)
    (m w : ℤ) (n : ℕ) {Z : Type*} (f g : (Smn m w ⟶ XModLambdaN A n) → Z)
    (h : ∀ a : Smn m w ⟶ A,
      f (LambdaPowerBoundary.inclHom (Smn m w) A n a) =
        g (LambdaPowerBoundary.inclHom (Smn m w) A n a)) : f = g := by
  funext a
  obtain ⟨b, rfl⟩ := RA.inclHom_surjective m w n a
  exact h b

end FreeLambdaHomotopy

namespace GeometricAdams.Input

variable {X : Syn}
variable [SyntheticShiftCofiberCompatibility (Syn := Syn)]
    [SyntheticStableLambdaCompatibility (Syn := Syn)]

/-- Applying the exact-functor comparison to the finite λ-quotient. Its
exactness and shift compatibility are derived from stable λ and 3×3
cofiber coherence. -/
noncomputable abbrev quotientLayerIso (G : GeometricAdams.Input X) (n : ℕ)
    (s : ℕ) :
    (G.quotient n).layer s ≅ XModLambdaN (G.layer s) n :=
  G.mapLayerIso (XModLambdaN.functor n) s

/-- The associated graded homotopy of the quotient filtration is the
truncated free model. -/
noncomputable def quotientLayerHomEquiv (G : GeometricAdams.Input X)
    (R : G.FreeLayers) (n : ℕ)
    (s : ℕ) (m w : ℤ) :
    (Smn m w ⟶ (G.quotient n).layer s) ≃+
      TruncatedLambdaE2.component ((R s).generator m) (m + (s : ℤ)) w n :=
  (AddEquiv.ofBijective (GeometricAdams.Input.postcompose (Smn m w)
    (G.quotientLayerIso n s).hom) ⟨by
      intro a b h
      exact (cancel_mono (G.quotientLayerIso n s).hom).mp h, by
      intro a
      refine ⟨a ≫ (G.quotientLayerIso n s).inv, ?_⟩
      change (a ≫ (G.quotientLayerIso n s).inv) ≫ (G.quotientLayerIso n s).hom = a
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩).trans
        (G.layerCofiberHomEquiv R s m w n)

end GeometricAdams.Input

end KIPBase.Synthetic
