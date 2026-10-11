import KIPBase.Synthetic.Sphere
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The λ-boundary and its maps on homotopy groups

The boundary of multiplication by λ, its naturality, and the exactness
statements needed for the boundary extension spectral sequence.
-/

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

/-! ### Towers and their factorization filtrations -/

/-- A tower in the homotopy category. Being the tower underlying the
synthetic Adams construction is additional mathematical content. -/
abbrev SyntheticCofiberTower (Syn : Type u) [Category.{v} Syn] := ℕᵒᵖ ⥤ Syn

namespace SyntheticCofiberTower

variable {Syn : Type u} [Category.{v} Syn]

abbrev stage (T : SyntheticCofiberTower Syn) (s : ℕ) : Syn := T.obj (Opposite.op s)

abbrev transition (T : SyntheticCofiberTower Syn) (a b : ℕ) (h : a ≤ b) :
    T.stage b ⟶ T.stage a := T.map (homOfLE h).op

@[simp] theorem transition_self (T : SyntheticCofiberTower Syn) (s : ℕ) :
    T.transition s s le_rfl = 𝟙 (T.stage s) := T.map_id _

@[reassoc] theorem transition_comp (T : SyntheticCofiberTower Syn)
    (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    T.transition b c hbc ≫ T.transition a b hab =
      T.transition a c (hab.trans hbc) := (T.map_comp _ _).symm

variable [Preadditive Syn]

/-- Filtration by actual factorizations through stages of the tower. -/
def homFiltration (T : SyntheticCofiberTower Syn) (S : Syn) (s : ℕ) :
    AddSubgroup (S ⟶ T.stage 0) :=
  AddMonoidHom.range
    { toFun := fun f : S ⟶ T.stage s => f ≫ T.transition 0 s (Nat.zero_le s)
      map_zero' := zero_comp
      map_add' := fun _ _ => by simp only [Preadditive.add_comp] }

theorem mem_homFiltration (T : SyntheticCofiberTower Syn) (S : Syn) (s : ℕ)
    (f : S ⟶ T.stage 0) : f ∈ T.homFiltration S s ↔
      ∃ g : S ⟶ T.stage s, g ≫ T.transition 0 s (Nat.zero_le s) = f := Iff.rfl

/-- The actual factorization filtration is decreasing. -/
theorem homFiltration_antitone (T : SyntheticCofiberTower Syn) (S : Syn) :
    Antitone (T.homFiltration S) := by
  intro a b hab f hf
  obtain ⟨g, rfl⟩ := (T.mem_homFiltration S b f).mp hf
  apply (T.mem_homFiltration S a _).mpr
  refine ⟨g ≫ T.transition a b hab, ?_⟩
  rw [Category.assoc, transition_comp]

end SyntheticCofiberTower

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]


/-! ### Restrictions of finite λ-quotients

These maps are constructed from the existing power recursion and the
functorial cofiber, without an additional quotient-tower witness. -/

/-- The factor of `λ^(n+2)` preceding `λ^(n+1)`, with exactly the
associativity isomorphism used in the definition of the power. -/
noncomputable def lambdaPowerStepNatTrans (n : ℕ) :
    SyntheticCategory.biShift (Syn := Syn) (0, -((n + 2 : ℕ) : ℤ)) ⟶
      SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ)) :=
  eqToHom (congrArg SyntheticCategory.biShift (show
      ((0 : ℤ), -((n + 2 : ℕ) : ℤ)) =
        ((0 : ℤ), -1) + (0, -((n + 1 : ℕ) : ℤ)) from by
          ext <;> dsimp; omega)) ≫
    (SyntheticCategory.biShift_comp
      (0, -1) (0, -((n + 1 : ℕ) : ℤ))).inv ≫
    Functor.whiskerRight SyntheticCategory.lam
      (SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ)))

theorem lambdaPowerStepNatTrans_comp (n : ℕ) :
    lambdaPowerStepNatTrans (Syn := Syn) n ≫ lambdaPowNatTrans (n + 1) =
      lambdaPowNatTrans (n + 2) := by
  have transport (a b : ℤ × ℤ) (h : a = b) (F : Syn ⥤ Syn)
      (f : SyntheticCategory.biShift a ⟶ F) :
      eqToHom (congrArg SyntheticCategory.biShift h.symm) ≫ f = h ▸ f := by
    cases h
    simp
  dsimp only [lambdaPowerStepNatTrans]
  conv_rhs => unfold lambdaPowNatTrans
  rw [← transport]
  simp only [Category.assoc]

/-- The natural factor `Σ^{0,-(n+1)}X ⟶ Σ^{0,-1}X` in `λ^(n+1)`.
Its construction follows the existing power recursion, so no additional
coherence law for the chosen bigraded suspension is assumed. -/
noncomputable def lambdaPowerToOneNatTrans : (n : ℕ) →
    SyntheticCategory.biShift (Syn := Syn) (0, -((n + 1 : ℕ) : ℤ)) ⟶
      SyntheticCategory.biShift (0, -1)
  | 0 => 𝟙 _
  | n + 1 => lambdaPowerStepNatTrans n ≫ lambdaPowerToOneNatTrans n

/-- This is a factorization of the actual multiplication map. -/
theorem lambdaPowerToOneNatTrans_comp (n : ℕ) :
    lambdaPowerToOneNatTrans (Syn := Syn) n ≫ SyntheticCategory.lam =
      lambdaPowNatTrans (n + 1) := by
  induction n with
  | zero => simp [lambdaPowerToOneNatTrans, lambdaPowNatTrans]
  | succ n ih =>
      change (lambdaPowerStepNatTrans n ≫ lambdaPowerToOneNatTrans n) ≫
        SyntheticCategory.lam = lambdaPowNatTrans (n + 2)
      rw [Category.assoc, ih, lambdaPowerStepNatTrans_comp]

/-- The component of the factor preceding the final multiplication by λ. -/
noncomputable def lambdaPowerToOne (X : Syn) (n : ℕ) :
    (SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).obj X ⟶
      (SyntheticCategory.biShift (0, -1)).obj X :=
  (lambdaPowerToOneNatTrans n).app X

theorem lambdaPowerToOne_comp (X : Syn) (n : ℕ) :
    lambdaPowerToOne X n ≫ lambdaPow 1 X = lambdaPow (n + 1) X :=
  congrArg (fun η => η.app X) (lambdaPowerToOneNatTrans_comp (Syn := Syn) n)

/-- Restriction from the `(n+1)`st finite quotient to the first quotient,
constructed by the actual factorization square of the powers of λ. -/
noncomputable def XModLambdaN.toOne (X : Syn) (n : ℕ) :
    XModLambdaN X (n + 1) ⟶ XModLambdaN X 1 :=
  syn_functorial_cofiber.cofibMap (lambdaPow (n + 1) X) (lambdaPow 1 X)
    (lambdaPowerToOne X n) (𝟙 X)
    (by simpa only [Category.comp_id] using lambdaPowerToOne_comp X n)

/-- Restriction preserves the actual quotient inclusion. -/
@[reassoc] theorem XModLambdaN.incl_toOne (X : Syn) (n : ℕ) :
    syn_functorial_cofiber.cofibι (lambdaPow (n + 1) X) ≫
        XModLambdaN.toOne X n =
      syn_functorial_cofiber.cofibι (lambdaPow 1 X) := by
  simpa only [Category.id_comp, XModLambdaN.toOne, XModLambdaN] using
    (syn_functorial_cofiber.cofibMap_ι
    (lambdaPow (n + 1) X) (lambdaPow 1 X)
    (lambdaPowerToOne X n) (𝟙 X)
    (by simpa only [Category.comp_id] using lambdaPowerToOne_comp X n)).symm

/-- The actual cofiber boundaries commute with quotient restriction. -/
@[reassoc] theorem XModLambdaN.toOne_boundary (X : Syn) (n : ℕ) :
    XModLambdaN.toOne X n ≫ syn_functorial_cofiber.cofibδ (lambdaPow 1 X) =
      syn_functorial_cofiber.cofibδ (lambdaPow (n + 1) X) ≫
        (shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n) :=
  syn_functorial_cofiber.cofibMap_δ
    (lambdaPow (n + 1) X) (lambdaPow 1 X)
    (lambdaPowerToOne X n) (𝟙 X)
    (by simpa only [Category.comp_id] using lambdaPowerToOne_comp X n)

@[simp] theorem XModLambdaN.toOne_zero (X : Syn) :
    XModLambdaN.toOne X 0 = 𝟙 (XModLambdaN X 1) := by
  exact syn_functorial_cofiber.cofibMap_id (lambdaPow 1 X)

/-- The restriction commutes with maps of the original synthetic spectra. -/
@[reassoc] theorem XModLambdaN.toOne_naturality {X Y : Syn} (f : X ⟶ Y)
    (n : ℕ) :
    XModLambdaN.map f (n + 1) ≫ XModLambdaN.toOne Y n =
      XModLambdaN.toOne X n ≫ XModLambdaN.map f 1 := by
  dsimp only [XModLambdaN.map, XModLambdaN.toOne, XModLambdaN]
  rw [syn_functorial_cofiber.cofibMap_comp,
    syn_functorial_cofiber.cofibMap_comp]
  congr 1
  · exact (lambdaPowerToOneNatTrans n).naturality f
  · simp


/-! ### The λ-boundary -/

/-- The boundary morphism in the cofiber sequence
`Σ^{0,-1}X →[λ] X → X/λ → Σ^{1,-1}X`.
The identity `lambdaPow_one` makes this the boundary of the given λ. -/
noncomputable def lambdaBocksteinConnecting (X : Syn) :
    XModLambdaN X 1 ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj X) :=
  syn_functorial_cofiber.cofibδ (lambdaPow 1 X)

/-- The boundary agrees with the projection of the original λ-cofiber. -/
@[simp] theorem lambdaBocksteinConnecting_eq_proj (X : Syn) :
    lambdaBocksteinConnecting X = XModLambda.proj X :=
  rfl

/-- The λ-boundary as a natural transformation on synthetic spectra. -/
noncomputable def lambdaBocksteinConnectingNatTrans :
    XModLambdaN.functor (Syn := Syn) 1 ⟶
      SyntheticCategory.biShift (0, (-1 : ℤ)) ⋙ shiftFunctor Syn (1 : ℤ) :=
  XModLambdaN.projNatTrans 1

/-- The λ-Bockstein boundary is natural in the synthetic spectrum. -/
theorem lambdaBocksteinConnecting_naturality {X Y : Syn} (f : X ⟶ Y) :
    XModLambdaN.map f 1 ≫ lambdaBocksteinConnecting Y =
      lambdaBocksteinConnecting X ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).map f) :=
  lambdaBocksteinConnectingNatTrans.naturality f

/-- The maps used by the boundary ESS belong to the λ distinguished triangle. -/
theorem lambdaBockstein_triangle_distinguished (X : Syn) :
    Triangle.mk (SyntheticCategory.lam.app X)
      (XModLambda.incl X) (lambdaBocksteinConnecting X) ∈
        distTriang Syn :=
  XModLambda.triangle_distinguished X

/-- The quotient inclusion is killed by the λ-boundary. -/
theorem lambdaBockstein_incl_comp_connecting (X : Syn) :
    XModLambda.incl X ≫ lambdaBocksteinConnecting X = 0 :=
  comp_distTriang_mor_zero₂₃ _
    (lambdaBockstein_triangle_distinguished X)

/-- The λ-boundary is killed by the suspended λ map. -/
theorem lambdaBockstein_connecting_comp_shift_lambda (X : Syn) :
    lambdaBocksteinConnecting X ≫
      (shiftFunctor Syn (1 : ℤ)).map (SyntheticCategory.lam.app X) = 0 :=
  comp_distTriang_mor_zero₃₁ _
    (lambdaBockstein_triangle_distinguished X)

/-- The quotient inclusion and boundary form a short complex. -/
noncomputable def lambdaBocksteinBoundaryComplex (X : Syn) : ShortComplex Syn :=
  ShortComplex.mk (XModLambda.incl X) (lambdaBocksteinConnecting X)
    (lambdaBockstein_incl_comp_connecting X)

/-- λ naturality induces a map of the boundary short complexes.
Both commuting squares are proved from the cofiber construction. -/
noncomputable def lambdaBocksteinBoundaryComplexMap {X Y : Syn} (f : X ⟶ Y) :
    lambdaBocksteinBoundaryComplex X ⟶ lambdaBocksteinBoundaryComplex Y :=
  ShortComplex.homMk f (XModLambdaN.map f 1)
    ((shiftFunctor Syn (1 : ℤ)).map
      ((SyntheticCategory.biShift (0, (-1 : ℤ))).map f))
    (XModLambdaN.incl_naturality f 1)
    (lambdaBocksteinConnecting_naturality f)

/-- The boundary short complex is functorial, using the already proved
identity and composition laws for finite λ-quotients. -/
noncomputable def lambdaBocksteinBoundaryComplexFunctor : Syn ⥤ ShortComplex Syn where
  obj X := lambdaBocksteinBoundaryComplex X
  map f := lambdaBocksteinBoundaryComplexMap f
  map_id X := by
    ext <;> simp [lambdaBocksteinBoundaryComplexMap,
      lambdaBocksteinBoundaryComplex]
  map_comp f g := by
    ext <;> simp [lambdaBocksteinBoundaryComplexMap,
      lambdaBocksteinBoundaryComplex, Functor.map_comp]

/-! ### The actual maps on represented homotopy groups -/

/-- Postcomposition with the λ-boundary is an additive map on represented
homotopy groups. Taking `T` to be a synthetic sphere gives the bigraded
homotopy map used by the boundary ESS. -/
noncomputable def lambdaBocksteinHomMap (T X : Syn) :
    (T ⟶ XModLambdaN X 1) →+
      (T ⟶ (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj X)) where
  toFun a := a ≫ lambdaBocksteinConnecting X
  map_zero' := zero_comp
  map_add' a b := by simp only [Preadditive.add_comp]

@[simp] theorem lambdaBocksteinHomMap_apply (T X : Syn)
    (a : T ⟶ XModLambdaN X 1) :
    lambdaBocksteinHomMap T X a = a ≫ lambdaBocksteinConnecting X :=
  rfl

/-- Naturality of the boundary on homotopy classes follows from λ
naturality, without a separate hypothesis about the boundary map. -/
theorem lambdaBocksteinHomMap_naturality (T : Syn) {X Y : Syn}
    (f : X ⟶ Y) (a : T ⟶ XModLambdaN X 1) :
    lambdaBocksteinHomMap T Y (a ≫ XModLambdaN.map f 1) =
      lambdaBocksteinHomMap T X a ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).map f) := by
  simp only [lambdaBocksteinHomMap_apply, Category.assoc,
    lambdaBocksteinConnecting_naturality]

/-- Changing the representing object commutes with the boundary map. -/
theorem lambdaBocksteinHomMap_precomp {T U : Syn} (a : U ⟶ T)
    (X : Syn) (b : T ⟶ XModLambdaN X 1) :
    lambdaBocksteinHomMap U X (a ≫ b) = a ≫ lambdaBocksteinHomMap T X b :=
  Category.assoc a b (lambdaBocksteinConnecting X)

/-- A homotopy class in `X/λ` has zero boundary exactly when it lifts to X. -/
theorem lambdaBocksteinHomMap_eq_zero_iff (T X : Syn)
    (a : T ⟶ XModLambdaN X 1) :
    lambdaBocksteinHomMap T X a = 0 ↔
      ∃ b : T ⟶ X, b ≫ XModLambda.incl X = a := by
  change a ≫ lambdaBocksteinConnecting X = 0 ↔ _
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₃ _
      (lambdaBockstein_triangle_distinguished X) a ha
    exact ⟨b, hb.symm⟩
  · rintro ⟨b, rfl⟩
    exact (Category.assoc b (XModLambda.incl X)
      (lambdaBocksteinConnecting X)).trans
      ((congrArg (fun q => b ≫ q)
        (lambdaBockstein_incl_comp_connecting X)).trans (comp_zero))

/-- A class is a boundary exactly when suspended multiplication by λ kills
it. This is exactness at the target of the boundary, in represented Hom. -/
theorem lambdaBocksteinHomMap_range_iff (T X : Syn)
    (b : T ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj X)) :
    (∃ a : T ⟶ XModLambdaN X 1, lambdaBocksteinHomMap T X a = b) ↔
      b ≫ (shiftFunctor Syn (1 : ℤ)).map (SyntheticCategory.lam.app X) = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    change (a ≫ lambdaBocksteinConnecting X) ≫ _ = 0
    rw [Category.assoc, lambdaBockstein_connecting_comp_shift_lambda, comp_zero]
  · intro hb
    obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₁ _
      (lambdaBockstein_triangle_distinguished X) b hb
    exact ⟨a, ha.symm⟩

/-- A class in X maps to zero in `X/λ` exactly when it is divisible by λ. -/
theorem lambdaBockstein_incl_eq_zero_iff (T X : Syn) (a : T ⟶ X) :
    a ≫ XModLambda.incl X = 0 ↔
      ∃ b : T ⟶ (SyntheticCategory.biShift (0, (-1 : ℤ))).obj X,
        b ≫ SyntheticCategory.lam.app X = a := by
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ _
      (lambdaBockstein_triangle_distinguished X) a ha
    exact ⟨b, hb.symm⟩
  · rintro ⟨b, rfl⟩
    exact (Category.assoc b (SyntheticCategory.lam.app X)
      (XModLambda.incl X)).trans
      ((congrArg (fun q => b ≫ q)
        (XModLambda.lam_comp_incl X)).trans (comp_zero))

/-- The map on represented homotopy groups induced by the quotient inclusion. -/
noncomputable def lambdaBocksteinInclHom (T X : Syn) :
    (T ⟶ X) →+ (T ⟶ XModLambdaN X 1) where
  toFun a := a ≫ XModLambda.incl X
  map_zero' := zero_comp
  map_add' a b := by simp only [Preadditive.add_comp]

/-- Suspended multiplication by λ on represented homotopy groups. -/
noncomputable def lambdaBocksteinShiftLambdaHom (T X : Syn) :
    (T ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj X)) →+
        (T ⟶ (shiftFunctor Syn (1 : ℤ)).obj X) where
  toFun a := a ≫ (shiftFunctor Syn (1 : ℤ)).map (SyntheticCategory.lam.app X)
  map_zero' := zero_comp
  map_add' a b := by simp only [Preadditive.add_comp]

/-- Kernel/image form of exactness at the λ-quotient, for use in subquotients. -/
theorem lambdaBocksteinInclHom_range (T X : Syn) :
    (lambdaBocksteinInclHom T X).range = (lambdaBocksteinHomMap T X).ker := by
  ext a
  change (∃ b : T ⟶ X, b ≫ XModLambda.incl X = a) ↔
    lambdaBocksteinHomMap T X a = 0
  exact (lambdaBocksteinHomMap_eq_zero_iff T X a).symm

/-- Kernel/image form of exactness at the target of the λ-boundary. -/
theorem lambdaBocksteinHomMap_range (T X : Syn) :
    (lambdaBocksteinHomMap T X).range =
      (lambdaBocksteinShiftLambdaHom T X).ker := by
  ext b
  change (∃ a : T ⟶ XModLambdaN X 1, lambdaBocksteinHomMap T X a = b) ↔
    b ≫ (shiftFunctor Syn (1 : ℤ)).map (SyntheticCategory.lam.app X) = 0
  exact lambdaBocksteinHomMap_range_iff T X b

/-- The boundary induces an isomorphism from homotopy classes in the
λ-quotient, modulo classes lifted from X, to classes killed by suspended λ.
This is an isomorphism of abelian groups, before taking Adams filtrations. -/
noncomputable def lambdaBocksteinQuotientEquiv (T X : Syn) :
    ((T ⟶ XModLambdaN X 1) ⧸ (lambdaBocksteinInclHom T X).range) ≃+
      (lambdaBocksteinShiftLambdaHom T X).ker := by
  let e : (lambdaBocksteinHomMap T X).range ≃+
      (lambdaBocksteinShiftLambdaHom T X).ker :=
    { toFun := fun a => ⟨a.val, by
        rw [← lambdaBocksteinHomMap_range T X]
        exact a.property⟩
      invFun := fun a => ⟨a.val, by
        rw [lambdaBocksteinHomMap_range T X]
        exact a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact (QuotientAddGroup.quotientAddEquivOfEq
    (lambdaBocksteinInclHom_range T X)).trans
      ((QuotientAddGroup.quotientKerEquivRange
        (lambdaBocksteinHomMap T X)).trans e)

/-- The quotient isomorphism sends a represented class to its actual
λ-boundary; it does not choose an unrelated group isomorphism. -/
@[simp] theorem lambdaBocksteinQuotientEquiv_apply (T X : Syn)
    (a : T ⟶ XModLambdaN X 1) :
    (lambdaBocksteinQuotientEquiv T X
      (QuotientAddGroup.mk a)).val = lambdaBocksteinHomMap T X a := by
  rfl

/-- The induced map on classes modulo those lifted from the original object.
Preservation of the subgroup is proved from quotient-inclusion naturality. -/
noncomputable def lambdaBocksteinQuotientMap (T : Syn) {X Y : Syn}
    (f : X ⟶ Y) :
    ((T ⟶ XModLambdaN X 1) ⧸ (lambdaBocksteinInclHom T X).range) →+
      ((T ⟶ XModLambdaN Y 1) ⧸ (lambdaBocksteinInclHom T Y).range) := by
  let q : (T ⟶ XModLambdaN X 1) →+ (T ⟶ XModLambdaN Y 1) :=
    { toFun := fun a => a ≫ XModLambdaN.map f 1
      map_zero' := zero_comp
      map_add' := fun a b => by simp only [Preadditive.add_comp] }
  refine QuotientAddGroup.map _ _ q ?_
  rintro _ ⟨b, rfl⟩
  refine ⟨b ≫ f, ?_⟩
  change (b ≫ f) ≫ XModLambda.incl Y =
    (b ≫ XModLambda.incl X) ≫ XModLambdaN.map f 1
  exact (Category.assoc b f (XModLambda.incl Y)).trans
    ((congrArg (fun g => b ≫ g) (XModLambdaN.incl_naturality f 1)).trans
      (Category.assoc b (XModLambda.incl X) (XModLambdaN.map f 1)).symm)

@[simp] theorem lambdaBocksteinQuotientMap_mk (T : Syn) {X Y : Syn}
    (f : X ⟶ Y) (a : T ⟶ XModLambdaN X 1) :
    lambdaBocksteinQuotientMap T f (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (a ≫ XModLambdaN.map f 1) :=
  rfl

/-- Suspended λ-torsion is preserved by maps of synthetic objects,
as a direct consequence of λ naturality. -/
noncomputable def lambdaBocksteinTorsionMap (T : Syn) {X Y : Syn}
    (f : X ⟶ Y) :
    (lambdaBocksteinShiftLambdaHom T X).ker →+
      (lambdaBocksteinShiftLambdaHom T Y).ker where
  toFun b := ⟨b.val ≫ (shiftFunctor Syn (1 : ℤ)).map
      ((SyntheticCategory.biShift (0, (-1 : ℤ))).map f), by
    change (b.val ≫ _) ≫
      (shiftFunctor Syn (1 : ℤ)).map (SyntheticCategory.lam.app Y) = 0
    rw [Category.assoc, ← Functor.map_comp, SyntheticCategory.lam.naturality f,
      Functor.map_comp, ← Category.assoc]
    have hb : b.val ≫
        (shiftFunctor Syn (1 : ℤ)).map (SyntheticCategory.lam.app X) = 0 :=
      b.property
    rw [hb, zero_comp]⟩
  map_zero' := Subtype.ext zero_comp
  map_add' a b := Subtype.ext (by
    change (a.val + b.val) ≫ _ = a.val ≫ _ + b.val ≫ _
    simp only [Preadditive.add_comp])

/-- The boundary-induced quotient isomorphism is natural in the synthetic
object. Its commuting square is proved from λ naturality on representatives. -/
theorem lambdaBocksteinQuotientEquiv_naturality (T : Syn) {X Y : Syn}
    (f : X ⟶ Y)
    (a : (T ⟶ XModLambdaN X 1) ⧸ (lambdaBocksteinInclHom T X).range) :
    lambdaBocksteinQuotientEquiv T Y (lambdaBocksteinQuotientMap T f a) =
      lambdaBocksteinTorsionMap T f (lambdaBocksteinQuotientEquiv T X a) := by
  induction a using QuotientAddGroup.induction_on with
  | H a =>
    apply Subtype.ext
    change lambdaBocksteinHomMap T Y (a ≫ XModLambdaN.map f 1) =
      lambdaBocksteinHomMap T X a ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).map f)
    exact lambdaBocksteinHomMap_naturality T f a

/-- The boundary map on bigraded homotopy groups. The target is left as a
suspended object, so no unproved Adams-filtration suspension rule is used. -/
noncomputable def lambdaBocksteinHomotopyMap (X : Syn) (m w : ℤ) :
    (Smn (Syn := Syn) m w ⟶ XModLambdaN X 1) →+
      (Smn (Syn := Syn) m w ⟶ (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj X)) :=
  lambdaBocksteinHomMap (Smn m w) X

/-! ### Homotopy groups of every finite λ-quotient

The following short exact sequence retains the actual inclusion and boundary
maps. It computes the group as an extension, without asserting that this
extension splits or discarding the maps needed by the boundary ESS.
-/

namespace LambdaPowerBoundary

/-- The actual target of the finite-power boundary is `Σ^{1,-n} X`.
This is an isomorphism of synthetic objects, without an assertion about
how the separately specified Adams filtrations transform under suspension. -/
noncomputable def targetIso (X : Syn) (n : ℕ) :
    (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X) ≅
      (SyntheticCategory.biShift (1, -(n : ℤ))).obj X :=
  ((SyntheticCategory.biShift_compat (Syn := Syn) 1).app
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X)).symm ≪≫
    (SyntheticCategory.biShift_comp (0, -(n : ℤ)) (1, 0)).app X ≪≫
      eqToIso (by simp)

/-- Removing the target suspension sends the boundary of a class of
homotopy bidegree `(m,w)` to bidegree `(m-1,w+n)` in X. -/
noncomputable def targetHomEquiv (X : Syn) (n : ℕ) (m w : ℤ) :
    (Smn (Syn := Syn) m w ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X)) ≃
        (Smn (Syn := Syn) (m - 1) (w + n) ⟶ X) := by
  let e : (Smn (Syn := Syn) (m - 1) (w + n) ⟶ X) ≃
      (Smn (Syn := Syn) m w ⟶
        (SyntheticCategory.biShift (1, -(n : ℤ))).obj X) := by
    simpa using susp_invariance (m - 1) (w + n) 1 (-(n : ℤ)) X
  exact (Iso.homCongr (Iso.refl _) (targetIso X n)).trans e.symm

/-- Multiplication by `λ^n` on represented homotopy groups. -/
noncomputable def mulHom (T X : Syn) (n : ℕ) :
    (T ⟶ (SyntheticCategory.biShift (0, -(n : ℤ))).obj X) →+ (T ⟶ X) where
  toFun a := a ≫ lambdaPow n X
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

/-- The actual quotient inclusion on represented homotopy groups. -/
noncomputable def inclHom (T X : Syn) (n : ℕ) :
    (T ⟶ X) →+ (T ⟶ XModLambdaN X n) where
  toFun a := a ≫ syn_functorial_cofiber.cofibι (lambdaPow n X)
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

/-- The actual boundary on represented homotopy groups. -/
noncomputable def boundaryHom (T X : Syn) (n : ℕ) :
    (T ⟶ XModLambdaN X n) →+
      (T ⟶ (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X)) where
  toFun a := a ≫ syn_functorial_cofiber.cofibδ (lambdaPow n X)
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

/-- The actual boundary of the reduction of a finite-quotient homotopy
class. This is an equality of specified homotopy classes, not an existence
statement obtained from exactness. -/
theorem boundaryHom_toOne (T X : Syn) (n : ℕ)
    (a : T ⟶ XModLambdaN X (n + 1)) :
    lambdaBocksteinHomMap T X (a ≫ XModLambdaN.toOne X n) =
      boundaryHom T X (n + 1) a ≫
        (shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n) := by
  exact (Category.assoc a (XModLambdaN.toOne X n)
    (syn_functorial_cofiber.cofibδ (lambdaPow 1 X))).trans
      ((congrArg (fun f => a ≫ f) (XModLambdaN.toOne_boundary X n)).trans
        (Category.assoc a
          (syn_functorial_cofiber.cofibδ (lambdaPow (n + 1) X))
          ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n))).symm)

/-- Suspended multiplication by `λ^n` on represented homotopy groups. -/
noncomputable def shiftMulHom (T X : Syn) (n : ℕ) :
    (T ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X)) →+
        (T ⟶ (shiftFunctor Syn (1 : ℤ)).obj X) where
  toFun a := a ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n X)
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

theorem mul_range (T X : Syn) (n : ℕ) :
    (mulHom T X n).range = (inclHom T X n).ker := by
  ext a
  change (∃ b, b ≫ lambdaPow n X = a) ↔
    a ≫ syn_functorial_cofiber.cofibι (lambdaPow n X) = 0
  constructor
  · rintro ⟨b, rfl⟩
    have h : lambdaPow n X ≫ syn_functorial_cofiber.cofibι (lambdaPow n X) = 0 :=
      comp_distTriang_mor_zero₁₂ _ (XModLambdaN.triangle_distinguished X n)
    rw [Category.assoc, h, comp_zero]
  · intro ha
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ _
      (XModLambdaN.triangle_distinguished X n) a ha
    exact ⟨b, hb.symm⟩

theorem incl_range (T X : Syn) (n : ℕ) :
    (inclHom T X n).range = (boundaryHom T X n).ker := by
  ext a
  change (∃ b, b ≫ syn_functorial_cofiber.cofibι (lambdaPow n X) = a) ↔
    a ≫ syn_functorial_cofiber.cofibδ (lambdaPow n X) = 0
  constructor
  · rintro ⟨b, rfl⟩
    have h : syn_functorial_cofiber.cofibι (lambdaPow n X) ≫
        syn_functorial_cofiber.cofibδ (lambdaPow n X) = 0 :=
      comp_distTriang_mor_zero₂₃ _ (XModLambdaN.triangle_distinguished X n)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => b ≫ q) h).trans comp_zero)
  · intro ha
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₃ _
      (XModLambdaN.triangle_distinguished X n) a ha
    exact ⟨b, hb.symm⟩

theorem boundary_range (T X : Syn) (n : ℕ) :
    (boundaryHom T X n).range = (shiftMulHom T X n).ker := by
  ext b
  change (∃ a, a ≫ syn_functorial_cofiber.cofibδ (lambdaPow n X) = b) ↔
    b ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n X) = 0
  constructor
  · rintro ⟨a, rfl⟩
    have h : syn_functorial_cofiber.cofibδ (lambdaPow n X) ≫
        (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n X) = 0 :=
      comp_distTriang_mor_zero₃₁ _ (XModLambdaN.triangle_distinguished X n)
    rw [Category.assoc, h, comp_zero]
  · intro hb
    obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₁ _
      (XModLambdaN.triangle_distinguished X n) b hb
    exact ⟨a, ha.symm⟩

/-- The left injection in the finite-quotient homotopy short exact sequence. -/
noncomputable def cokernelIncl (T X : Syn) (n : ℕ) :
    ((T ⟶ X) ⧸ (mulHom T X n).range) →+ (T ⟶ XModLambdaN X n) :=
  (QuotientAddGroup.kerLift (inclHom T X n)).comp
    (QuotientAddGroup.quotientAddEquivOfEq (mul_range T X n)).toAddMonoidHom

@[simp] theorem cokernelIncl_mk (T X : Syn) (n : ℕ) (a : T ⟶ X) :
    cokernelIncl T X n (QuotientAddGroup.mk a) = inclHom T X n a := rfl

theorem cokernelIncl_injective (T X : Syn) (n : ℕ) :
    Function.Injective (cokernelIncl T X n) :=
  (QuotientAddGroup.kerLift_injective (inclHom T X n)).comp
    (QuotientAddGroup.quotientAddEquivOfEq (mul_range T X n)).injective

/-- The right surjection is induced by the cofiber boundary itself. -/
noncomputable def boundaryToKernel (T X : Syn) (n : ℕ) :
    (T ⟶ XModLambdaN X n) →+ (shiftMulHom T X n).ker where
  toFun a := ⟨boundaryHom T X n a, by
    rw [← boundary_range T X n]
    exact ⟨a, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp] theorem boundaryToKernel_apply (T X : Syn) (n : ℕ)
    (a : T ⟶ XModLambdaN X n) :
    (boundaryToKernel T X n a).val =
      a ≫ syn_functorial_cofiber.cofibδ (lambdaPow n X) := rfl

theorem boundaryToKernel_surjective (T X : Syn) (n : ℕ) :
    Function.Surjective (boundaryToKernel T X n) := by
  intro b
  have hb : b.val ∈ (boundaryHom T X n).range := by
    simpa only [boundary_range T X n] using b.property
  obtain ⟨a, ha⟩ := hb
  exact ⟨a, Subtype.ext ha⟩

theorem cokernelIncl_range (T X : Syn) (n : ℕ) :
    (cokernelIncl T X n).range = (boundaryToKernel T X n).ker := by
  ext a
  constructor
  · rintro ⟨q, rfl⟩
    induction q using QuotientAddGroup.induction_on with
    | H b =>
      apply Subtype.ext
      change boundaryHom T X n (inclHom T X n b) = 0
      have hb : inclHom T X n b ∈ (inclHom T X n).range := ⟨b, rfl⟩
      rwa [incl_range T X n] at hb
  · intro ha
    have hb : a ∈ (boundaryHom T X n).ker := congrArg Subtype.val ha
    rw [← incl_range T X n] at hb
    obtain ⟨b, rfl⟩ := hb
    exact ⟨QuotientAddGroup.mk b, rfl⟩

/-- The finite-quotient homotopy sequence with quotient and torsion endpoints. -/
noncomputable def homotopyComplex (T X : Syn) (n : ℕ) :
    ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk (AddCommGrpCat.ofHom (cokernelIncl T X n))
    (AddCommGrpCat.ofHom (boundaryToKernel T X n)) (by
      apply ConcreteCategory.hom_ext
      intro q
      have hq : cokernelIncl T X n q ∈ (cokernelIncl T X n).range := ⟨q, rfl⟩
      rw [cokernelIncl_range T X n] at hq
      exact hq)

/-- `0 → coker(λ^n) → π(X/λ^n) → ker(Σλ^n) → 0`.
Taking `T = Smn m w` gives every bigraded homotopy group. No splitting,
filtration bound, or comparison of spectral sequences is assumed. -/
theorem homotopy_shortExact (T X : Syn) (n : ℕ) :
    (homotopyComplex T X n).ShortExact where
  exact := ShortComplex.ab_exact_iff_range_eq_ker.2
    (cokernelIncl_range T X n)
  mono_f := (AddCommGrpCat.mono_iff_injective _).2
    (cokernelIncl_injective T X n)
  epi_g := (AddCommGrpCat.epi_iff_surjective _).2
    (boundaryToKernel_surjective T X n)

/-- Equality of boundaries is precisely the ambiguity of lifting from X. -/
theorem boundary_eq_iff (T X : Syn) (n : ℕ)
    (a b : T ⟶ XModLambdaN X n) :
    boundaryHom T X n a = boundaryHom T X n b ↔
      ∃ c : T ⟶ X, inclHom T X n c = a - b := by
  rw [← sub_eq_zero, ← map_sub]
  change a - b ∈ (boundaryHom T X n).ker ↔ _
  rw [← incl_range T X n]
  rfl

end LambdaPowerBoundary

/-! ### Geometric capping and its actual boundary -/

namespace SyntheticCofiberTower

/-- The relative cofiber of two stages, with no exact-couple construction. -/
noncomputable abbrev relative (T : SyntheticCofiberTower Syn)
    (a b : ℕ) (h : a ≤ b) : Syn :=
  syn_functorial_cofiber.cofib (T.transition a b h)

noncomputable def quotient (T : SyntheticCofiberTower Syn) (n : ℕ) :
    SyntheticCofiberTower Syn := T ⋙ XModLambdaN.functor n

end SyntheticCofiberTower

namespace LambdaCofiberGeometry

/-- The disk cofiber is its suspended boundary. -/
noncomputable def diskBoundaryIso {B D : Syn} (i : B ⟶ D) (hD : IsZero D) :
    syn_functorial_cofiber.cofib i ≅ (shiftFunctor Syn (1 : ℤ)).obj B := by
  let δ := syn_functorial_cofiber.cofibδ i
  haveI : IsIso δ := by
    apply isIso_of_yoneda_map_bijective
    intro T
    constructor
    · intro f g hfg
      change f ≫ δ = g ≫ δ at hfg
      have hz : (f - g) ≫ δ = 0 := by
        rw [Preadditive.sub_comp, hfg, sub_self]
      obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₃ _
        (syn_functorial_cofiber.cofib_distinguished i) (f - g) hz
      have hz' : f - g = 0 := ha.trans
        ((congrArg (fun q : T ⟶ D => q ≫ syn_functorial_cofiber.cofibι i)
          (hD.eq_zero_of_tgt a)).trans zero_comp)
      exact sub_eq_zero.mp hz'
    · intro f
      obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₁ _
        (syn_functorial_cofiber.cofib_distinguished i) f
        (((shiftFunctor Syn (1 : ℤ)).map_isZero hD).eq_zero_of_tgt _)
      exact ⟨a, ha.symm⟩
  exact asIso δ

/-- The common cone remembers the relative class before passing to the
lambda quotient. -/
noncomputable abbrev commonCone {A Y : Syn} (j : Y ⟶ A) (n : ℕ) : Syn :=
  syn_functorial_cofiber.cofib (lambdaPow n Y ≫ j)

noncomputable def toRelative {A Y : Syn} (j : Y ⟶ A) (n : ℕ) :
    commonCone j n ⟶ syn_functorial_cofiber.cofib j :=
  syn_functorial_cofiber.cofibMap (lambdaPow n Y ≫ j) j
    (lambdaPow n Y) (𝟙 A) (by simp)

noncomputable def toQuotient {A Y : Syn} (j : Y ⟶ A) (n : ℕ) :
    commonCone j n ⟶ XModLambdaN A n :=
  syn_functorial_cofiber.cofibMap (lambdaPow n Y ≫ j) (lambdaPow n A)
    ((SyntheticCategory.biShift (0, -(n : ℤ))).map j) (𝟙 A)
    (by simpa only [Category.comp_id] using lambdaPow_naturality n j)

@[reassoc] theorem toRelative_boundary {A Y : Syn} (j : Y ⟶ A) (n : ℕ) :
    toRelative j n ≫ syn_functorial_cofiber.cofibδ j =
      syn_functorial_cofiber.cofibδ (lambdaPow n Y ≫ j) ≫
        (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y) :=
  syn_functorial_cofiber.cofibMap_δ _ _ _ _ _

@[reassoc] theorem toQuotient_boundary {A Y : Syn} (j : Y ⟶ A) (n : ℕ) :
    toQuotient j n ≫ syn_functorial_cofiber.cofibδ (lambdaPow n A) =
      syn_functorial_cofiber.cofibδ (lambdaPow n Y ≫ j) ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(n : ℤ))).map j) :=
  syn_functorial_cofiber.cofibMap_δ _ _ _ _ _

/-- A specified relative class whose actual boundary is divisible by
lambda^n lifts to the common cone, retaining both that class and its chosen
divided boundary. The lift and its correction are constructed by exactness. -/
theorem exists_commonLift_of_relative_boundary {A Y S : Syn}
    (j : Y ⟶ A) (n : ℕ) (x : S ⟶ syn_functorial_cofiber.cofib j)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y))
    (hxy : x ≫ syn_functorial_cofiber.cofibδ j =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y)) :
    ∃ c : S ⟶ commonCone j n,
      c ≫ toRelative j n = x ∧
      c ≫ syn_functorial_cofiber.cofibδ (lambdaPow n Y ≫ j) = y := by
  have hjzero : syn_functorial_cofiber.cofibδ j ≫
      (shiftFunctor Syn (1 : ℤ)).map j = 0 :=
    comp_distTriang_mor_zero₃₁ _ (syn_functorial_cofiber.cofib_distinguished j)
  have hjzero' : syn_functorial_cofiber.cofibι (lambdaPow n Y ≫ j) ≫
      syn_functorial_cofiber.cofibδ (lambdaPow n Y ≫ j) = 0 :=
    comp_distTriang_mor_zero₂₃ _
      (syn_functorial_cofiber.cofib_distinguished (lambdaPow n Y ≫ j))
  have hyzero : y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y ≫ j) = 0 := by
    rw [Functor.map_comp, ← Category.assoc, ← hxy, Category.assoc,
      hjzero, comp_zero]
  obtain ⟨c, hc⟩ := Triangle.coyoneda_exact₁ _
    (syn_functorial_cofiber.cofib_distinguished (lambdaPow n Y ≫ j)) y hyzero
  change S ⟶ commonCone j n at c
  change y = c ≫ syn_functorial_cofiber.cofibδ (lambdaPow n Y ≫ j) at hc
  have hcz : (c ≫ toRelative j n) ≫ syn_functorial_cofiber.cofibδ j =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y) := by
    rw [Category.assoc, toRelative_boundary, ← Category.assoc, ← hc]
  have hz : (x - c ≫ toRelative j n) ≫ syn_functorial_cofiber.cofibδ j = 0 := by
    rw [Preadditive.sub_comp, hxy, hcz, sub_self]
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₃ _
    (syn_functorial_cofiber.cofib_distinguished j)
    (x - c ≫ toRelative j n) hz
  change S ⟶ A at a
  change x - c ≫ toRelative j n = a ≫ syn_functorial_cofiber.cofibι j at ha
  have hi : syn_functorial_cofiber.cofibι (lambdaPow n Y ≫ j) ≫
      toRelative j n = syn_functorial_cofiber.cofibι j := by
    exact (syn_functorial_cofiber.cofibMap_ι (lambdaPow n Y ≫ j) j
      (lambdaPow n Y) (𝟙 A) (by simp)).symm.trans (Category.id_comp _)
  refine ⟨c + a ≫ syn_functorial_cofiber.cofibι (lambdaPow n Y ≫ j), ?_, ?_⟩
  · rw [Preadditive.add_comp, Category.assoc, hi, ← ha]
    abel
  · rw [Preadditive.add_comp, Category.assoc,
      hjzero', comp_zero, add_zero]
    exact hc.symm

/-- The lambda cap of a fixed relative source is constructed, together
with a common-cone witness preserving that source and the divided boundary. -/
theorem exists_cap_of_relative_boundary {A Y S : Syn}
    (j : Y ⟶ A) (n : ℕ) (x : S ⟶ syn_functorial_cofiber.cofib j)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y))
    (hxy : x ≫ syn_functorial_cofiber.cofibδ j =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y)) :
    ∃ (c : S ⟶ commonCone j n) (z : S ⟶ XModLambdaN A n),
      c ≫ toRelative j n = x ∧ c ≫ toQuotient j n = z ∧
      c ≫ syn_functorial_cofiber.cofibδ (lambdaPow n Y ≫ j) = y ∧
      z ≫ syn_functorial_cofiber.cofibδ (lambdaPow n A) =
        y ≫ (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(n : ℤ))).map j) := by
  obtain ⟨c, hx, hy⟩ := exists_commonLift_of_relative_boundary j n x y hxy
  refine ⟨c, c ≫ toQuotient j n, hx, rfl, hy, ?_⟩
  rw [Category.assoc, toQuotient_boundary, ← Category.assoc, hy]

/-- The fixed relative source also determines a capped representative in
X/lambda. Its actual boundary is the divided target followed by the
remaining lambda power and the inclusion from the deeper stage. -/
theorem exists_singleCap_of_relative_boundary {A Y S : Syn}
    (j : Y ⟶ A) (n : ℕ) (x : S ⟶ syn_functorial_cofiber.cofib j)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).obj Y))
    (hxy : x ≫ syn_functorial_cofiber.cofibδ j =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow (n + 1) Y)) :
    ∃ c : S ⟶ commonCone j (n + 1),
      c ≫ toRelative j (n + 1) = x ∧
      c ≫ syn_functorial_cofiber.cofibδ (lambdaPow (n + 1) Y ≫ j) = y ∧
      ((c ≫ toQuotient j (n + 1)) ≫ XModLambdaN.toOne A n) ≫
          lambdaBocksteinConnecting A =
        y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne Y n) ≫
          (shiftFunctor Syn (1 : ℤ)).map
            ((SyntheticCategory.biShift (0, (-1 : ℤ))).map j) := by
  obtain ⟨c, hx, hy⟩ := exists_commonLift_of_relative_boundary j (n + 1) x y hxy
  have hn : (SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).map j ≫
      lambdaPowerToOne A n = lambdaPowerToOne Y n ≫
        (SyntheticCategory.biShift (0, (-1 : ℤ))).map j :=
    (lambdaPowerToOneNatTrans n).naturality j
  have hb : (c ≫ toQuotient j (n + 1)) ≫
      syn_functorial_cofiber.cofibδ (lambdaPow (n + 1) A) =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map
        ((SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).map j) := by
    rw [Category.assoc, toQuotient_boundary, ← Category.assoc, hy]
  refine ⟨c, hx, hy, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => (c ≫ toQuotient j (n + 1)) ≫ q)
      (XModLambdaN.toOne_boundary A n)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPowerToOne A n)) hb).trans (by
            rw [Category.assoc, ← Functor.map_comp, hn, Functor.map_comp]))))

/-- A boundary--disk square in the existing homotopy-category interface.
The equality concerns actual morphisms. This data does not construct a
model cofibration or realize a specified Adams page class; below the chosen
cofiber functor supplies a compatible gluing of this square. -/
structure DiskData {A Y : Syn} (j : Y ⟶ A) (n : ℕ) where
  boundary : Syn
  disk : Syn
  disk_isZero : IsZero disk
  inclusion : boundary ⟶ disk
  diskMap : disk ⟶ A
  target : boundary ⟶ (SyntheticCategory.biShift (0, -(n : ℤ))).obj Y
  comm : target ≫ (lambdaPow n Y ≫ j) = inclusion ≫ diskMap

namespace DiskData
variable {A Y : Syn} {j : Y ⟶ A} {n : ℕ} (d : DiskData j n)

/-- Glue the chosen disk to the cone on its divided boundary. -/
noncomputable def glued :
    syn_functorial_cofiber.cofib d.inclusion ⟶ commonCone j n :=
  syn_functorial_cofiber.cofibMap d.inclusion (lambdaPow n Y ≫ j)
    d.target d.diskMap d.comm

/-- The relative representative induced by this same disk square is
preserved by the common cone. -/
theorem glued_toRelative :
    d.glued ≫ toRelative j n =
      syn_functorial_cofiber.cofibMap d.inclusion j
        (d.target ≫ lambdaPow n Y) d.diskMap
        (by simpa only [Category.assoc] using d.comm) := by
  dsimp only [glued, toRelative]
  rw [syn_functorial_cofiber.cofibMap_comp]
  simp only [Category.comp_id]

/-- Mapping the common cone to the finite lambda quotient is the cap. -/
theorem glued_toQuotient :
    d.glued ≫ toQuotient j n =
      syn_functorial_cofiber.cofibMap d.inclusion (lambdaPow n A)
        (d.target ≫ (SyntheticCategory.biShift (0, -(n : ℤ))).map j)
        d.diskMap
        (by rw [Category.assoc, lambdaPow_naturality n j]; exact d.comm) := by
  dsimp only [glued, toQuotient, XModLambdaN]
  simpa only [Category.comp_id] using
    syn_functorial_cofiber.cofibMap_comp d.inclusion (lambdaPow n Y ≫ j)
      (lambdaPow n A) d.target d.diskMap
      ((SyntheticCategory.biShift (0, -(n : ℤ))).map j) (𝟙 A) d.comm
      (by simpa only [Category.comp_id] using lambdaPow_naturality n j)

/-- The common-cone class on the suspension of the disk boundary. -/
noncomputable def sphereClass :
    (shiftFunctor Syn (1 : ℤ)).obj d.boundary ⟶ commonCone j n :=
  (diskBoundaryIso d.inclusion d.disk_isZero).inv ≫ d.glued

/-- The connecting map reads off precisely the divided boundary. -/
@[reassoc] theorem sphereClass_boundary :
    d.sphereClass ≫ syn_functorial_cofiber.cofibδ (lambdaPow n Y ≫ j) =
      (shiftFunctor Syn (1 : ℤ)).map d.target := by
  have h : d.glued ≫ syn_functorial_cofiber.cofibδ (lambdaPow n Y ≫ j) =
      (diskBoundaryIso d.inclusion d.disk_isZero).hom ≫
        (shiftFunctor Syn (1 : ℤ)).map d.target :=
    syn_functorial_cofiber.cofibMap_δ d.inclusion
      (lambdaPow n Y ≫ j) d.target d.diskMap d.comm
  change (_ ≫ d.glued) ≫ _ = _
  rw [Category.assoc, h, ← Category.assoc]
  rw [Iso.inv_hom_id, Category.id_comp]

noncomputable def capped :
    (shiftFunctor Syn (1 : ℤ)).obj d.boundary ⟶ XModLambdaN A n :=
  d.sphereClass ≫ toQuotient j n

/-- After capping, the lambda boundary is the suspended target, included
from the deeper stage. -/
@[reassoc] theorem capped_boundary :
    d.capped ≫ syn_functorial_cofiber.cofibδ (lambdaPow n A) =
      (shiftFunctor Syn (1 : ℤ)).map d.target ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(n : ℤ))).map j) := by
  dsimp only [capped]
  rw [Category.assoc, toQuotient_boundary, ← Category.assoc,
    sphereClass_boundary]

/-- The relative boundary before capping is multiplication by lambda^n
of the same target. -/
@[reassoc] theorem relative_boundary :
    (d.sphereClass ≫ toRelative j n) ≫ syn_functorial_cofiber.cofibδ j =
      (shiftFunctor Syn (1 : ℤ)).map d.target ≫
        (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y) := by
  rw [Category.assoc, toRelative_boundary, ← Category.assoc,
    sphereClass_boundary]

/-- Mapping a capped class to an earlier stage preserves its specified
boundary representative. -/
@[reassoc] theorem capped_postcomp_boundary {Z : Syn} (k : A ⟶ Z) :
    (d.capped ≫ XModLambdaN.map k n) ≫
        syn_functorial_cofiber.cofibδ (lambdaPow n Z) =
      (shiftFunctor Syn (1 : ℤ)).map d.target ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(n : ℤ))).map (j ≫ k)) := by
  have h := XModLambdaN.proj_naturality k n
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => d.capped ≫ q) h).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(n : ℤ))).map k))
            d.capped_boundary).trans (by
              simp only [Functor.map_comp, Category.assoc]))))

/-- Reducing the capped class to the first quotient computes its actual
single-lambda boundary, with the remaining power on the target. -/
@[reassoc] theorem capped_toOne_boundary {m : ℕ}
    (e : DiskData j (m + 1)) :
    (e.capped ≫ XModLambdaN.toOne A m) ≫ lambdaBocksteinConnecting A =
      (shiftFunctor Syn (1 : ℤ)).map
          (e.target ≫ lambdaPowerToOne Y m) ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).map j) := by
  have hn : (SyntheticCategory.biShift (0, -((m + 1 : ℕ) : ℤ))).map j ≫
      lambdaPowerToOne A m = lambdaPowerToOne Y m ≫
        (SyntheticCategory.biShift (0, (-1 : ℤ))).map j :=
    (lambdaPowerToOneNatTrans m).naturality j
  have h := XModLambdaN.toOne_boundary A m
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => e.capped ≫ q) h).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPowerToOne A m)) e.capped_boundary).trans (by
            rw [Category.assoc, ← Functor.map_comp, hn,
              Functor.map_comp, ← Category.assoc, ← Functor.map_comp]))))

end DiskData

/-! ### Filtration positions read from the actual tower -/

variable (T : SyntheticCofiberTower Syn) {a b n : ℕ} (hab : a ≤ b)
    (d : DiskData (T.transition a b hab) n)

/-- Include a cap made at stage `a` into the quotient of stage zero. -/
noncomputable def cappedAtBase :
    (shiftFunctor Syn (1 : ℤ)).obj d.boundary ⟶
      XModLambdaN (T.stage 0) n :=
  d.capped ≫ XModLambdaN.map (T.transition 0 a (Nat.zero_le a)) n

/-- The capped source factors through stage `a` of the quotient tower. -/
theorem cappedAtBase_mem :
    cappedAtBase T hab d ∈ (T.quotient n).homFiltration
      ((shiftFunctor Syn (1 : ℤ)).obj d.boundary) a :=
  ⟨d.capped, rfl⟩

/-- The cap boundary factors through precisely the named deeper stage;
no filtration bound or spectral-sequence assumption is used. -/
theorem cappedAtBase_boundary :
    cappedAtBase T hab d ≫
        syn_functorial_cofiber.cofibδ (lambdaPow n (T.stage 0)) =
      (shiftFunctor Syn (1 : ℤ)).map d.target ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(n : ℤ))).map
            (T.transition 0 b (Nat.zero_le b))) := by
  have h := d.capped_postcomp_boundary (T.transition 0 a (Nat.zero_le a))
  rw [T.transition_comp] at h
  exact h

/-- The target of the cap boundary lies in stage `b` of the suspended,
weight-shifted tower. Identifying this with the named Adams filtration
requires the geometric realization of that Adams tower. -/
theorem cappedAtBase_boundary_mem :
    cappedAtBase T hab d ≫
        syn_functorial_cofiber.cofibδ (lambdaPow n (T.stage 0)) ∈
      SyntheticCofiberTower.homFiltration
        (T ⋙ SyntheticCategory.biShift (0, -(n : ℤ)) ⋙
          shiftFunctor Syn (1 : ℤ))
        ((shiftFunctor Syn (1 : ℤ)).obj d.boundary) b :=
  ⟨(shiftFunctor Syn (1 : ℤ)).map d.target, (cappedAtBase_boundary T hab d).symm⟩

end LambdaCofiberGeometry

end KIPBase.Synthetic
