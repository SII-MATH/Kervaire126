/-
  KIPBase.StableHomotopy.TensorTriangulatedCategory
  Closed symmetric tensor triangulated category structure.

  Blueprint: prerequisites.tex, Definition prereq:def:closed-symmetric-tensor-triangulated
  Reference: Hovey–Palmieri–Strickland, Definition A.2.1
-/
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

namespace KIPBase.StableHomotopy

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory Pretriangulated

universe u v

/-! ## Functorial Cofiber

General classes for a pretriangulated category with a canonical cofiber construction.
These are parameterized by an arbitrary category C (no SH dependency). -/

section FunctorialCofiber

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Limits.HasZeroObject C]
  [Pretriangulated C]

/-- A pretriangulated category has **functorial cofiber** when there is a canonical
    choice of cofiber for every morphism, together with canonical structure maps
    and functoriality from commutative squares.

    Blueprint: prerequisites.tex (functorial cofiber construction). -/
class HasFunctorialCofiber where
  /-- Canonical cofiber object for a morphism f : X ⟶ Y. -/
  cofib : {X Y : C} → (X ⟶ Y) → C
  /-- Canonical inclusion Y ⟶ cofib f. -/
  cofibι : {X Y : C} → (f : X ⟶ Y) → Y ⟶ cofib f
  /-- Canonical connecting map cofib f ⟶ X⟦1⟧. -/
  cofibδ : {X Y : C} → (f : X ⟶ Y) → cofib f ⟶ (shiftFunctor C (1 : ℤ)).obj X
  /-- The cofiber triangle X →[f] Y →[ι] cofib f →[δ] X⟦1⟧ is distinguished. -/
  cofib_distinguished : ∀ {X Y : C} (f : X ⟶ Y),
    Triangle.mk f (cofibι f) (cofibδ f) ∈ distTriang C
  /-- Functoriality: a commutative square α ≫ f₂ = f₁ ≫ β induces a map
      (cofib f₁ ⟶ cofib f₂) on cofibers. -/
  cofibMap : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂), α ≫ f₂ = f₁ ≫ β →
    (cofib f₁ ⟶ cofib f₂)
  /-- cofibMap is compatible with the inclusion maps ι:
      β ≫ cofibι f₂ = cofibι f₁ ≫ cofibMap f₁ f₂ α β h. -/
  cofibMap_ι : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂) (h : α ≫ f₂ = f₁ ≫ β),
    β ≫ cofibι f₂ = cofibι f₁ ≫ cofibMap f₁ f₂ α β h
  /-- cofibMap is compatible with the connecting maps δ:
      cofibMap f₁ f₂ α β h ≫ cofibδ f₂ = cofibδ f₁ ≫ (shiftFunctor C 1).map α. -/
  cofibMap_δ : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂) (h : α ≫ f₂ = f₁ ≫ β),
    cofibMap f₁ f₂ α β h ≫ cofibδ f₂ = cofibδ f₁ ≫ (shiftFunctor C (1 : ℤ)).map α
  /-- The cofiber map of the identity square is the identity. -/
  cofibMap_id : ∀ {X Y : C} (f : X ⟶ Y),
    cofibMap f f (𝟙 X) (𝟙 Y) (by simp) = 𝟙 (cofib f)
  /-- Cofiber maps respect vertical composition of commutative squares. -/
  cofibMap_comp : ∀ {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C}
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
      (α₁₂ : X₁ ⟶ X₂) (β₁₂ : Y₁ ⟶ Y₂)
      (α₂₃ : X₂ ⟶ X₃) (β₂₃ : Y₂ ⟶ Y₃)
      (h₁₂ : α₁₂ ≫ f₂ = f₁ ≫ β₁₂)
      (h₂₃ : α₂₃ ≫ f₃ = f₂ ≫ β₂₃),
    cofibMap f₁ f₂ α₁₂ β₁₂ h₁₂ ≫
        cofibMap f₂ f₃ α₂₃ β₂₃ h₂₃ =
      cofibMap f₁ f₃ (α₁₂ ≫ α₂₃) (β₁₂ ≫ β₂₃) (by
        simp only [Category.assoc, h₂₃]
        rw [← Category.assoc, h₁₂, Category.assoc])

namespace HasFunctorialCofiber

/-- The pointwise cofiber of a natural transformation, using the selected
functorial cofiber on objects and commutative squares. -/
noncomputable def natCofiberFunctor [HasFunctorialCofiber C]
    {F G : Functor C C} (τ : NatTrans F G) : Functor C C where
  obj X := cofib (τ.app X)
  map {X Y} f :=
    cofibMap (τ.app X) (τ.app Y) (F.map f) (G.map f) (τ.naturality f)
  map_id X := by
    simpa only [F.map_id, G.map_id] using cofibMap_id (τ.app X)
  map_comp f g := by
    simpa only [F.map_comp, G.map_comp] using
      (cofibMap_comp (τ.app _) (τ.app _) (τ.app _)
        (F.map f) (G.map f) (F.map g) (G.map g)
        (τ.naturality f) (τ.naturality g)).symm

end HasFunctorialCofiber

/-- Coherent preservation of the selected cofiber triangles by a functor.
The last field is the morphism part of the stable 3×3 lemma: the comparison
on the third vertices is natural in commutative squares, while the first two
vertices are fixed by identities. -/
structure PreservesFunctorialCofibers [HasFunctorialCofiber C]
    (H : Functor C C) [H.CommShift ℤ] where
  triangleIso {A B : C} (f : A ⟶ B) :
    H.mapTriangle.obj (Triangle.mk f (HasFunctorialCofiber.cofibι f)
      (HasFunctorialCofiber.cofibδ f)) ≅
      Triangle.mk (H.map f) (HasFunctorialCofiber.cofibι (H.map f))
        (HasFunctorialCofiber.cofibδ (H.map f))
  hom₁ {A B : C} (f : A ⟶ B) :
    (triangleIso f).hom.hom₁ = 𝟙 (H.obj A)
  hom₂ {A B : C} (f : A ⟶ B) :
    (triangleIso f).hom.hom₂ = 𝟙 (H.obj B)
  naturality {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
      (a : A ⟶ A') (b : B ⟶ B') (h : a ≫ g = f ≫ b) :
    H.map (HasFunctorialCofiber.cofibMap f g a b h) ≫
      (triangleIso g).hom.hom₃ =
      (triangleIso f).hom.hom₃ ≫
        HasFunctorialCofiber.cofibMap (H.map f) (H.map g) (H.map a) (H.map b)
          (by simpa only [Functor.map_comp] using congrArg H.map h)

end FunctorialCofiber

section TensorFunctorialCofiber

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Limits.HasZeroObject C]
  [MonoidalCategory C] [Pretriangulated C]

/-- A tensor triangulated category with functorial cofiber extends `HasFunctorialCofiber`
    with the compatibility isomorphism: cofib(f ▷ W) ≅ cofib(f) ⊗ W.

    Blueprint: prerequisites.tex (tensor–cofiber compatibility). -/
class TensorTriangulatedCatWithFunctorialCofiber extends HasFunctorialCofiber C where
  /-- Tensor with W commutes with functorial cofiber:
      cofib(f ▷ W) ≅ cofib(f) ⊗ W. -/
  tensorCofibIso : ∀ {X Y : C} (f : X ⟶ Y) (W : C),
    cofib (f ▷ W) ≅ cofib f ⊗ W
  /-- Stable 3×3 coherence: the pointwise cofiber of a morphism of exact
      endofunctors has the canonical coherent shift comparison. This is the
      stable enhancement missing from bare functorial choices of cones. -/
  natCofiberFunctorCommShift (F G : Functor C C)
      [F.CommShift ℤ] [G.CommShift ℤ] (τ : NatTrans F G)
      [NatTrans.CommShift τ ℤ] :
    (HasFunctorialCofiber.natCofiberFunctor C τ).CommShift ℤ
  /-- The 3×3 lemma for the selected stable cofiber, including the natural
      comparison of its third vertices. Exactness of the pointwise cofiber is
      derived below from this coherent comparison. -/
  natCofiberFunctorPreservesCofibers (F G : Functor C C)
      [F.CommShift ℤ] [G.CommShift ℤ]
      [F.IsTriangulated] [G.IsTriangulated] (τ : NatTrans F G)
      [NatTrans.CommShift τ ℤ] :
    letI := natCofiberFunctorCommShift F G τ
    PreservesFunctorialCofibers C
      (HasFunctorialCofiber.natCofiberFunctor C τ)

namespace TensorTriangulatedCatWithFunctorialCofiber

variable [TensorTriangulatedCatWithFunctorialCofiber C]

/-- The coherent shift comparison supplied by stable functorial cofibers. -/
noncomputable instance natCofiberFunctor_commShift {F G : Functor C C}
    [F.CommShift ℤ] [G.CommShift ℤ] (τ : NatTrans F G)
    [NatTrans.CommShift τ ℤ] :
    (HasFunctorialCofiber.natCofiberFunctor C τ).CommShift ℤ :=
  natCofiberFunctorCommShift F G τ

/-- Exactness of pointwise cofibers, derived from the stable 3×3 field. -/
noncomputable instance natCofiberFunctor_isTriangulated
    {F G : Functor C C} [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] (τ : NatTrans F G)
    [NatTrans.CommShift τ ℤ] :
    (HasFunctorialCofiber.natCofiberFunctor C τ).IsTriangulated where
  map_distinguished := by
    intro T hT
    let H := HasFunctorialCofiber.natCofiberFunctor C τ
    let D := natCofiberFunctorPreservesCofibers F G τ
    let K := Triangle.mk T.mor₁ (HasFunctorialCofiber.cofibι T.mor₁)
      (HasFunctorialCofiber.cofibδ T.mor₁)
    have hK : K ∈ distTriang C :=
      HasFunctorialCofiber.cofib_distinguished T.mor₁
    have hHK : H.mapTriangle.obj K ∈ distTriang C :=
      isomorphic_distinguished _
        (HasFunctorialCofiber.cofib_distinguished (H.map T.mor₁)) _
        (D.triangleIso T.mor₁)
    let e : T ≅ K := isoTriangleOfIso₁₂ T K hT hK
      (Iso.refl _) (Iso.refl _) (by
        change T.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ T.mor₁
        rw [Category.comp_id, Category.id_comp])
    change H.mapTriangle.obj T ∈ distTriang C
    exact isomorphic_distinguished _ hHK _ (H.mapTriangle.mapIso e)

end TensorTriangulatedCatWithFunctorialCofiber

end TensorFunctorialCofiber

/-! ## Closed Symmetric Tensor Triangulated Category -/

/-- A closed symmetric tensor triangulated category
    (prereq:def:closed-symmetric-tensor-triangulated).
    A triangulated category with a closed symmetric monoidal structure
    compatible with the triangulation, following HPS Def A.2.1. -/
class ClosedSymmetricTensorTriangulated (C : Type u)
    [Category.{v} C] [Preadditive C] [HasShift C ℤ]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Limits.HasZeroObject C]
    [MonoidalCategory C] [Pretriangulated C] where
  /-- The monoidal structure is symmetric. -/
  symmetricCategory : SymmetricCategory C
  /-- The symmetric monoidal structure is closed (internal hom exists). -/
  monoidalClosed : MonoidalClosed C
  /-- (1) Smash preserves suspensions: `Σ X ∧ Y ≃ Σ(X ∧ Y)`, compatible with
      unit and associativity isomorphisms. -/
  smashSuspIso : ∀ (X Y : C),
    (shiftFunctor C (1 : ℤ)).obj X ⊗ Y ≅ (shiftFunctor C (1 : ℤ)).obj (X ⊗ Y)
  /-- (2) Smash is exact: if `X → Y → Z → Σ X` is distinguished,
      then `X ∧ W → Y ∧ W → Z ∧ W → Σ(X ∧ W)` is distinguished. -/
  smashExact : ∀ (W : C) [_inst : (tensorRight W).CommShift ℤ]
    (T : Triangle C), T ∈ distTriang C →
    (tensorRight W).mapTriangle.obj T ∈ distTriang C
  /-- (3) The internal hom `F(W, -)` is exact in the second variable. -/
  ihomExact : ∀ (W : C),
    letI : MonoidalClosed C := monoidalClosed
    [_inst : (ihom W).CommShift ℤ] →
    (T : Triangle C) → T ∈ distTriang C →
    (ihom W).mapTriangle.obj T ∈ distTriang C

attribute [instance] ClosedSymmetricTensorTriangulated.symmetricCategory
attribute [instance] ClosedSymmetricTensorTriangulated.monoidalClosed

end KIPBase.StableHomotopy
