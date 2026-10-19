/-
  KIPBase.Synthetic.ShiftCofiber
  Coherence between synthetic bidegree shifts and the chosen functorial cofiber.
-/
import KIPBase.Synthetic.Basic

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

noncomputable section

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The selected functorial cofiber triangle of a morphism. -/
noncomputable abbrev chosenCofiberTriangle {X Y : Syn} (f : X ⟶ Y) : Triangle Syn :=
  Triangle.mk f (syn_functorial_cofiber.cofibι f)
    (syn_functorial_cofiber.cofibδ f)

/-- Coherence required for synthetic bidegree shifts to preserve the selected
functorial cofiber construction.  This is deliberately separate from the
minimal `SyntheticCategory` interface: equivalence and additivity alone do not
determine maps between chosen cones.

Besides commuting with the triangulated suspension, the comparison is required
to respect both structure maps of the cofiber triangle and the chosen map of
cofibers attached to every commutative square. -/
class SyntheticShiftCofiberCompatibility where
  commShift (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := Syn) p).CommShift ℤ
  cofiberTriangleIso (p : ℤ × ℤ) {X Y : Syn} (f : X ⟶ Y) :
    letI := commShift p
    (SyntheticCategory.biShift p).mapTriangle.obj (chosenCofiberTriangle f) ≅
      chosenCofiberTriangle ((SyntheticCategory.biShift p).map f)
  cofiberTriangleIso_hom₁ (p : ℤ × ℤ) {X Y : Syn} (f : X ⟶ Y) :
    letI := commShift p
    (cofiberTriangleIso p f).hom.hom₁ =
      𝟙 ((SyntheticCategory.biShift p).obj X)
  cofiberTriangleIso_hom₂ (p : ℤ × ℤ) {X Y : Syn} (f : X ⟶ Y) :
    letI := commShift p
    (cofiberTriangleIso p f).hom.hom₂ =
      𝟙 ((SyntheticCategory.biShift p).obj Y)
  map_cofibMap (p : ℤ × ℤ)
      {X₁ Y₁ X₂ Y₂ : Syn} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
      (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂) (h : α ≫ f₂ = f₁ ≫ β) :
    (SyntheticCategory.biShift p).map
          (syn_functorial_cofiber.cofibMap f₁ f₂ α β h) ≫
        (cofiberTriangleIso p f₂).hom.hom₃ =
      (cofiberTriangleIso p f₁).hom.hom₃ ≫
        syn_functorial_cofiber.cofibMap
          ((SyntheticCategory.biShift p).map f₁)
          ((SyntheticCategory.biShift p).map f₂)
          ((SyntheticCategory.biShift p).map α)
          ((SyntheticCategory.biShift p).map β)
          (by simpa only [Functor.map_comp] using
            congrArg (SyntheticCategory.biShift p).map h)

namespace SyntheticShiftCofiberCompatibility

variable [SyntheticShiftCofiberCompatibility (Syn := Syn)]

/-- A compatible synthetic bidegree shift commutes coherently with the
triangulated suspension. -/
noncomputable instance biShift_commShift (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := Syn) p).CommShift ℤ :=
  SyntheticShiftCofiberCompatibility.commShift p

/-- The chosen comparison between shifting a cofiber and taking the cofiber
of the shifted map. -/
noncomputable abbrev biShiftCofibIso (p : ℤ × ℤ) {X Y : Syn} (f : X ⟶ Y) :
    (SyntheticCategory.biShift p).obj (syn_functorial_cofiber.cofib f) ≅
      syn_functorial_cofiber.cofib ((SyntheticCategory.biShift p).map f) :=
  Triangle.π₃.mapIso
    (SyntheticShiftCofiberCompatibility.cofiberTriangleIso p f)

/-- The cofiber comparison is compatible with the selected inclusion. -/
theorem biShiftCofibIso_ι (p : ℤ × ℤ) {X Y : Syn} (f : X ⟶ Y) :
    (SyntheticCategory.biShift p).map (syn_functorial_cofiber.cofibι f) ≫
        (biShiftCofibIso p f).hom =
      syn_functorial_cofiber.cofibι ((SyntheticCategory.biShift p).map f) := by
  have h := (SyntheticShiftCofiberCompatibility.cofiberTriangleIso p f).hom.comm₂
  dsimp only [chosenCofiberTriangle, Functor.mapTriangle,
    Triangle.mk_mor₂, Functor.mapIso_hom, Triangle.π₃] at h ⊢
  rw [SyntheticShiftCofiberCompatibility.cofiberTriangleIso_hom₂] at h
  exact h.trans (Category.id_comp _)

/-- The cofiber comparison is compatible with the selected connecting map. -/
theorem biShiftCofibIso_δ (p : ℤ × ℤ) {X Y : Syn} (f : X ⟶ Y) :
    (biShiftCofibIso p f).hom ≫
        syn_functorial_cofiber.cofibδ ((SyntheticCategory.biShift p).map f) =
      (SyntheticCategory.biShift p).map (syn_functorial_cofiber.cofibδ f) ≫
        ((SyntheticCategory.biShift p).commShiftIso (1 : ℤ)).hom.app X := by
  have h := (SyntheticShiftCofiberCompatibility.cofiberTriangleIso p f).hom.comm₃
  dsimp only [chosenCofiberTriangle, Functor.mapTriangle,
    Triangle.mk_mor₃, Triangle.mk_obj₁, Functor.mapIso_hom, Triangle.π₃] at h ⊢
  rw [SyntheticShiftCofiberCompatibility.cofiberTriangleIso_hom₁] at h
  let a := (SyntheticCategory.biShift p).map
      (syn_functorial_cofiber.cofibδ f) ≫
    ((SyntheticCategory.biShift p).commShiftIso (1 : ℤ)).hom.app X
  have hid : (shiftFunctor Syn (1 : ℤ)).map
      (𝟙 ((SyntheticCategory.biShift p).obj X)) = 𝟙 _ :=
    (shiftFunctor Syn (1 : ℤ)).map_id _
  exact h.symm.trans ((congrArg (fun k => a ≫ k) hid).trans (Category.comp_id a))

/-- Preservation of the selected functorial cofibers implies preservation of
all distinguished triangles. -/
noncomputable instance biShift_isTriangulated (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := Syn) p).IsTriangulated where
  map_distinguished T hT := by
    let F := SyntheticCategory.biShift (Syn := Syn) p
    let C : Triangle Syn := chosenCofiberTriangle T.mor₁
    have hC : C ∈ distTriang Syn :=
      syn_functorial_cofiber.cofib_distinguished T.mor₁
    let D : Triangle Syn := chosenCofiberTriangle (F.map T.mor₁)
    have hD : D ∈ distTriang Syn :=
      syn_functorial_cofiber.cofib_distinguished (F.map T.mor₁)
    let e : F.mapTriangle.obj C ≅ D :=
      SyntheticShiftCofiberCompatibility.cofiberTriangleIso p T.mor₁
    have hFC : F.mapTriangle.obj C ∈ distTriang Syn :=
      isomorphic_distinguished D hD _ e
    let eT : T ≅ C := isoTriangleOfIso₁₂ T C hT hC
      (Iso.refl _) (Iso.refl _) (by
        change T.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ T.mor₁
        simp)
    exact isomorphic_distinguished _ hFC _ (F.mapTriangle.mapIso eT)

end SyntheticShiftCofiberCompatibility

end

end KIPBase.Synthetic
