import KIPBase.Synthetic.GeometricAdamsRealization
import KIPBase.Synthetic.ShiftCofiber

/-!
# Stable quotient coherence and object-level Adams realization

Coherent preservation of cofibers by the actual finite λ quotient is derived
from stable λ and stable 3×3 data.  Removal of a deeper-filtration error is
then a consequence of the explicit object-level Adams realization interface;
it is not asserted for arbitrary towers.
-/

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIPBase.StableHomotopy

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]

/-- The precise geometric obligation in step 1. Besides preservation of
triangles, the selected comparisons must commute with maps of cofibers.
This is data local to the deferred construction, not a global instance. -/
structure LambdaQuotientCofiberData (n : ℕ) where
  commShift : (XModLambdaN.functor (Syn := Syn) n).CommShift ℤ
  triangleIso {A B : Syn} (f : A ⟶ B) :
    letI := commShift
    (XModLambdaN.functor n).mapTriangle.obj (chosenCofiberTriangle f) ≅
      chosenCofiberTriangle ((XModLambdaN.functor n).map f)
  hom₁ {A B : Syn} (f : A ⟶ B) :
    letI := commShift
    (triangleIso f).hom.hom₁ = 𝟙 (XModLambdaN A n)
  hom₂ {A B : Syn} (f : A ⟶ B) :
    letI := commShift
    (triangleIso f).hom.hom₂ = 𝟙 (XModLambdaN B n)
  naturality {A B A' B' : Syn} (f : A ⟶ B) (g : A' ⟶ B')
      (a : A ⟶ A') (b : B ⟶ B') (h : a ≫ g = f ≫ b) :
    (XModLambdaN.functor n).map
        (syn_functorial_cofiber.cofibMap f g a b h) ≫
        (triangleIso g).hom.hom₃ =
      (triangleIso f).hom.hom₃ ≫
        syn_functorial_cofiber.cofibMap
          ((XModLambdaN.functor n).map f) ((XModLambdaN.functor n).map g)
          ((XModLambdaN.functor n).map a) ((XModLambdaN.functor n).map b)
          (by simpa only [Functor.map_comp] using
            congrArg (XModLambdaN.functor n).map h)

namespace GeometricAdams.Deferred

variable [SyntheticShiftCofiberCompatibility (Syn := Syn)]
    [SyntheticStableLambdaCompatibility (Syn := Syn)]

/-- The coherent selected-cofiber comparison for the finite lambda quotient,
obtained by specializing the stable 3×3 structure to `lambdaPowNatTrans`. -/
noncomputable def quotientCofiberData (n : ℕ) :
    LambdaQuotientCofiberData (Syn := Syn) n := by
  letI : TensorTriangulatedCatWithFunctorialCofiber Syn :=
    syn_functorial_cofiber
  letI : (XModLambdaN.functor (Syn := Syn) n).CommShift ℤ :=
    XModLambdaN.functor_commShift n
  let D :=
    TensorTriangulatedCatWithFunctorialCofiber.natCofiberFunctorPreservesCofibers
      (SyntheticCategory.biShift (0, -(n : ℤ))) (Functor.id Syn)
      (lambdaPowNatTrans (Syn := Syn) n)
  exact
    { commShift := inferInstance
      triangleIso := fun f => D.triangleIso f
      hom₁ := fun f => D.hom₁ f
      hom₂ := fun f => D.hom₂ f
      naturality := fun f g a b h => D.naturality f g a b h }

omit [SyntheticShiftCofiberCompatibility (Syn := Syn)]
    [SyntheticStableLambdaCompatibility (Syn := Syn)] in
/-- At the generator weight, the object-level Adams realization constructs a
divided stage target and corrects the relative representative. The target
keeps its specified adjacent-layer value. The statement stops at an equality
of actual morphisms; it contains no ESS conclusion.

The λ exponent is the differential length minus one. All filtration
indices are those of the supplied tower, with no boundedness assumption. -/
theorem correctedBoundary {X : Syn} (G : GeometricAdams.Input X)
    (R : G.FreeLayers) (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ)
    (x : G.PageGroup (Smn m (m + s)) s r (by omega))
    (y : Smn m (m + s) ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).obj (G.layer (s + r))))
    (hxy : G.pageObstruction (Smn m (m + s)) s r (by omega) x =
      QuotientAddGroup.mk
        (y ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (r - 1) (G.layer (s + r))))) :
    ∃ (z : G.Representative (Smn m (m + s)) s r)
      (y' : Smn m (m + s) ⟶ (G.boundaryTarget (r - 1)).stage (s + r)),
      QuotientAddGroup.mk
        (⟨G.source (Smn m (m + s)) s r (by omega) z,
          ⟨z, rfl⟩⟩ : G.sourceCycles (Smn m (m + s)) s r (by omega)) = x ∧
      y' ≫ (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).map
            (syn_functorial_cofiber.cofibι
              (G.transition (s + r) (s + r + 1) (Nat.le_succ _)))) = y ∧
      z ≫ G.boundary s (s + r) (Nat.le_add_right s r) =
        y' ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (r - 1) (G.stage (s + r))) :=
  A.dividedBoundary s r hr m x y hxy

end GeometricAdams.Deferred

namespace LambdaQuotientCofiberData

/-- Preservation of all distinguished triangles is proved from the
specified comparisons of the selected cofiber triangles. -/
theorem isTriangulated {n : ℕ} (D : LambdaQuotientCofiberData (Syn := Syn) n) :
    letI := D.commShift
    (XModLambdaN.functor (Syn := Syn) n).IsTriangulated := by
  letI := D.commShift
  refine ⟨?_⟩
  intro T hT
  let F := XModLambdaN.functor (Syn := Syn) n
  let C := chosenCofiberTriangle T.mor₁
  have hC : C ∈ distTriang Syn := syn_functorial_cofiber.cofib_distinguished T.mor₁
  have hFC : F.mapTriangle.obj C ∈ distTriang Syn :=
    isomorphic_distinguished _
      (syn_functorial_cofiber.cofib_distinguished (F.map T.mor₁)) _
      (D.triangleIso T.mor₁)
  let e : T ≅ C := isoTriangleOfIso₁₂ T C hT hC
    (Iso.refl _) (Iso.refl _) (by
      change T.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ T.mor₁
      rw [Category.comp_id, Category.id_comp])
  exact isomorphic_distinguished _ hFC _ (F.mapTriangle.mapIso e)

/-- The actual layer of the quotient tower, compared using the coherent
choice in step 1. -/
noncomputable def layerIso {n : ℕ} (D : LambdaQuotientCofiberData (Syn := Syn) n)
    {X : Syn} (G : GeometricAdams.Input X) (s : ℕ) :
    (G.quotient n).layer s ≅ XModLambdaN (G.layer s) n :=
  (Triangle.π₃.mapIso
    (D.triangleIso (G.transition s (s + 1) (Nat.le_succ s)))).symm

/-- The deferred geometric step now gives the finite-quotient layer
calculation, with no additional comparison premise. -/
noncomputable def layerHomEquiv {n : ℕ}
    (D : LambdaQuotientCofiberData (Syn := Syn) n)
    {X : Syn} (G : GeometricAdams.Input X) (R : G.FreeLayers)
    (s : ℕ) (m w : ℤ) :
    (Smn m w ⟶ (G.quotient n).layer s) ≃+
      TruncatedLambdaE2.component ((R s).generator m) (m + (s : ℤ)) w n :=
  (AddEquiv.ofBijective (GeometricAdams.Input.postcompose (Smn m w)
    (D.layerIso G s).hom) ⟨by
      intro a b h
      exact (cancel_mono (D.layerIso G s).hom).mp h, by
      intro a
      refine ⟨a ≫ (D.layerIso G s).inv, ?_⟩
      change (a ≫ (D.layerIso G s).inv) ≫ (D.layerIso G s).hom = a
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩).trans
    (G.layerCofiberHomEquiv R s m w n)

end LambdaQuotientCofiberData

namespace GeometricAdams.Deferred

variable [SyntheticShiftCofiberCompatibility (Syn := Syn)]
    [SyntheticStableLambdaCompatibility (Syn := Syn)]

/-- The actual quotient-layer comparison supplied by stable synthetic lambda
and the coherent selected-cofiber 3×3 structure. -/
noncomputable def quotientLayerIso {X : Syn} (G : GeometricAdams.Input X)
    (n s : ℕ) : (G.quotient n).layer s ≅ XModLambdaN (G.layer s) n :=
  (quotientCofiberData (Syn := Syn) n).layerIso G s

/-- The free-layer calculation is now attached to the actual quotient
filtration. Its only deferred dependency is step 1. -/
noncomputable def quotientLayerHomEquiv {X : Syn} (G : GeometricAdams.Input X)
  (R : G.FreeLayers) (n s : ℕ) (m w : ℤ) :
    (Smn m w ⟶ (G.quotient n).layer s) ≃+
      TruncatedLambdaE2.component ((R s).generator m) (m + (s : ℤ)) w n :=
  (quotientCofiberData (Syn := Syn) n).layerHomEquiv G R s m w

end GeometricAdams.Deferred

end KIPBase.Synthetic
