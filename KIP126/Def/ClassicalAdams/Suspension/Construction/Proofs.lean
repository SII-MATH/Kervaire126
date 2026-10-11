module

public import KIP126.Def.ClassicalAdams.Suspension.Construction.Data
public import KIP126.Def.ClassicalAdams.Tower.Proofs

@[expose] public section


/-! All tower transitions and both cofiber squares, including the negative
connecting square, for the constructed suspension comparison. -/

namespace KIP126.Classical.Adams.Suspension.Construction

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

set_option backward.isDefEq.respectTransparency false

theorem cofiberIso_inclusion {A B A' B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B')
    (eA : A' ≅ A⟦(1 : ℤ)⟧) (eB : B' ≅ B⟦(1 : ℤ)⟧)
    (hcomm : f' ≫ eB.hom = eA.hom ≫ f⟦(1 : ℤ)⟧') :
    HasFunctorialCofiber.cofibι f' ≫ (cofiberIso f f' eA eB hcomm).hom =
      eB.hom ≫ (HasFunctorialCofiber.cofibι f)⟦(1 : ℤ)⟧' := by
  have h := (cofiberTriangleIso f f' eA eB hcomm).hom.comm₂
  change HasFunctorialCofiber.cofibι f' ≫
    (cofiberTriangleIso f f' eA eB hcomm).hom.hom₃ = _
  change HasFunctorialCofiber.cofibι f' ≫
    (cofiberTriangleIso f f' eA eB hcomm).hom.hom₃ =
    (cofiberTriangleIso f f' eA eB hcomm).hom.hom₂ ≫
      (HasFunctorialCofiber.cofibι f)⟦(1 : ℤ)⟧' at h
  simpa only [cofiberTriangleIso, isoTriangleOfIso₁₂_hom_hom₂] using h

theorem cofiberIso_connecting {A B A' B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B')
    (eA : A' ≅ A⟦(1 : ℤ)⟧) (eB : B' ≅ B⟦(1 : ℤ)⟧)
    (hcomm : f' ≫ eB.hom = eA.hom ≫ f⟦(1 : ℤ)⟧') :
    (cofiberIso f f' eA eB hcomm).hom ≫
        (HasFunctorialCofiber.cofibδ f)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorComm C (1 : ℤ) (1 : ℤ)).hom.app A =
      -(HasFunctorialCofiber.cofibδ f' ≫ eA.hom⟦(1 : ℤ)⟧') := by
  have h := (cofiberTriangleIso f f' eA eB hcomm).hom.comm₃
  simp only [cofiberTriangleIso, isoTriangleOfIso₁₂_hom_hom₁] at h
  change HasFunctorialCofiber.cofibδ f' ≫ eA.hom⟦(1 : ℤ)⟧' =
    (cofiberIso f f' eA eB hcomm).hom ≫
      ((1 : ℤ).negOnePow • (HasFunctorialCofiber.cofibδ f)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorComm C (1 : ℤ) (1 : ℤ)).hom.app A) at h
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul,
    Preadditive.comp_neg] at h
  exact (neg_eq_iff_eq_neg.mpr h).symm

variable (H : Mod2EilenbergMacLane (C := C))
  [(tensorLeft H.HF2).CommShift ℤ] [(mod2UnitNatTrans H).CommShift ℤ]

@[simp] theorem fiberTriangleIso_hom₂ {Y Z : C} (e : Y ≅ Z⟦(1 : ℤ)⟧) :
    (fiberTriangleIso H e).hom.hom₂ = -e.hom := by
  simp [fiberTriangleIso, invRotate, adamsFiberTriangle, Triangle.invRotate,
    Triangle.mk]
  change e.hom ≫ 𝟙 (Z⟦(1 : ℤ)⟧) = e.hom
  simp only [Category.comp_id]

/-- The positive inclusion square needed for the recursion of tower maps. -/
theorem fiberIso_hom_ι {Y Z : C} (e : Y ≅ Z⟦(1 : ℤ)⟧) :
    (fiberIso H e).hom ≫ (fiberι (adamsUnit H.unit Z))⟦(1 : ℤ)⟧' =
      fiberι (adamsUnit H.unit Y) ≫ e.hom := by
  have h := (fiberTriangleIso H e).hom.comm₁
  rw [fiberTriangleIso_hom₂, adamsFiberTriangle_mor₁] at h
  change (-fiberι (adamsUnit H.unit Y)) ≫ (-e.hom) =
    (fiberIso H e).hom ≫ ((1 : ℤ).negOnePow •
      (adamsFiberTriangle (adamsUnit H.unit Z)).mor₁⟦(1 : ℤ)⟧') at h
  rw [adamsFiberTriangle_mor₁] at h
  simpa only [Int.negOnePow_one, Units.neg_smul, one_smul, Functor.map_neg,
    neg_neg, Preadditive.neg_comp, Preadditive.comp_neg] using h.symm

theorem towerIso_step (X : C) (s : ℕ) :
    (towerIso H X (s + 1)).hom ≫ (adamsTowerStep H.unit X s)⟦(1 : ℤ)⟧' =
      adamsTowerStep H.unit (X⟦(1 : ℤ)⟧) s ≫ (towerIso H X s).hom :=
  fiberIso_hom_ι H (towerIso H X s)

theorem towerIso_map (X : C) (s t : ℕ) (hst : s ≤ t) :
    (towerIso H X t).hom ≫ (adamsTowerMap H.unit X s t hst)⟦(1 : ℤ)⟧' =
      adamsTowerMap H.unit (X⟦(1 : ℤ)⟧) s t hst ≫ (towerIso H X s).hom := by
  induction t, hst using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    rw [adamsTowerMap_succ H.unit X s t ht,
      adamsTowerMap_succ H.unit (X⟦(1 : ℤ)⟧) s t ht,
      Functor.map_comp, ← Category.assoc, towerIso_step H,
      Category.assoc, ih, ← Category.assoc]

theorem towerIso_mapAt (X : C) (s t : ℤ) (hst : s ≤ t) :
    (towerIso H X t.toNat).hom ≫ (adamsTowerMapAt H.unit X s t hst)⟦(1 : ℤ)⟧' =
      adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s t hst ≫ (towerIso H X s.toNat).hom :=
  towerIso_map H X s.toNat t.toNat (by omega)
end
end KIP126.Classical.Adams.Suspension.Construction
