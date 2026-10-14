module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Integer.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Foundation

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem sourceIntegerShiftFunctor_nat (n : ℕ) :
    sourceIntegerShiftFunctor.{u} (n : ℤ) = functorIterate sourceSuspensionFunctor n := rfl

@[simp] theorem sourceIntegerShiftFunctor_neg_nat (n : ℕ) :
    sourceIntegerShiftFunctor.{u} (-(n : ℤ)) = functorIterate sourceDesuspensionFunctor n := by
  cases n <;> rfl

@[simp] theorem sourceIntegerShiftFunctor_one :
    sourceIntegerShiftFunctor.{u} 1 = sourceSuspensionFunctor := rfl

@[simp] theorem sourceIntegerShiftFunctor_neg_one :
    sourceIntegerShiftFunctor.{u} (-1) = sourceDesuspensionFunctor := rfl

/-- All nonnegative addition comparisons are strict functor equalities. -/
theorem sourceIntegerShiftFunctor_add_nat (m n : ℕ) :
    sourceIntegerShiftFunctor.{u} ((m : ℤ) + n) =
      sourceIntegerShiftFunctor (m : ℤ) ⋙ sourceIntegerShiftFunctor (n : ℤ) := by
  rw [← Int.natCast_add, sourceIntegerShiftFunctor_nat,
    sourceIntegerShiftFunctor_nat, sourceIntegerShiftFunctor_nat]
  exact functorIterate_add _ m n

/-- All nonpositive addition comparisons are strict functor equalities. -/
theorem sourceIntegerShiftFunctor_add_neg_nat (m n : ℕ) :
    sourceIntegerShiftFunctor.{u} (-(m : ℤ) + -(n : ℤ)) =
      sourceIntegerShiftFunctor (-(m : ℤ)) ⋙ sourceIntegerShiftFunctor (-(n : ℤ)) := by
  rw [← neg_add, ← Int.natCast_add, sourceIntegerShiftFunctor_neg_nat,
    sourceIntegerShiftFunctor_neg_nat, sourceIntegerShiftFunctor_neg_nat]
  exact functorIterate_add _ m n

theorem sourceSuspensionIterate_obj (n : ℕ) (X : Prespectrum.{u}) :
    (functorIterate sourceSuspensionFunctor n).obj (sourceLocalization.obj X) =
      sourceLocalization.obj ((suspension^[n]) X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sourceSuspensionFunctor.obj
      ((functorIterate sourceSuspensionFunctor n).obj (sourceLocalization.obj X)) = _
    rw [ih, Function.iterate_succ_apply']
    rfl

theorem sourceDesuspensionIterate_obj (n : ℕ) (X : Prespectrum.{u}) :
    (functorIterate sourceDesuspensionFunctor n).obj (sourceLocalization.obj X) =
      sourceLocalization.obj ((desuspension^[n]) X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sourceDesuspensionFunctor.obj
      ((functorIterate sourceDesuspensionFunctor n).obj (sourceLocalization.obj X)) = _
    rw [ih, Function.iterate_succ_apply']
    rfl

/-- Every member of the signed functor family has exactly the original
point-set integer shift as its value, for every actual prespectrum. -/
theorem sourceIntegerShiftFunctor_obj (d : ℤ) (X : Prespectrum.{u}) :
    (sourceIntegerShiftFunctor d).obj (sourceLocalization.obj X) =
      sourceLocalization.obj (if 0 ≤ d then (suspension^[d.toNat]) X
        else (desuspension^[(-d).toNat]) X) := by
  cases d with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, sourceIntegerShiftFunctor_nat, Int.natCast_nonneg,
      if_true, Int.toNat_natCast] using sourceSuspensionIterate_obj n X
  | negSucc n =>
    simpa only [sourceIntegerShiftFunctor, Int.negSucc_not_nonneg, if_false,
      Int.neg_negSucc, Int.toNat_natCast] using sourceDesuspensionIterate_obj (n + 1) X

/-- The specified forward and backward steps recover the actual
equivalence unit on every signed iterate. -/
theorem sourceIntegerUndoSuccessorIso_hom_comp (d : ℤ) (X : SourceCategory.{u}) :
    (sourceIntegerUndoSuccessorIso d).hom.app X ≫
      sourceDesuspensionFunctor.map ((sourceIntegerSuccessorIso d).hom.app X) =
        sourceSuspensionEquivalence.unitIso.hom.app ((sourceIntegerShiftFunctor d).obj X) := by
  change (sourceSuspensionEquivalence.unitIso.hom.app ((sourceIntegerShiftFunctor d).obj X) ≫
    sourceDesuspensionFunctor.map ((sourceIntegerSuccessorIso d).inv.app X)) ≫ _ = _
  erw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

@[simp] theorem sourceIntegerSuccessorIso_neg_one :
    sourceIntegerSuccessorIso.{u} (-1) = sourceSuspensionEquivalence.counitIso.symm := rfl

@[simp] theorem sourceIntegerUndoSuccessorIso_zero :
    sourceIntegerUndoSuccessorIso.{u} 0 = sourceSuspensionEquivalence.unitIso := by
  ext X
  change sourceSuspensionEquivalence.unitIso.hom.app X ≫
    sourceDesuspensionFunctor.map (𝟙 _) = sourceSuspensionEquivalence.unitIso.hom.app X
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The mixed-step overlap on suspension satisfies the actual triangle identity. -/
theorem sourceIntegerSuspensionTriangle (X : SourceCategory.{u}) :
    sourceSuspensionFunctor.map ((sourceIntegerUndoSuccessorIso 0).hom.app X) ≫
      (sourceIntegerSuccessorIso (-1)).inv.app (sourceSuspensionFunctor.obj X) =
        𝟙 (sourceSuspensionFunctor.obj X) := by
  rw [sourceIntegerUndoSuccessorIso_zero, sourceIntegerSuccessorIso_neg_one]
  exact sourceSuspensionEquivalence.functor_unitIso_comp X

/-- The mixed-step overlap on desuspension satisfies the other triangle identity. -/
theorem sourceIntegerDesuspensionTriangle (X : SourceCategory.{u}) :
    (sourceIntegerUndoSuccessorIso 0).hom.app (sourceDesuspensionFunctor.obj X) ≫
      sourceDesuspensionFunctor.map ((sourceIntegerSuccessorIso (-1)).inv.app X) =
        𝟙 (sourceDesuspensionFunctor.obj X) := by
  rw [sourceIntegerUndoSuccessorIso_zero, sourceIntegerSuccessorIso_neg_one]
  exact sourceSuspensionEquivalence.unit_inverse_comp X

end KIP126.StableHomotopy.Implementation.Prespectrum
