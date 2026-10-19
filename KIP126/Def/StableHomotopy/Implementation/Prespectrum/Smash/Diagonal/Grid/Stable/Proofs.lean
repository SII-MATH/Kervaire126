module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Stable.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
set_option backward.isDefEq.respectTransparency false
variable {X Y : Prespectrum.{0}} {d : ℤ}

@[simp] theorem DiagonalGridClass.toDiagonal_horizontal (a : DiagonalGridClass X Y d) :
    a.horizontal.toDiagonal = a.toDiagonal.next :=
  Subtype.ext a.normalize_horizontal

@[simp] theorem DiagonalGridClass.toDiagonal_vertical (a : DiagonalGridClass X Y d) :
    a.vertical.toDiagonal = a.toDiagonal.next :=
  Subtype.ext a.normalize_vertical

/-- Equal-stage normalization is a finite number of actual diagonal
steps, rather than a new equivalence assumption. -/
theorem DiagonalGridDiagonalClass.toDiagonal_eq_iterate (a : DiagonalGridDiagonalClass X Y d) :
    a.val.toDiagonal = (DiagonalGridDiagonalClass.next^[a.val.left]) a := by
  apply Subtype.ext
  have hi (m : ℕ) : ((DiagonalGridDiagonalClass.next^[m]) a).val =
      ((DiagonalGridClass.vertical ∘ DiagonalGridClass.horizontal)^[m]) a.val := by
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
        exact congrArg (DiagonalGridClass.vertical ∘ DiagonalGridClass.horizontal) ih
  rw [hi,(DiagonalGridClass.horizontal_vertical_commute.symm).comp_iterate]
  change (DiagonalGridClass.horizontal^[a.val.right])
      ((DiagonalGridClass.vertical^[a.val.left]) a.val) =
    (DiagonalGridClass.vertical^[a.val.left])
      ((DiagonalGridClass.horizontal^[a.val.left]) a.val)
  rw [← a.property]
  exact DiagonalGridClass.horizontal_vertical_commute.iterate_iterate _ _ _

theorem DiagonalGridClass.stable_eq_horizontal_iterate (a : DiagonalGridClass X Y d) (m : ℕ) :
    (Quot.mk _ a : DiagonalGridStable X Y d) =
      Quot.mk _ ((DiagonalGridClass.horizontal^[m]) a) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (Quot.sound (DiagonalGridRelation.horizontal _))

theorem DiagonalGridClass.stable_eq_vertical_iterate (a : DiagonalGridClass X Y d) (m : ℕ) :
    (Quot.mk _ a : DiagonalGridStable X Y d) =
      Quot.mk _ ((DiagonalGridClass.vertical^[m]) a) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (Quot.sound (DiagonalGridRelation.vertical _))

theorem DiagonalGridClass.stable_eq_normalize (a : DiagonalGridClass X Y d) :
    (Quot.mk _ a : DiagonalGridStable X Y d) = Quot.mk _ a.normalize :=
  (a.stable_eq_vertical_iterate a.left).trans
    (((DiagonalGridClass.vertical^[a.left]) a).stable_eq_horizontal_iterate a.right)

theorem DiagonalGridDiagonalClass.stable_eq_iterate (a : DiagonalGridDiagonalClass X Y d) (m : ℕ) :
    (Quot.mk _ a : DiagonalGridDiagonalStable X Y d) =
      Quot.mk _ ((DiagonalGridDiagonalClass.next^[m]) a) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (Quot.sound (DiagonalGridDiagonalRelation.step _))

end KIP126.StableHomotopy.Implementation.Prespectrum
