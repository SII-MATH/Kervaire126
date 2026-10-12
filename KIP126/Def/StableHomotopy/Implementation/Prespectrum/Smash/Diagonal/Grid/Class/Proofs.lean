module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Class.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
set_option backward.isDefEq.respectTransparency false
variable {X Y : Prespectrum.{0}} {d : ℤ}

/-- The alternating orientations make the actual class transitions
commute strictly; this is a consequence of the constructed square homotopy. -/
theorem DiagonalGridClass.horizontal_vertical_commute :
    Function.Commute (@DiagonalGridClass.horizontal X Y d) DiagonalGridClass.vertical := by
  intro a
  rcases a with ⟨n,k,r,h,q⟩
  unfold DiagonalGridClass.horizontal DiagonalGridClass.vertical
  congr 1
  induction q using Quotient.inductionOn with
  | h p => exact Quotient.sound (diagonalGridLoop_interchange_homotopic X Y n k r p).symm

@[simp] theorem DiagonalGridClass.horizontal_iterate_left (a : DiagonalGridClass X Y d) (m : ℕ) :
    ((DiagonalGridClass.horizontal^[m]) a).left = a.left+m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      change ((DiagonalGridClass.horizontal^[m]) a).left+1 = _
      rw [ih]
      omega

@[simp] theorem DiagonalGridClass.horizontal_iterate_right (a : DiagonalGridClass X Y d) (m : ℕ) :
    ((DiagonalGridClass.horizontal^[m]) a).right = a.right := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ih

@[simp] theorem DiagonalGridClass.vertical_iterate_left (a : DiagonalGridClass X Y d) (m : ℕ) :
    ((DiagonalGridClass.vertical^[m]) a).left = a.left := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ih

@[simp] theorem DiagonalGridClass.vertical_iterate_right (a : DiagonalGridClass X Y d) (m : ℕ) :
    ((DiagonalGridClass.vertical^[m]) a).right = a.right+m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      change ((DiagonalGridClass.vertical^[m]) a).right+1 = _
      rw [ih]
      omega

@[simp] theorem DiagonalGridClass.normalize_left (a : DiagonalGridClass X Y d) :
    a.normalize.left = a.left+a.right := by
  simp [DiagonalGridClass.normalize]

@[simp] theorem DiagonalGridClass.normalize_right (a : DiagonalGridClass X Y d) :
    a.normalize.right = a.left+a.right := by
  simp [DiagonalGridClass.normalize,Nat.add_comm]

/-- Advancing either independent grid direction advances the normalized
diagonal class by exactly one pair of actual bonds. -/
theorem DiagonalGridClass.normalize_horizontal (a : DiagonalGridClass X Y d) :
    a.horizontal.normalize = a.normalize.horizontal.vertical := by
  let H := @DiagonalGridClass.horizontal X Y d
  let V := @DiagonalGridClass.vertical X Y d
  have h : Function.Commute H V := DiagonalGridClass.horizontal_vertical_commute
  change (H^[a.right]) ((V^[a.left+1]) (H a)) = V (H ((H^[a.right]) ((V^[a.left]) a)))
  rw [← h.iterate_right (a.left+1) a,Function.iterate_succ_apply']
  rw [← Function.iterate_succ_apply,Function.iterate_succ_apply',h.iterate_left a.right]
  exact h _

theorem DiagonalGridClass.normalize_vertical (a : DiagonalGridClass X Y d) :
    a.vertical.normalize = a.normalize.horizontal.vertical := by
  let H := @DiagonalGridClass.horizontal X Y d
  let V := @DiagonalGridClass.vertical X Y d
  have h : Function.Commute H V := DiagonalGridClass.horizontal_vertical_commute
  change (H^[a.right+1]) ((V^[a.left]) (V a)) = V (H ((H^[a.right]) ((V^[a.left]) a)))
  rw [← Function.iterate_succ_apply,Function.iterate_succ_apply']
  rw [Function.iterate_succ_apply' (f := V),h.iterate_left a.right]
  exact h _

end KIP126.StableHomotopy.Implementation.Prespectrum
