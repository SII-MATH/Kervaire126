import KIPBase.Synthetic.GeometricAdamsCofiber
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Ordinary naturality does not imply compatibility with suspension

This is a counterexample to that inference on graded rational vector spaces.
It is not a formal construction of the full synthetic-category countermodel
discussed in `LambdaExactnessGap.md`.
-/

namespace KIPBase.Synthetic.LambdaShiftCounterexample

open CategoryTheory CategoryTheory.Limits

abbrev Graded := ℤ → ModuleCat ℚ

def suspension : Graded ⥤ Graded where
  obj A j := A (j - 1)
  map f j := f (j - 1)

noncomputable def ordinaryNatural : 𝟭 Graded ⟶ 𝟭 Graded where
  app A j := if j = 0 then 𝟙 (A j) else 0
  naturality := by
    intro A B f
    funext j
    change f j ≫ (if j = 0 then 𝟙 (B j) else 0) =
      (if j = 0 then 𝟙 (A j) else 0) ≫ f j
    split_ifs
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (comp_zero : f j ≫ (0 : B j ⟶ B j) = 0).trans
        (zero_comp : (0 : A j ⟶ A j) ≫ f j = 0).symm

def constant : Graded := fun _ => ModuleCat.of ℚ ℚ

/-- This natural transformation fails to commute with the shift even
on the constant graded vector space, as its degree-one component shows. -/
theorem ordinary_naturality_does_not_imply_shift :
    suspension.map (ordinaryNatural.app constant) ≠
      ordinaryNatural.app (suspension.obj constant) := by
  intro h
  have h1 := congrArg (fun f => (f (1 : ℤ)).hom (1 : ℚ)) h
  change (1 : ℚ) = 0 at h1
  exact one_ne_zero h1

end KIPBase.Synthetic.LambdaShiftCounterexample
