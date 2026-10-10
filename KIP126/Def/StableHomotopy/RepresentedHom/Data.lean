import KIP126.Def.StableHomotopy.Context.Data
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Shifted morphisms represented by an arbitrary object

These are the actual groups `Hom(P[n], Y)`, with their postcomposition and
cofiber connecting maps.  The representing object is explicit; no sphere,
monoidal compatibility, or separately chosen homological functor is required.
-/

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Morphisms into `Y` represented by the `n`-fold shift of `P`. -/
abbrev ShiftedHom (P : C) (n : ℤ) (Y : C) : Type v := P⟦n⟧ ⟶ Y

/-- Postcomposition on the actual represented morphism groups. -/
def postcomposeHom (P : C) (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    ShiftedHom P n X →+ ShiftedHom P n Y where
  toFun := fun x => x ≫ f
  map_zero' := Limits.zero_comp
  map_add' := fun a b => Preadditive.add_comp _ _ _ a b f

/-- The integer-linear form of the postcomposition map. -/
def postcomposeLinearMap (P : C) (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    ShiftedHom P n X →ₗ[ℤ] ShiftedHom P n Y :=
  (postcomposeHom P n f).toIntLinearMap

/-- The connecting map of a chosen distinguished cofiber triangle, represented
by `P`.  It is the actual boundary `z ≫ T.h`, shifted by `-1` and transported
using the specified coherence isomorphisms for the shift functors. -/
noncomputable def connectingHom (P : C) (T : HoCofiberSequence (C := C)) (n : ℤ) :
    ShiftedHom P n T.Z →+ ShiftedHom P (n - 1) T.X where
  toFun z :=
    (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app P ≫
      eqToHom (show (shiftFunctor C n ⋙ shiftFunctor C (-1)).obj P =
        (shiftFunctor C (-1)).obj ((shiftFunctor C n).obj P) by
          simp only [Functor.comp_obj]) ≫
      (shiftFunctor C (-1)).map (z ≫ T.h) ≫
        eqToHom (show (shiftFunctor C (-1)).obj ((shiftFunctor C (1 : ℤ)).obj T.X) =
          (shiftFunctor C (1 : ℤ) ⋙ shiftFunctor C (-1)).obj T.X by
            simp only [Functor.comp_obj]) ≫
        (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app T.X ≫
          eqToHom (Functor.id_obj T.X)
  map_zero' := by
    simp only [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  map_add' := by
    intro a b
    rw [Preadditive.add_comp]
    simp only [Functor.map_add]
    rw [Preadditive.add_comp]
    rw [Preadditive.comp_add]
    rw [Preadditive.comp_add]

/-- The integer-linear form of the represented connecting map. -/
noncomputable def connectingLinearMap
    (P : C) (T : HoCofiberSequence (C := C)) (n : ℤ) :
    ShiftedHom P n T.Z →ₗ[ℤ] ShiftedHom P (n - 1) T.X :=
  (connectingHom P T n).toIntLinearMap

end KIP126.StableHomotopy
