import KIP126.Def.Steenrod.MilnorModule.Resolution.Data
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
The right-comodule/left-module Ext comparison is constrained on every
resolution cocycle by the actual transpose-conjugation map. Its target
resolution is the prescribed dual of the same source resolution. Internal
degree is unchanged, while the two Ext arguments are reversed.
-/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory KIP126.Core.Algebra

/-- Every cocycle is sent to its actual dual representative. The existential
proof only certifies that this fixed representative is a cocycle; it does not
choose another representative, resolution, or operation. -/
def PreservesDualCobarRepresentatives (R : Ext.CobarResolution)
    (e : ∀ (s : ℕ) (t : ℤ), Ext.SphereExt s t ≃ₗ[F2] SphereExt s t) : Prop :=
  ∀ (s : ℕ) (t : ℤ)
    (f : Ext.trivialAt t ⟶ R.resolution.cocomplex.X s)
    (hf : f ≫ R.resolution.cocomplex.d s (s + 1) = 0),
    ∃ hf' : (dualCobarResolution R).complex.d (s + 1) s ≫
        (dualLeftMap f ≫ (trivialDualIso t).hom) = 0,
      e s t (R.resolution.extMk f (s + 1) rfl hf) =
        (dualCobarResolution R).extMk
          (dualLeftMap f ≫ (trivialDualIso t).hom) (s + 1) rfl hf'

end KIP126.Steenrod.Milnor.Module
