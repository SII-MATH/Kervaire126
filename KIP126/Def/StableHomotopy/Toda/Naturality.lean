import KIP126.Def.StableHomotopy.Toda.Predicates
import Mathlib.CategoryTheory.Triangulated.Functor

/-! Data for the composition-only naturality interface of shifted Toda
relations.  No monoidal or sphere-spectrum structure occurs here. -/
namespace KIP126.StableHomotopy.Toda

open CategoryTheory CategoryTheory.Pretriangulated

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]

section
variable [HasShift C ℤ] [HasShift D ℤ]

/-! `Exact` has the standard triangulated meaning: commuting with the
ℤ-shift and carrying distinguished triangles to distinguished triangles. -/
class Exact (F : C ⥤ D) where
  commutesWithShift : Prop
  mapsDistinguishedTriangles : Prop

/-- A shift-compatible functor datum for the first Toda naturality step. -/
structure TodaFunctorData (F : C ⥤ D) [Exact F] where
  shiftIso : ∀ (X : C), F.obj (X⟦(1 : ℤ)⟧) ≅ F.obj X⟦(1 : ℤ)⟧

end

end KIP126.StableHomotopy.Toda
