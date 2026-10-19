module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

set_option backward.isDefEq.respectTransparency false

/-- Desuspension transports represented injectivity to the shifted target map. -/
theorem postcomp_shift_injective_of_desuspension {X Y U : C} (f : X ⟶ Y)
    (hi : Function.Injective (fun a : U⟦(-1 : ℤ)⟧ ⟶ X => a ≫ f)) :
    Function.Injective (fun a : U ⟶ X⟦(1 : ℤ)⟧ => a ≫ f⟦(1 : ℤ)⟧') := by
  let F := shiftFunctor C (-1 : ℤ)
  let e := shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)
  have hn : F.map (f⟦(1 : ℤ)⟧') ≫ e.hom.app Y = e.hom.app X ≫ f :=
    e.hom.naturality f
  intro a b hab
  apply F.map_injective
  apply (cancel_mono (e.hom.app X)).mp
  apply hi
  have h := congrArg (fun q => F.map q ≫ e.hom.app Y) hab
  simpa only [Functor.map_comp, Category.assoc, hn] using h

/-- Two consecutive represented conditions force vanishing on the third
vertex of the specified distinguished triangle. -/
theorem hom_triangle_third_subsingleton_of_postcomp (T : Triangle C)
    (hT : T ∈ distTriang C) (U : C)
    (hs : Function.Surjective (fun a : U ⟶ T.obj₁ => a ≫ T.mor₁))
    (hi : Function.Injective (fun a : U⟦(-1 : ℤ)⟧ ⟶ T.obj₁ => a ≫ T.mor₁)) :
    Subsingleton (U ⟶ T.obj₃) := by
  have hz (z : U ⟶ T.obj₃) : z = 0 := by
    have hb : z ≫ T.mor₃ = 0 := by
      apply postcomp_shift_injective_of_desuspension T.mor₁ hi
      change (z ≫ T.mor₃) ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 ≫ T.mor₁⟦(1 : ℤ)⟧'
      rw [Category.assoc, comp_distTriang_mor_zero₃₁ T hT, comp_zero, zero_comp]
    obtain ⟨y, hy⟩ := T.coyoneda_exact₃ hT z hb
    obtain ⟨x, hx⟩ := hs y
    rw [hy, ← hx, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end KIP126.Foundation
