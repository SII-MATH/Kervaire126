module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Cocone.Data
public import KIP126.Def.Algebra.DirectSequence.Coproduct.Proofs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

universe u v

set_option backward.isDefEq.respectTransparency false

/-- The actual Milnor map has the prescribed adjacent-difference coordinates. -/
@[reassoc]
theorem sourceSequentialOneSubShift_inclusion (F : ℕ ⥤ SourceCategory.{u}) (n : ℕ) :
    Sigma.ι F.obj n ≫ sourceSequentialOneSubShift F =
      Sigma.ι F.obj n - F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n+1) := by
  simp only [sourceSequentialOneSubShift, Preadditive.comp_sub, Category.comp_id,
    sourceSequentialShiftMap, Sigma.ι_desc]

/-- An additive abelian-group functor preserving this actual coproduct
sends its Milnor difference to a monomorphism. -/
theorem sourceSequentialOneSubShift_map_mono (F : ℕ ⥤ SourceCategory.{u})
    (G : SourceCategory.{u} ⥤ AddCommGrpCat.{v}) [G.Additive]
    [PreservesColimit (Discrete.functor F.obj) G] :
    Mono (G.map (sourceSequentialOneSubShift F)) := by
  let c : Cofan (F ⋙ G).obj := Cofan.mk (G.obj (∐ F.obj))
    (fun n => G.map (Sigma.ι F.obj n))
  have hc : IsColimit c := isColimitOfHasCoproductOfPreservesColimit G F.obj
  apply Foundation.sequenceDifference_mono_of_isColimit (F ⋙ G) c hc
  intro n
  change G.map (Sigma.ι F.obj n) ≫ G.map (sourceSequentialOneSubShift F) = _
  rw [← G.map_comp, sourceSequentialOneSubShift_inclusion, G.map_sub, G.map_comp]
  rfl

end KIP126.StableHomotopy.Implementation
