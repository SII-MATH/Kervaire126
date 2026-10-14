module

public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

@[expose] public section

namespace KIP126.Foundation
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false

/-- A zero object remains a zero object in the explicit localization at any morphism property. The actual unique arrows extend by localization naturality. -/
theorem localization_isZero {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) (O : C) (hO : IsZero O) : IsZero (W.Q.obj O) := by
  let to0 : W.Q ⋙ 𝟭 W.Localization ⟶
      W.Q ⋙ (Functor.const W.Localization).obj (W.Q.obj O) := {
    app X := W.Q.map (hO.from_ X)
    naturality := by
      intro X Y f
      change W.Q.map f ≫ W.Q.map (hO.from_ Y) = W.Q.map (hO.from_ X) ≫ 𝟙 _
      rw [Category.comp_id,← Functor.map_comp]
      exact congrArg W.Q.map (hO.eq_of_tgt _ _) }
  let from0 : W.Q ⋙ (Functor.const W.Localization).obj (W.Q.obj O) ⟶
      W.Q ⋙ 𝟭 W.Localization := {
    app X := W.Q.map (hO.to_ X)
    naturality := by
      intro X Y f
      change 𝟙 _ ≫ W.Q.map (hO.to_ Y) = W.Q.map (hO.to_ X) ≫ W.Q.map f
      rw [Category.id_comp,← Functor.map_comp]
      exact congrArg W.Q.map (hO.eq_of_src _ _) }
  let T := Localization.Construction.natTransExtension to0
  let F := Localization.Construction.natTransExtension from0
  have ht : T.app (W.Q.obj O) = 𝟙 (W.Q.obj O) := by
    change Localization.Construction.NatTransExtension.app to0 (W.Q.obj O) = _
    rw [Localization.Construction.NatTransExtension.app_eq]
    change W.Q.map (hO.from_ O) = _
    rw [hO.eq_of_tgt (hO.from_ O) (𝟙 O)]
    exact W.Q.map_id O
  have hf : F.app (W.Q.obj O) = 𝟙 (W.Q.obj O) := by
    change Localization.Construction.NatTransExtension.app from0 (W.Q.obj O) = _
    rw [Localization.Construction.NatTransExtension.app_eq]
    change W.Q.map (hO.to_ O) = _
    rw [hO.eq_of_src (hO.to_ O) (𝟙 O)]
    exact W.Q.map_id O
  constructor
  · intro Y
    refine ⟨{default := F.app Y,uniq := ?_}⟩
    intro f
    have hh := F.naturality f
    change 𝟙 (W.Q.obj O) ≫ F.app Y = F.app (W.Q.obj O) ≫ f at hh
    rw [hf] at hh
    exact (Category.id_comp f).symm.trans (hh.symm.trans (Category.id_comp (F.app Y)))
  · intro Y
    refine ⟨{default := T.app Y,uniq := ?_}⟩
    intro f
    have hh := T.naturality f
    change f ≫ T.app (W.Q.obj O) = T.app Y ≫ 𝟙 (W.Q.obj O) at hh
    rw [ht] at hh
    exact (Category.comp_id f).symm.trans (hh.trans (Category.comp_id (T.app Y)))
end KIP126.Foundation

