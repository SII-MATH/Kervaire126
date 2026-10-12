module

public import KIP126.Def.CategoryTheory.Localization.Pi.Fractions.Data

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory MorphismProperty

universe w u v u' v'
variable {J : Type w} {C : J → Type u} [∀ j, Category.{v} (C j)]
  (W : ∀ j, MorphismProperty (C j))

set_option backward.isDefEq.respectTransparency false

/-- Right calculus of fractions is preserved by arbitrary products of
categories; no finiteness of the indexing family is needed. -/
instance pi_hasRightCalculusOfFractions [∀ j, (W j).HasRightCalculusOfFractions] :
    (MorphismProperty.pi W).HasRightCalculusOfFractions where
  id_mem X j := (W j).id_mem (X j)
  comp_mem f g hf hg j := (W j).comp_mem (f j) (g j) (hf j) (hg j)
  exists_rightFraction X Y φ := by
    let φj j : (W j).LeftFraction _ _ := ⟨φ.f j, φ.s j, φ.hs j⟩
    choose ψ hψ using fun j => HasRightCalculusOfFractions.exists_rightFraction (φj j)
    exact ⟨piRightFraction W ψ, funext hψ⟩
  ext X Y Y' f₁ f₂ s hs h := by
    choose X t ht he using fun j => HasRightCalculusOfFractions.ext
      (f₁ j) (f₂ j) (s j) (hs j) (congrFun h j)
    exact ⟨X, t, ht, funext he⟩

/-- The exact common-refinement relation on right fractions is determined
coordinatewise, even for an infinite family. -/
theorem pi_rightFractionRel_iff {X Y : ∀ j, C j}
    (φ ψ : (MorphismProperty.pi W).RightFraction X Y) :
    RightFractionRel φ ψ ↔ ∀ j,
      RightFractionRel (rightFractionComponent W φ j) (rightFractionComponent W ψ j) := by
  constructor
  · rintro ⟨Z,a,b,hs,hf,hw⟩ j
    exact ⟨Z j,a j,b j,congrFun hs j,congrFun hf j,hw j⟩
  · intro h
    choose Z a b hs hf hw using h
    exact ⟨Z,a,b,funext hs,funext hf,hw⟩

/-- Evaluating a right fraction under a product functor evaluates each
of its coordinate fractions in that coordinate localization. -/
theorem rightFractionComponent_map {D : J → Type u'} [∀ j, Category.{v'} (D j)]
    (L : ∀ j, C j ⥤ D j) (hL : ∀ j, (W j).IsInvertedBy (L j))
    {X Y : ∀ j, C j} (φ : (MorphismProperty.pi W).RightFraction X Y) (j : J) :
    (φ.map (Functor.pi L) (MorphismProperty.IsInvertedBy.pi W L hL)) j =
      (rightFractionComponent W φ j).map (L j) (hL j) := by
  letI := hL j (φ.s j) (φ.hs j)
  apply (cancel_epi ((L j).map (φ.s j))).mp
  exact (congrFun (φ.map_s_comp_map (Functor.pi L)
    (MorphismProperty.IsInvertedBy.pi W L hL)) j).trans
      ((rightFractionComponent W φ j).map_s_comp_map (L j) (hL j)).symm

end KIP126.Foundation
