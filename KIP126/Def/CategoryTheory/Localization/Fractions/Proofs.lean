module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory

universe v u v' u'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (W : MorphismProperty C) (F : C ⥤ D) (hF : W.IsInvertedBy F)

set_option backward.isDefEq.respectTransparency false

/-- The actual localization lift carries a right fraction to that same
fraction evaluated by the original functor. -/
theorem localizationLift_map_rightFraction {X Y : C} (φ : W.RightFraction X Y) :
    (Localization.Construction.lift F hF).map (φ.map W.Q W.Q_inverts) =
      φ.map F hF := by
  let G := Localization.Construction.lift F hF
  have hG {A B : C} (f : A ⟶ B) : G.map (W.Q.map f) = F.map f := by
    simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
      Functor.congr_hom (Localization.Construction.fac F hF) f
  letI := hF φ.s φ.hs
  apply (cancel_epi (F.map φ.s)).mp
  rw [← hG φ.s, ← G.map_comp, φ.map_s_comp_map, hG, hG]
  exact (φ.map_s_comp_map F hF).symm

/-- Right-fraction normal forms and their exact equality criterion identify
an essentially surjective functor as the actual localization. -/
theorem isLocalization_of_rightFractions [W.HasRightCalculusOfFractions] [F.EssSurj]
    (hfull : ∀ {X Y : C} (f : F.obj X ⟶ F.obj Y),
      ∃ φ : W.RightFraction X Y, f = φ.map F hF)
    (hfaith : ∀ {X Y : C} (φ ψ : W.RightFraction X Y),
      φ.map F hF = ψ.map F hF → MorphismProperty.RightFractionRel φ ψ) :
    F.IsLocalization W := by
  let G := Localization.Construction.lift F hF
  have hmap {X Y : C} (φ : W.RightFraction X Y) :
      G.map (φ.map W.Q W.Q_inverts) = φ.map F hF :=
    localizationLift_map_rightFraction W F hF φ
  letI : G.Full :=
    { map_surjective := by
        rintro ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ f
        obtain ⟨φ,hφ⟩ := hfull (X := X) (Y := Y) f
        exact ⟨φ.map W.Q W.Q_inverts, (hmap φ).trans hφ.symm⟩ }
  letI : G.Faithful :=
    { map_injective := by
        rintro ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ f g h
        obtain ⟨φ,rfl⟩ := Localization.exists_rightFraction W.Q W f
        obtain ⟨ψ,rfl⟩ := Localization.exists_rightFraction W.Q W g
        rw [hmap, hmap] at h
        exact (MorphismProperty.RightFraction.map_eq_iff W.Q W φ ψ).mpr (hfaith φ ψ h) }
  letI : G.EssSurj :=
    { mem_essImage := fun Y =>
        ⟨W.Q.obj (F.objPreimage Y), ⟨F.objObjPreimageIso Y⟩⟩ }
  exact { inverts := hF, isEquivalence := { } }

end KIP126.Foundation
