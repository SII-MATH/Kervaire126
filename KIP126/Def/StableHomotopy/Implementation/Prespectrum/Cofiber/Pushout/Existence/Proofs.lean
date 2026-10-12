module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Map.Proofs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u

/-- The actual quotient cofiber is unchanged by an actual strict pushout.
This identifies the quotient of a cell attachment before any stable-excision claim. -/
theorem cofiberPushoutIso_exists {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) :
    ∃ e : pointSetCofiber f ≅ pointSetCofiber j,
      cofiberProjection f ≫ e.hom = i ≫ cofiberProjection j := by
  have zcomp {U V W : Prespectrum.{u}} (a : V ⟶ W) : zeroMap U V ≫ a = zeroMap U W := by
    apply Hom.ext
    funext n
    exact ContinuousMap.ext (fun _ => a.point n)
  have compz {U V W : Prespectrum.{u}} (a : U ⟶ V) : a ≫ zeroMap V W = zeroMap U W := rfl
  let F := cofiberMap g i h.w
  let U := h.desc (cofiberProjection f) (zeroMap C (pointSetCofiber f))
    (by rw [cofiberProjection_comp,compz])
  have hU : j ≫ U = zeroMap C (pointSetCofiber f) := h.inr_desc _ _ _
  let R := cofiberDesc j U hU
  have hFR : F ≫ R = 𝟙 _ := by
    apply cofiberHom_ext f
    change cofiberProjection f ≫ cofiberMap g i h.w ≫ cofiberDesc j U hU = _
    rw [cofiberProjection_map_assoc,cofiberProjection_desc]
    rw [Category.comp_id]
    exact h.inl_desc _ _ _
  have hRF : R ≫ F = 𝟙 _ := by
    apply cofiberHom_ext j
    change cofiberProjection j ≫ cofiberDesc j U hU ≫ F = _
    rw [cofiberProjection_desc_assoc,Category.comp_id]
    apply h.hom_ext
    · rw [← Category.assoc,show i ≫ U = cofiberProjection f from h.inl_desc _ _ _]
      exact cofiberProjection_map g i h.w
    · rw [← Category.assoc,hU,zcomp,cofiberProjection_comp]
  exact ⟨⟨F,R,hFR,hRF⟩,cofiberProjection_map g i h.w⟩
end KIP126.StableHomotopy.Implementation.Prespectrum
